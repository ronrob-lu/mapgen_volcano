-- mapgen_volcano/init.lua
-- Endless procedural volcanic world mapgen with occasional explosive eruptions.
-- Uses ONLY Minetest Game `default` blocks (no custom nodes, items, textures, or sounds).
-- Copyright (c) 2026 ronrob-lu (MIT License)

local api = rawget(_G, "core") or minetest
local modname = api.get_current_modname() or "mapgen_volcano"
local settings = api.settings

local math_abs = math.abs
local math_cos = math.cos
local math_floor = math.floor
local math_max = math.max
local math_min = math.min
local math_pi = math.pi
local math_random = math.random
local math_sin = math.sin
local math_sqrt = math.sqrt
local atan2 = math.atan2 or math.atan

-- Exported public API table
mapgen_volcano = {}

--------------------------------------------------------------------------------
-- 1. Configuration (all configurable via minetest.conf / Luanti settings)
--------------------------------------------------------------------------------

local function get_bool_setting(key, default_val)
	if not settings then
		return default_val
	end
	local v = settings:get_bool(key)
	if v == nil then
		return default_val
	end
	return v
end

local function get_num_setting(key, default_val, min_val, max_val)
	local v = settings and tonumber(settings:get(key))
	if not v then
		return default_val
	end
	if min_val and v < min_val then
		v = min_val
	end
	if max_val and v > max_val then
		v = max_val
	end
	return v
end

local FORCE_SINGLENODE        = get_bool_setting("mapgen_volcano.force_singlenode", true)
local ERUPTIONS_ENABLED       = get_bool_setting("mapgen_volcano.eruptions_enabled", true)
local AMBIENT_SMOKE_ENABLED   = get_bool_setting("mapgen_volcano.ambient_smoke", true)
local ERUPTION_DAMAGE_ENABLED = get_bool_setting("mapgen_volcano.damage_enabled", true)
local ERUPTION_CHECK_INTERVAL = get_num_setting("mapgen_volcano.eruption_check_interval", 6.0, 1.0, 120.0)
local ERUPTION_CHANCE         = get_num_setting("mapgen_volcano.eruption_chance", 0.07, 0.001, 1.0)
local ERUPTION_COOLDOWN       = get_num_setting("mapgen_volcano.eruption_cooldown", 150.0, 15.0, 3600.0)
local ACTIVE_RADIUS           = get_num_setting("mapgen_volcano.active_radius", 180.0, 40.0, 400.0)
local MAX_CONCURRENT          = math_floor(get_num_setting("mapgen_volcano.max_concurrent", 2, 1, 8))
local BASE_BLAST_RADIUS       = math_floor(get_num_setting("mapgen_volcano.blast_radius", 5, 2, 9))

local CELL_SIZE               = 160
local CELL_MARGIN             = 36
local MAX_INFLUENCE           = 104
local LAVA_SEA_LEVEL          = 0
local MAGMA_FLOOR             = -64
local SKY_SKIP_Y              = 132
local MAX_ACTIVE_EJECTA       = 36
local VOLCANO_CACHE_LIMIT     = 2048

-- Configure the world to use singlenode so our Lua volcanic terrain covers everything
if FORCE_SINGLENODE and api.set_mapgen_setting then
	api.set_mapgen_setting("mg_name", "singlenode", true)
end

--------------------------------------------------------------------------------
-- 2. Deterministic Hashing & PRNG (strictly Lua 5.1 / LuaJIT 53-bit safe)
--------------------------------------------------------------------------------

local HASH_MOD = 2147483647 -- 2^31 - 1 (Mersenne prime)

local function hash_int(a, b, c)
	local h = a % HASH_MOD
	if h < 0 then h = h + HASH_MOD end
	local b_mod = b % HASH_MOD
	if b_mod < 0 then b_mod = b_mod + HASH_MOD end
	local c_mod = c % HASH_MOD
	if c_mod < 0 then c_mod = c_mod + HASH_MOD end

	-- 2147483647 * 48271 ~= 1.036e14 < 2^53 (9.007e15), exact in IEEE-754 double
	h = (h * 48271 + b_mod + 12345) % HASH_MOD
	h = (h * 48271 + c_mod + 67891) % HASH_MOD
	h = (h * 48271 + 98765) % HASH_MOD
	if h <= 0 then h = h + HASH_MOD end
	return h
end

local function make_rng(seed)
	local state = seed % HASH_MOD
	if state <= 0 then state = state + HASH_MOD - 1 end
	if state <= 0 then state = 1 end

	local rng = {}
	function rng.next_float()
		state = (state * 48271) % HASH_MOD
		return (state - 1) / (HASH_MOD - 1)
	end
	function rng.range(lo, hi)
		return lo + rng.next_float() * (hi - lo)
	end
	function rng.int(lo, hi)
		return lo + math_floor(rng.next_float() * (hi - lo + 1))
	end
	return rng
end

local function coord_hash(x, y, z, seed)
	local h = (x * 374761 + y * 668265 + z * 214748 + seed) % HASH_MOD
	if h < 0 then h = h + HASH_MOD end
	h = (h * 48271 + 12345) % HASH_MOD
	h = (h * 48271 + 67891) % HASH_MOD
	return h
end

--------------------------------------------------------------------------------
-- 3. Noise Definitions & Lazy Engine Initialization (Luanti 5.10+ & Minetest 5.x)
--------------------------------------------------------------------------------

local function noise_get_2d(nobj, pos)
	if not nobj then
		return 0
	end
	if nobj.get_2d then
		return nobj:get_2d(pos)
	end
	return nobj:get2d(pos)
end

local function noisemap_get_2d_flat(nobj, pos, buf)
	if nobj.get_2d_map_flat then
		return nobj:get_2d_map_flat(pos, buf)
	end
	return nobj:get2dMap_flat(pos, buf)
end

local function noisemap_get_3d_flat(nobj, pos, buf)
	if nobj.get_3d_map_flat then
		return nobj:get_3d_map_flat(pos, buf)
	end
	return nobj:get3dMap_flat(pos, buf)
end

local np_base = {
	offset = 9,
	scale = 13,
	spread = {x = 128, y = 128, z = 128},
	seed = 4109,
	octaves = 4,
	persist = 0.55,
	lacunarity = 2.0,
	flags = "defaults",
}

local np_detail = {
	offset = 0,
	scale = 1,
	spread = {x = 24, y = 24, z = 24},
	seed = 8821,
	octaves = 3,
	persist = 0.55,
	lacunarity = 2.0,
	flags = "defaults",
}

local np_fissure = {
	offset = 0,
	scale = 1,
	spread = {x = 76, y = 76, z = 76},
	seed = 17331,
	octaves = 3,
	persist = 0.52,
	lacunarity = 2.0,
	flags = "defaults",
}

local np_material = {
	offset = 0,
	scale = 1,
	spread = {x = 58, y = 58, z = 58},
	seed = 29413,
	octaves = 3,
	persist = 0.55,
	lacunarity = 2.0,
	flags = "defaults",
}

local np_cave = {
	offset = 0,
	scale = 1,
	spread = {x = 30, y = 18, z = 30},
	seed = 51907,
	octaves = 3,
	persist = 0.5,
	lacunarity = 2.0,
	flags = "defaults",
}

local world_seed_hash = nil
local using_direct_noise_ctor = false
local volcano_cache = {}
local volcano_cache_count = 0
local cached_spawn_pos = nil
local npt_base = nil
local npt_detail = nil
local npt_fissure = nil
local npt_material = nil

-- Chunk-scoped reusable noise maps & buffers
local map_sx, map_sy, map_sz = 0, 0, 0
local nobj_base, nobj_detail, nobj_fissure, nobj_material, nobj_cave
local buf_base = {}
local buf_detail = {}
local buf_fissure = {}
local buf_material = {}
local buf_cave = {}
local vm_data_buf = {}

local function parse_world_seed()
	local seed_str = tostring((api.get_mapgen_setting and api.get_mapgen_setting("seed")) or "0")
	local h = 1337
	for i = 1, #seed_str do
		h = (h * 131 + string.byte(seed_str, i)) % HASH_MOD
	end
	if h <= 0 then h = 1 end
	return h
end

local function make_seeded_np(np)
	return {
		offset = np.offset,
		scale = np.scale,
		spread = {x = np.spread.x, y = np.spread.y, z = np.spread.z},
		seed = (np.seed + (world_seed_hash or 0)) % HASH_MOD,
		octaves = np.octaves,
		persist = np.persist,
		lacunarity = np.lacunarity,
		flags = np.flags,
	}
end

local function try_call(fn, ...)
	if not fn then
		return nil
	end
	local ok, res = pcall(fn, ...)
	if ok and res ~= nil then
		return res
	end
	return nil
end

local function create_noise_point(np, force_direct)
	if not force_direct then
		local nobj = try_call(api.get_value_noise, np)
			or try_call(api.get_perlin, np)
		if nobj then
			return nobj, false
		end
	end
	local seeded = make_seeded_np(np)
	local ctor_v = rawget(_G, "ValueNoise")
	local ctor_p = rawget(_G, "PerlinNoise")
	local nobj = try_call(ctor_v, seeded) or try_call(ctor_p, seeded)
	return nobj, true
end

local function create_noise_map_2d(np, sx, sz, sy)
	local sizes = {
		{x = sx, y = sz, z = 1},
		{x = sx, y = sz},
		{x = sx, y = sz, z = math_max(2, sy or 2)},
	}

	if not using_direct_noise_ctor then
		local env_fns = {}
		if api.get_value_noise_map then env_fns[#env_fns + 1] = api.get_value_noise_map end
		if api.get_perlin_map then env_fns[#env_fns + 1] = api.get_perlin_map end

		for fi = 1, #env_fns do
			local fn = env_fns[fi]
			for si = 1, #sizes do
				local nobj = try_call(fn, np, sizes[si])
				if nobj then
					return nobj, false
				end
			end
		end
	end

	local seeded = make_seeded_np(np)
	local ctors = {}
	local ctor_v = rawget(_G, "ValueNoiseMap")
	local ctor_p = rawget(_G, "PerlinNoiseMap")
	if ctor_v then ctors[#ctors + 1] = ctor_v end
	if ctor_p then ctors[#ctors + 1] = ctor_p end

	for ci = 1, #ctors do
		local fn = ctors[ci]
		for si = 1, #sizes do
			local nobj = try_call(fn, seeded, sizes[si])
			if nobj then
				return nobj, true
			end
		end
	end
	return nil, false
end

local function create_noise_map_3d(np, sx, sy, sz)
	local size3d = {x = sx, y = sy, z = math_max(2, sz)}
	if not using_direct_noise_ctor then
		local nobj = try_call(api.get_value_noise_map, np, size3d)
			or try_call(api.get_perlin_map, np, size3d)
		if nobj then
			return nobj, false
		end
	end
	local seeded = make_seeded_np(np)
	local nobj = try_call(rawget(_G, "ValueNoiseMap"), seeded, size3d)
		or try_call(rawget(_G, "PerlinNoiseMap"), seeded, size3d)
	return nobj, (nobj ~= nil)
end

local function rebuild_point_noises(force_direct)
	local b, d1 = create_noise_point(np_base, force_direct)
	local d = create_noise_point(np_detail, force_direct or d1)
	local f = create_noise_point(np_fissure, force_direct or d1)
	local m = create_noise_point(np_material, force_direct or d1)
	npt_base = b
	npt_detail = d
	npt_fissure = f
	npt_material = m
	if d1 then
		using_direct_noise_ctor = true
	end
end

local function ensure_world_init()
	if not world_seed_hash then
		world_seed_hash = parse_world_seed()
	end
	if not npt_base then
		rebuild_point_noises(using_direct_noise_ctor)
	end
end

local function ensure_chunk_noisemaps(sx, sy, sz)
	ensure_world_init()
	if (not nobj_base) or (not nobj_detail) or (not nobj_fissure)
		or (not nobj_material) or (not nobj_cave)
		or sx ~= map_sx or sy ~= map_sy or sz ~= map_sz then
		local b, fb = create_noise_map_2d(np_base, sx, sz, sy)
		if fb and not using_direct_noise_ctor then
			-- Keep single-point noise generators seed-consistent with direct fallback
			using_direct_noise_ctor = true
			rebuild_point_noises(true)
			volcano_cache = {}
			volcano_cache_count = 0
			cached_spawn_pos = nil
		end
		local d = create_noise_map_2d(np_detail, sx, sz, sy)
		local f = create_noise_map_2d(np_fissure, sx, sz, sy)
		local m = create_noise_map_2d(np_material, sx, sz, sy)
		local c = create_noise_map_3d(np_cave, sx, sy, sz)
		if b and d and f and m and c then
			nobj_base = b
			nobj_detail = d
			nobj_fissure = f
			nobj_material = m
			nobj_cave = c
			map_sx, map_sy, map_sz = sx, sy, sz
			return true
		end
		api.log("error", string.format(
			"[%s] Failed to initialize noise maps (sx=%s, sy=%s, sz=%s)",
			modname, tostring(sx), tostring(sy), tostring(sz)
		))
		return false
	end
	return true
end

--------------------------------------------------------------------------------
-- 4. Content ID Cache (strictly Minetest `default` nodes + optional `fire`)
--------------------------------------------------------------------------------

local cids_ready = false
local c_air, c_ignore
local c_stone, c_cobble, c_obsidian, c_coalblock, c_gravel
local c_desert_stone, c_desert_cobble, c_desert_sand, c_silver_sand
local c_lava, c_lava_flowing, c_dry_shrub
local c_ore_coal, c_ore_iron, c_ore_copper, c_ore_tin
local c_ore_gold, c_ore_mese, c_ore_diamond
local has_fire_mod = false
local has_tnt_mod = false

local function resolve_cid(name, fallback_cid)
	if api.registered_nodes and api.registered_nodes[name] then
		return api.get_content_id(name)
	end
	return fallback_cid
end

local function ensure_content_ids()
	if cids_ready then
		return
	end
	c_air           = api.get_content_id("air")
	c_ignore        = api.get_content_id("ignore")
	c_stone         = api.get_content_id("default:stone")
	c_cobble        = resolve_cid("default:cobble", c_stone)
	c_obsidian      = resolve_cid("default:obsidian", c_stone)
	c_coalblock     = resolve_cid("default:coalblock", c_obsidian)
	c_gravel        = resolve_cid("default:gravel", c_cobble)
	c_desert_stone  = resolve_cid("default:desert_stone", c_stone)
	c_desert_cobble = resolve_cid("default:desert_cobble", c_cobble)
	c_desert_sand   = resolve_cid("default:desert_sand", c_gravel)
	c_silver_sand   = resolve_cid("default:silver_sand", c_gravel)
	c_lava          = api.get_content_id("default:lava_source")
	c_lava_flowing  = resolve_cid("default:lava_flowing", c_lava)
	c_dry_shrub     = resolve_cid("default:dry_shrub", c_air)

	c_ore_coal      = resolve_cid("default:stone_with_coal", c_stone)
	c_ore_iron      = resolve_cid("default:stone_with_iron", c_stone)
	c_ore_copper    = resolve_cid("default:stone_with_copper", c_ore_iron)
	c_ore_tin       = resolve_cid("default:stone_with_tin", c_ore_iron)
	c_ore_gold      = resolve_cid("default:stone_with_gold", c_ore_iron)
	c_ore_mese      = resolve_cid("default:stone_with_mese", c_ore_gold)
	c_ore_diamond   = resolve_cid("default:stone_with_diamond", c_ore_mese)

	has_fire_mod = (api.get_modpath("fire") ~= nil)
		and (api.registered_nodes ~= nil)
		and (api.registered_nodes["fire:basic_flame"] ~= nil)
	has_tnt_mod = (api.get_modpath("tnt") ~= nil)

	cids_ready = true
end

--------------------------------------------------------------------------------
-- 5. Deterministic Volcano Grid (infinite world, zero cross-chunk seams)
--------------------------------------------------------------------------------

local function cell_key(cx, cz)
	return cx .. ":" .. cz
end

local function get_volcano_in_cell(cx, cz)
	ensure_world_init()

	local key = cell_key(cx, cz)
	local cached = volcano_cache[key]
	if cached ~= nil then
		return cached or nil
	end

	if volcano_cache_count >= VOLCANO_CACHE_LIMIT then
		volcano_cache = {}
		volcano_cache_count = 0
	end

	local rng = make_rng(hash_int(cx, cz, world_seed_hash))

	-- ~86% of cells contain a volcano; ~14% remain broad basalt/fissure plains
	if rng.next_float() > 0.86 then
		volcano_cache[key] = false
		volcano_cache_count = volcano_cache_count + 1
		return nil
	end

	local vx = cx * CELL_SIZE + rng.int(CELL_MARGIN, CELL_SIZE - CELL_MARGIN)
	local vz = cz * CELL_SIZE + rng.int(CELL_MARGIN, CELL_SIZE - CELL_MARGIN)

	local roll = rng.next_float()
	local kind, outer_r, peak_h, crater_r, crater_depth, lava_depth, conduit_r, breach_prob
	if roll < 0.55 then
		-- Tall classic stratovolcano
		kind = "stratovolcano"
		outer_r = rng.range(52, 76)
		peak_h = rng.range(44, 82)
		crater_r = rng.range(8, 14)
		crater_depth = rng.range(12, 22)
		lava_depth = rng.range(4, 8)
		conduit_r = rng.range(3.0, 4.8)
		breach_prob = 0.60
	elseif roll < 0.80 then
		-- Broad volcanic caldera with huge glowing lava lake
		kind = "caldera"
		outer_r = rng.range(60, 82)
		peak_h = rng.range(28, 48)
		crater_r = rng.range(15, 24)
		crater_depth = rng.range(14, 24)
		lava_depth = rng.range(5, 9)
		conduit_r = rng.range(4.5, 7.2)
		breach_prob = 0.35
	else
		-- Steep dark cinder cone
		kind = "cinder_cone"
		outer_r = rng.range(28, 44)
		peak_h = rng.range(26, 46)
		crater_r = rng.range(5, 8)
		crater_depth = rng.range(8, 14)
		lava_depth = rng.range(3, 6)
		conduit_r = rng.range(2.2, 3.4)
		breach_prob = 0.40
	end

	local has_breach = rng.next_float() < breach_prob
	local breach_angle = rng.range(-math_pi, math_pi)
	local breach_length = rng.range(0.58, 0.92)
	local breach_phase = rng.range(0, math_pi * 2)

	-- Base elevation at the volcano center determines flat horizontal caldera lava height
	local base_y = noise_get_2d(npt_base, {x = vx, y = vz})
	local rim_y = math_floor(base_y + peak_h)
	local lava_y = math_max(LAVA_SEA_LEVEL + 8, rim_y - math_floor(lava_depth))

	local reach = outer_r * 1.18 + 6
	local v = {
		key = key,
		cx = cx,
		cz = cz,
		x = vx,
		z = vz,
		kind = kind,
		outer_r = outer_r,
		peak_h = peak_h,
		crater_r = crater_r,
		crater_depth = crater_depth,
		lava_depth = lava_depth,
		conduit_r = conduit_r,
		base_y = base_y,
		rim_y = rim_y,
		lava_y = lava_y,
		reach = reach,
		has_breach = has_breach,
		breach_angle = breach_angle,
		bx = math_cos(breach_angle),
		bz = math_sin(breach_angle),
		breach_length = breach_length,
		breach_phase = breach_phase,
	}

	volcano_cache[key] = v
	volcano_cache_count = volcano_cache_count + 1
	return v
end

local function collect_volcanoes_for_area(minx, maxx, minz, maxz)
	local min_cx = math_floor((minx - MAX_INFLUENCE) / CELL_SIZE)
	local max_cx = math_floor((maxx + MAX_INFLUENCE) / CELL_SIZE)
	local min_cz = math_floor((minz - MAX_INFLUENCE) / CELL_SIZE)
	local max_cz = math_floor((maxz + MAX_INFLUENCE) / CELL_SIZE)

	local list = {}
	for cz = min_cz, max_cz do
		for cx = min_cx, max_cx do
			local v = get_volcano_in_cell(cx, cz)
			if v then
				if (v.x + v.reach >= minx) and (v.x - v.reach <= maxx)
					and (v.z + v.reach >= minz) and (v.z - v.reach <= maxz) then
					list[#list + 1] = v
				end
			end
		end
	end
	return list
end

--------------------------------------------------------------------------------
-- 6. Shared Volcanic Column Evaluator (Mapgen + Safe Spawn)
--------------------------------------------------------------------------------

local function evaluate_column(x, z, n_base, n_detail, n_fissure, candidates)
	local base_h = n_base + n_detail * 2.2
	local best_cone_h = 0
	local best_profile = 0
	local dom_v = nil
	local dom_d = 0
	local dom_raw_dist = 0
	local in_crater = false
	local in_conduit = false
	local near_conduit = false
	local conduit_top_y = nil
	local caldera_lava_y = nil
	local in_breach_lava = false
	local breach_carve = 0

	for i = 1, #candidates do
		local v = candidates[i]
		local dx = x - v.x
		local dz = z - v.z
		local raw_dist_sq = dx * dx + dz * dz
		if raw_dist_sq <= v.reach * v.reach then
			local raw_dist = math_sqrt(raw_dist_sq)
			-- Scale domain warp near center so the crater throat stays clean
			local warp_scale = math_min(1.0, raw_dist / math_max(v.crater_r, 6.0))
			local warp = n_detail * (v.outer_r * 0.085) * warp_scale
			local d = raw_dist + warp
			if d < 0 then d = 0 end

			if d < v.outer_r then
				local h_add
				local prof
				local local_crater = false
				if d < v.crater_r then
					local ct = d / v.crater_r
					local bowl = ct * ct
					h_add = v.peak_h + n_detail * 2.4 - v.crater_depth * (1.0 - bowl)
					prof = 1.0
					local_crater = true
				else
					local t = (d - v.crater_r) / (v.outer_r - v.crater_r)
					local u = 1.0 - t
					if v.kind == "caldera" then
						prof = u * u * (2.2 - 1.2 * u)
					else
						prof = u * u * (1.8 - 0.8 * u)
					end
					h_add = v.peak_h * prof + n_detail * 2.4 * prof
				end

				-- Check if this volcano dominates here (crater takes priority inside its rim)
				if local_crater or ((not in_crater) and h_add > best_cone_h) then
					best_cone_h = h_add
					best_profile = prof
					dom_v = v
					dom_d = d
					dom_raw_dist = raw_dist
					in_crater = local_crater
					if local_crater then
						caldera_lava_y = v.lava_y
					else
						caldera_lava_y = nil
					end
				end

				-- Check central magma conduit & obsidian jacket
				if raw_dist <= v.conduit_r then
					in_conduit = true
					conduit_top_y = v.lava_y
				elseif raw_dist <= v.conduit_r + 2.2 then
					near_conduit = true
					conduit_top_y = conduit_top_y or v.lava_y
				end
			end
		end
	end

	local height_f = base_h + best_cone_h

	-- Optional meandering lava breach channel cutting from crater rim down one flank
	if dom_v and dom_v.has_breach and (not in_conduit) and dom_d < dom_v.outer_r * dom_v.breach_length then
		local dx = x - dom_v.x
		local dz = z - dom_v.z
		local proj = dx * dom_v.bx + dz * dom_v.bz
		if proj >= dom_v.crater_r * 0.65 then
			local cross = dx * (-dom_v.bz) + dz * dom_v.bx
			local meander = math_sin(proj * 0.13 + dom_v.breach_phase) * 2.4
			local perp = math_abs(cross - meander)
			local half_w = 3.4
			if perp < half_w then
				local edge = 1.0 - (perp / half_w)
				local rim_boost = 0
				if proj < dom_v.crater_r * 1.45 then
					rim_boost = dom_v.lava_depth * 0.65
				end
				breach_carve = (3.4 + rim_boost) * (edge * edge)
				height_f = height_f - breach_carve
				if perp <= 1.25 and height_f <= dom_v.lava_y and height_f > LAVA_SEA_LEVEL + 1 then
					in_breach_lava = true
				end
			end
		end
	end

	local surface_y = math_floor(height_f)
	local lava_top_y = nil
	local in_fissure = false
	local fissure_rim = false

	-- Glowing tectonic lava fissures across the volcanic lowlands
	if best_profile < 0.16 and not in_crater and not in_conduit then
		local abs_f = math_abs(n_fissure)
		if abs_f < 0.052 and surface_y >= LAVA_SEA_LEVEL + 1 and surface_y <= 22 then
			local depth_frac = 1.0 - (abs_f / 0.052)
			local carve = math_floor(3 + depth_frac * 5)
			local orig_y = surface_y
			surface_y = orig_y - carve
			-- Fill bottom of rift with glowing lava (kept sunken beneath rims)
			lava_top_y = math_max(LAVA_SEA_LEVEL, math_min(orig_y - 2, surface_y + 2))
			in_fissure = true
		elseif abs_f < 0.090 and surface_y >= LAVA_SEA_LEVEL + 1 and surface_y <= 22 then
			fissure_rim = true
		end
	end

	-- Caldera lava lake
	if in_crater and caldera_lava_y and surface_y < caldera_lava_y then
		lava_top_y = caldera_lava_y
	end

	-- Flank lava channel inside carved breach gully
	if in_breach_lava and dom_v then
		local stream_y = math_min(dom_v.lava_y, surface_y + 1)
		if not lava_top_y or stream_y > lava_top_y then
			lava_top_y = stream_y
		end
	end

	-- Global volcanic lava sea in lowlands
	if surface_y < LAVA_SEA_LEVEL then
		if not lava_top_y or LAVA_SEA_LEVEL > lava_top_y then
			lava_top_y = LAVA_SEA_LEVEL
		end
	end

	return {
		surface_y = surface_y,
		lava_top_y = lava_top_y,
		in_crater = in_crater,
		in_conduit = in_conduit,
		near_conduit = near_conduit,
		conduit_top_y = conduit_top_y,
		in_fissure = in_fissure,
		fissure_rim = fissure_rim,
		in_breach_lava = in_breach_lava,
		volcano_frac = best_profile,
		dom_v = dom_v,
		dom_raw_dist = dom_raw_dist,
	}
end

--------------------------------------------------------------------------------
-- 7. Volcanic Surface Stratification & Ore Selection (100% `default` blocks)
--------------------------------------------------------------------------------

local function choose_surface_node(col, y, n_detail, n_mat, h_surf)
	-- Shoreline & lava-adjacent crust -> obsidian & dark scoria
	if col.in_breach_lava or col.in_fissure or col.in_crater then
		if (h_surf % 5) == 0 then
			return c_coalblock
		end
		return c_obsidian
	end

	if col.fissure_rim or y <= LAVA_SEA_LEVEL + 1 then
		local r = h_surf % 10
		if r < 6 then
			return c_obsidian
		elseif r < 8 then
			return c_coalblock
		else
			return c_cobble
		end
	end

	-- Upper volcano cone slopes: obsidian, charred coalblock, volcanic gravel/ash, red tuff
	local vf = col.volcano_frac
	if vf > 0.62 then
		local r = h_surf % 12
		if r < 4 then
			return c_obsidian
		elseif r < 7 then
			return c_coalblock
		elseif r < 9 then
			return c_gravel
		elseif r < 11 then
			return c_desert_stone
		else
			return c_cobble
		end
	elseif vf > 0.25 then
		if n_detail > 0.35 then
			return c_obsidian
		elseif n_detail < -0.35 then
			return c_gravel
		elseif n_mat > 0.30 then
			return ((h_surf % 3) == 0) and c_desert_cobble or c_desert_stone
		else
			return ((h_surf % 4) == 0) and c_coalblock or c_cobble
		end
	end

	-- Volcanic plains & badlands outside cones
	if n_mat < -0.35 then
		-- Basalt & obsidian lava fields
		local r = h_surf % 10
		if r < 4 then
			return c_obsidian
		elseif r < 7 then
			return c_stone
		elseif r < 9 then
			return c_coalblock
		else
			return c_cobble
		end
	elseif n_mat < 0.35 then
		-- Volcanic ash & tephra barrens
		local r = h_surf % 10
		if r < 4 then
			return c_gravel
		elseif r < 6 then
			return c_silver_sand
		elseif r < 8 then
			return c_cobble
		else
			return c_stone
		end
	else
		-- Scorched red-brown volcanic tuff badlands
		local r = h_surf % 10
		if r < 4 then
			return c_desert_stone
		elseif r < 7 then
			return c_desert_cobble
		elseif r < 9 then
			return c_desert_sand
		else
			return c_obsidian
		end
	end
end

local function choose_subsurface_node(col, depth, n_mat, h_surf)
	if col.in_crater or col.in_fissure or col.in_breach_lava then
		return (depth <= 2) and c_obsidian or c_stone
	end
	if col.volcano_frac > 0.45 then
		if depth == 1 then
			return ((h_surf % 3) == 0) and c_obsidian or c_cobble
		end
		return ((h_surf % 4) == 0) and c_desert_stone or c_stone
	end
	if n_mat >= 0.35 and depth <= 3 then
		return c_desert_stone
	end
	if depth == 1 and (h_surf % 3) == 0 then
		return c_cobble
	end
	return c_stone
end

local function choose_ore_node(x, y, z, near_magma)
	-- Cluster ores in 2x2x2 cells so veins feel natural rather than single speckles
	local qx = math_floor(x / 2)
	local qy = math_floor(y / 2)
	local qz = math_floor(z / 2)
	local ch = coord_hash(qx, qy, qz, world_seed_hash + 7919)
	local vh = coord_hash(x, y, z, world_seed_hash + 104729)

	-- Only ~45% of voxels inside a mineral cluster carry the ore
	if (vh % 100) >= 45 then
		return c_stone
	end

	local m = ch % 1000
	if y <= -48 then
		local diam_thresh = near_magma and 16 or 8
		if m < diam_thresh then return c_ore_diamond end
	end
	if y <= -34 and m >= 20 and m < 32 then
		return c_ore_mese
	end
	if y <= -20 and m >= 40 and m < 56 then
		return c_ore_gold
	end
	if y <= -8 and m >= 60 and m < 80 then
		return c_ore_tin
	end
	if y <= 8 and m >= 90 and m < 118 then
		return c_ore_copper
	end
	if y <= 24 and m >= 130 and m < 168 then
		return c_ore_iron
	end
	if y <= 52 and m >= 200 and m < 258 then
		return c_ore_coal
	end

	return c_stone
end

--------------------------------------------------------------------------------
-- 8. High-Speed VoxelManip Mapgen Callback
--------------------------------------------------------------------------------

api.register_on_generated(function(minp, maxp, blockseed)
	ensure_content_ids()
	ensure_world_init()

	-- Fast exit for pure sky chunks when using singlenode
	local mg_name = api.get_mapgen_setting and api.get_mapgen_setting("mg_name")
	if minp.y > SKY_SKIP_Y and mg_name == "singlenode" then
		return
	end

	local vm, emin, emax = api.get_mapgen_object("voxelmanip")
	local area = VoxelArea:new({MinEdge = emin, MaxEdge = emax})
	local data = vm:get_data(vm_data_buf)
	local ystride = area.ystride

	local sx = maxp.x - minp.x + 1
	local sy = maxp.y - minp.y + 1
	local sz = maxp.z - minp.z + 1

	-- Pure sky overwrite when mod is enabled on non-singlenode mapgens
	if minp.y > SKY_SKIP_Y then
		for z = minp.z, maxp.z do
			for y = minp.y, maxp.y do
				local vi = area:index(minp.x, y, z)
				for _ = 1, sx do
					data[vi] = c_air
					vi = vi + 1
				end
			end
		end
		vm:set_data(data)
		vm:set_lighting({day = 0, night = 0})
		vm:calc_lighting()
		vm:write_to_map()
		return
	end

	if not ensure_chunk_noisemaps(sx, sy, sz) then
		return
	end

	local minp2d = {x = minp.x, y = minp.z}
	buf_base = noisemap_get_2d_flat(nobj_base, minp2d, buf_base)
	buf_detail = noisemap_get_2d_flat(nobj_detail, minp2d, buf_detail)
	buf_fissure = noisemap_get_2d_flat(nobj_fissure, minp2d, buf_fissure)
	buf_material = noisemap_get_2d_flat(nobj_material, minp2d, buf_material)

	local use_caves = (minp.y <= 32)
	if use_caves then
		buf_cave = noisemap_get_3d_flat(nobj_cave, minp, buf_cave)
	end

	local candidates = collect_volcanoes_for_area(minp.x, maxp.x, minp.z, maxp.z)

	local ni2d = 1
	for z = minp.z, maxp.z do
		local dz_idx = z - minp.z
		for x = minp.x, maxp.x do
			local dx_idx = x - minp.x
			local n_base = buf_base[ni2d]
			local n_detail = buf_detail[ni2d]
			local n_fissure = buf_fissure[ni2d]
			local n_mat = buf_material[ni2d]
			ni2d = ni2d + 1

			local col = evaluate_column(x, z, n_base, n_detail, n_fissure, candidates)
			local surf_y = col.surface_y
			local lava_top = col.lava_top_y
			local in_conduit = col.in_conduit
			local near_conduit = col.near_conduit
			local conduit_top = col.conduit_top_y
			local h_surf = coord_hash(x, 0, z, world_seed_hash + 313)

			local vi = area:index(x, minp.y, z)
			local ni3d = (dz_idx * sy) * sx + dx_idx + 1

			for y = minp.y, maxp.y do
				local cid

				-- 1. Vertical volcano magma conduit (lava chimney)
				if in_conduit and conduit_top and y >= MAGMA_FLOOR and y <= conduit_top then
					cid = c_lava
				elseif near_conduit and conduit_top and y >= MAGMA_FLOOR and y <= conduit_top - 1 and y <= surf_y then
					cid = c_obsidian
				elseif y > surf_y then
					-- 2. Above solid ground: lava lakes/streams, rare scorched shrub, or air
					if lava_top and y <= lava_top then
						cid = c_lava
					elseif y == surf_y + 1
						and not lava_top
						and col.volcano_frac < 0.20
						and not col.in_crater
						and not col.in_fissure
						and not col.fissure_rim
						and surf_y >= LAVA_SEA_LEVEL + 4
						and (h_surf % 211) == 0 then
						cid = c_dry_shrub
					else
						cid = c_air
					end
				elseif y == surf_y then
					-- 3. Surface crust
					cid = choose_surface_node(col, y, n_detail, n_mat, h_surf)
				else
					-- 4. Subsurface & deep volcanic underground
					local depth = surf_y - y
					local is_cave = false
					local is_magma_chamber = false

					if use_caves and depth >= 5 and y <= 28 then
						local nc = buf_cave[ni3d]
						if math_abs(nc) < 0.085 then
							is_cave = true
						elseif y <= -26 and nc > 0.58 then
							is_cave = true
							is_magma_chamber = true
						end
					end

					if is_cave then
						if y <= -38 or (is_magma_chamber and y <= -32) then
							cid = c_lava
						else
							cid = c_air
						end
					elseif depth <= 4 then
						cid = choose_subsurface_node(col, depth, n_mat, h_surf)
					else
						-- Deep obsidian veins near magma chambers or underground ores
						local near_magma = near_conduit or (y <= -36)
						if near_magma and (coord_hash(x, y, z, world_seed_hash + 557) % 14) == 0 then
							cid = c_obsidian
						else
							cid = choose_ore_node(x, y, z, near_magma)
						end
					end
				end

				data[vi] = cid
				vi = vi + ystride
				ni3d = ni3d + sx
			end
		end
	end

	vm:set_data(data)
	vm:set_lighting({day = 0, night = 0})
	vm:calc_lighting()
	vm:write_to_map()
	vm:update_liquids()
end)

--------------------------------------------------------------------------------
-- 9. Safe Player Spawn & Respawn (essential for `singlenode` volcanic worlds)
--------------------------------------------------------------------------------

local function sample_column_at(x, z)
	ensure_world_init()
	local pos2d = {x = x, y = z}
	local n_base = noise_get_2d(npt_base, pos2d)
	local n_detail = noise_get_2d(npt_detail, pos2d)
	local n_fissure = noise_get_2d(npt_fissure, pos2d)
	local candidates = collect_volcanoes_for_area(x - 4, x + 4, z - 4, z + 4)
	return evaluate_column(x, z, n_base, n_detail, n_fissure, candidates)
end

local function is_column_safe_for_spawn(x, z)
	local col = sample_column_at(x, z)
	if col.lava_top_y or col.in_crater or col.in_conduit or col.in_fissure or col.in_breach_lava then
		return false, nil
	end
	if col.surface_y < LAVA_SEA_LEVEL + 4 or col.surface_y > 42 then
		return false, nil
	end
	-- Ensure immediate neighbors are also dry and not sheer cliffs
	local offsets = {{-2, 0}, {2, 0}, {0, -2}, {0, 2}}
	for i = 1, #offsets do
		local nc = sample_column_at(x + offsets[i][1], z + offsets[i][2])
		if nc.lava_top_y or nc.in_crater or nc.in_fissure or nc.in_breach_lava then
			return false, nil
		end
		if math_abs(nc.surface_y - col.surface_y) > 4 then
			return false, nil
		end
	end
	return true, col
end

local function find_safe_spawn()
	if cached_spawn_pos then
		return {x = cached_spawn_pos.x, y = cached_spawn_pos.y, z = cached_spawn_pos.z}
	end

	-- Spiral outward from (0, 0) to find dry solid volcanic ground
	local step = 4
	local max_r = 256
	local ok, col = is_column_safe_for_spawn(0, 0)
	if ok then
		cached_spawn_pos = {x = 0, y = col.surface_y + 1.5, z = 0}
		return {x = cached_spawn_pos.x, y = cached_spawn_pos.y, z = cached_spawn_pos.z}
	end

	for r = step, max_r, step do
		for dx = -r, r, step do
			local tests = {{dx, -r}, {dx, r}}
			for _, t in ipairs(tests) do
				local safe, c = is_column_safe_for_spawn(t[1], t[2])
				if safe then
					cached_spawn_pos = {x = t[1], y = c.surface_y + 1.5, z = t[2]}
					return {x = cached_spawn_pos.x, y = cached_spawn_pos.y, z = cached_spawn_pos.z}
				end
			end
		end
		for dz = -r + step, r - step, step do
			local tests = {{-r, dz}, {r, dz}}
			for _, t in ipairs(tests) do
				local safe, c = is_column_safe_for_spawn(t[1], t[2])
				if safe then
					cached_spawn_pos = {x = t[1], y = c.surface_y + 1.5, z = t[2]}
					return {x = cached_spawn_pos.x, y = cached_spawn_pos.y, z = cached_spawn_pos.z}
				end
			end
		end
	end

	-- Guaranteed fallback
	local fallback_col = sample_column_at(0, 0)
	local fy = math_max(LAVA_SEA_LEVEL + 6, fallback_col.surface_y + 2)
	cached_spawn_pos = {x = 0, y = fy, z = 0}
	return {x = 0, y = fy, z = 0}
end

local function place_player_at_spawn(player)
	local sp = find_safe_spawn()
	-- If the spawn area is already loaded, snap cleanly onto current solid non-lava surface
	local n = api.get_node_or_nil({x = sp.x, y = math_floor(sp.y), z = sp.z})
	if n and n.name ~= "ignore" then
		for y = math_floor(sp.y) + 12, math_floor(sp.y) - 12, -1 do
			local below = api.get_node_or_nil({x = sp.x, y = y, z = sp.z})
			local above1 = api.get_node_or_nil({x = sp.x, y = y + 1, z = sp.z})
			local above2 = api.get_node_or_nil({x = sp.x, y = y + 2, z = sp.z})
			if below and above1 and above2
				and below.name ~= "air"
				and below.name ~= "ignore"
				and below.name ~= "default:lava_source"
				and below.name ~= "default:lava_flowing"
				and above1.name == "air"
				and above2.name == "air" then
				sp.y = y + 1.5
				break
			end
		end
	end
	player:set_pos(sp)
end

api.register_on_newplayer(function(player)
	place_player_at_spawn(player)
end)

api.register_on_respawnplayer(function(player)
	place_player_at_spawn(player)
	return true
end)

--------------------------------------------------------------------------------
-- 10. Helpers for Volcanic Eruptions (Damage, Protection, Particles, Sounds)
--------------------------------------------------------------------------------

local function is_world_damage_enabled()
	if not ERUPTION_DAMAGE_ENABLED then
		return false
	end
	return get_bool_setting("enable_damage", true)
end

local function is_node_protected(pos)
	if api.is_protected then
		return api.is_protected(pos, "")
	end
	return false
end

local function apply_blast_damage(center, radius, max_damage, knockback)
	if not is_world_damage_enabled() then
		return
	end
	if not api.get_objects_inside_radius then
		return
	end

	local objs = api.get_objects_inside_radius(center, radius)
	for i = 1, #objs do
		local obj = objs[i]
		local ent = obj:get_luaentity()
		-- Skip our own volcanic ejecta projectiles
		if not (ent and ent.name == modname .. ":ejecta") then
			local opos = obj:get_pos()
			if opos then
				local dx = opos.x - center.x
				local dy = (opos.y + 0.8) - center.y
				local dz = opos.z - center.z
				local dist = math_sqrt(dx * dx + dy * dy + dz * dz)
				if dist < radius then
					local factor = 1.0 - (dist / radius)
					local dmg = math_floor(max_damage * factor + 0.5)

					local armor = obj.get_armor_groups and obj:get_armor_groups() or nil
					local immortal = armor and armor.immortal and armor.immortal > 0

					if dmg > 0 and not immortal and obj.get_hp and obj.set_hp then
						local hp = obj:get_hp()
						if hp and hp > 0 then
							obj:set_hp(math_max(0, hp - dmg))
						end
					end

					if knockback and knockback > 0 and obj.add_velocity then
						local inv = (dist > 0.01) and (1.0 / dist) or 0
						local push = knockback * factor
						obj:add_velocity({
							x = dx * inv * push,
							y = math_max(2.5, (dy * inv + 0.65) * push),
							z = dz * inv * push,
						})
					end
				end
			end
		end
	end
end

local function play_volcano_sound(name, pos, gain, pitch, max_dist)
	if not api.sound_play then
		return
	end
	api.sound_play(name, {
		pos = pos,
		gain = gain or 1.0,
		pitch = pitch or 1.0,
		max_hear_distance = max_dist or 140,
	}, true)
end

local function spawn_crater_smoke(pos, radius, intensity, fiery)
	if not api.add_particlespawner then
		return
	end
	local spread = math_max(2, radius * 0.6)
	api.add_particlespawner({
		amount = math_floor(16 * intensity),
		time = 1.4,
		minpos = {x = pos.x - spread, y = pos.y + 0.5, z = pos.z - spread},
		maxpos = {x = pos.x + spread, y = pos.y + 2.5, z = pos.z + spread},
		minvel = {x = -1.6 * intensity, y = 4.5 * intensity, z = -1.6 * intensity},
		maxvel = {x = 1.6 * intensity, y = 9.5 * intensity, z = 1.6 * intensity},
		minacc = {x = -0.3, y = 0.6, z = -0.3},
		maxacc = {x = 0.3, y = 1.5, z = 0.3},
		minexptime = 2.5,
		maxexptime = 5.5,
		minsize = 4.0 * intensity,
		maxsize = 9.0 * intensity,
		collisiondetection = false,
		texture = "default_coal_block.png^[opacity:165",
	})

	if fiery then
		api.add_particlespawner({
			amount = math_floor(14 * intensity),
			time = 1.2,
			minpos = {x = pos.x - spread * 0.7, y = pos.y + 0.5, z = pos.z - spread * 0.7},
			maxpos = {x = pos.x + spread * 0.7, y = pos.y + 2.0, z = pos.z + spread * 0.7},
			minvel = {x = -2.5 * intensity, y = 7.0 * intensity, z = -2.5 * intensity},
			maxvel = {x = 2.5 * intensity, y = 14.0 * intensity, z = 2.5 * intensity},
			minacc = {x = 0, y = -9.0, z = 0},
			maxacc = {x = 0, y = -6.0, z = 0},
			minexptime = 1.0,
			maxexptime = 2.6,
			minsize = 1.5,
			maxsize = 3.5,
			collisiondetection = true,
			texture = "default_lava.png",
			glow = 14,
		})
	end
end

local function spawn_explosion_plume(pos, radius, intensity)
	if not api.add_particlespawner then
		return
	end
	local spread = math_max(3, radius * 0.7)

	-- 1. Towering dark ash mushroom column
	api.add_particlespawner({
		amount = math_floor(55 * intensity),
		time = 0.8,
		minpos = {x = pos.x - spread, y = pos.y, z = pos.z - spread},
		maxpos = {x = pos.x + spread, y = pos.y + 3, z = pos.z + spread},
		minvel = {x = -6.0 * intensity, y = 12.0 * intensity, z = -6.0 * intensity},
		maxvel = {x = 6.0 * intensity, y = 26.0 * intensity, z = 6.0 * intensity},
		minacc = {x = -1.2, y = -0.8, z = -1.2},
		maxacc = {x = 1.2, y = 1.0, z = 1.2},
		minexptime = 3.5,
		maxexptime = 7.5,
		minsize = 7.0 * intensity,
		maxsize = 16.0 * intensity,
		collisiondetection = false,
		texture = "default_coal_block.png^[opacity:205",
	})

	-- 2. Gray tephra billow
	api.add_particlespawner({
		amount = math_floor(40 * intensity),
		time = 1.0,
		minpos = {x = pos.x - spread, y = pos.y + 1, z = pos.z - spread},
		maxpos = {x = pos.x + spread, y = pos.y + 4, z = pos.z + spread},
		minvel = {x = -8.0 * intensity, y = 8.0 * intensity, z = -8.0 * intensity},
		maxvel = {x = 8.0 * intensity, y = 18.0 * intensity, z = 8.0 * intensity},
		minacc = {x = -0.5, y = -1.8, z = -0.5},
		maxacc = {x = 0.5, y = -0.5, z = 0.5},
		minexptime = 3.0,
		maxexptime = 6.0,
		minsize = 5.0 * intensity,
		maxsize = 12.0 * intensity,
		collisiondetection = false,
		texture = "default_gravel.png^[colorize:#221a18:165^[opacity:180",
	})

	-- 3. Incandescent lava fountain sparks
	api.add_particlespawner({
		amount = math_floor(65 * intensity),
		time = 0.6,
		minpos = {x = pos.x - spread * 0.6, y = pos.y + 1, z = pos.z - spread * 0.6},
		maxpos = {x = pos.x + spread * 0.6, y = pos.y + 3, z = pos.z + spread * 0.6},
		minvel = {x = -9.0 * intensity, y = 14.0 * intensity, z = -9.0 * intensity},
		maxvel = {x = 9.0 * intensity, y = 30.0 * intensity, z = 9.0 * intensity},
		minacc = {x = 0, y = -13.0, z = 0},
		maxacc = {x = 0, y = -9.0, z = 0},
		minexptime = 1.2,
		maxexptime = 3.2,
		minsize = 2.0,
		maxsize = 5.5,
		collisiondetection = true,
		texture = "default_lava.png",
		glow = 14,
	})
end

local function spawn_ashfall(pos, radius, intensity)
	if not api.add_particlespawner then
		return
	end
	local spread = math_max(12, radius * 2.5)
	api.add_particlespawner({
		amount = math_floor(36 * intensity),
		time = 2.5,
		minpos = {x = pos.x - spread, y = pos.y + 12, z = pos.z - spread},
		maxpos = {x = pos.x + spread, y = pos.y + 28, z = pos.z + spread},
		minvel = {x = -1.5, y = -3.0, z = -1.5},
		maxvel = {x = 1.5, y = -1.0, z = 1.5},
		minacc = {x = -0.2, y = -0.4, z = -0.2},
		maxacc = {x = 0.2, y = -0.1, z = 0.2},
		minexptime = 3.0,
		maxexptime = 6.5,
		minsize = 1.5,
		maxsize = 4.0,
		collisiondetection = true,
		collision_removal = true,
		texture = "default_gravel.png^[colorize:#2a2422:150^[opacity:175",
	})
end

--------------------------------------------------------------------------------
-- 11. Transient Ballistic Volcanic Ejecta Entity (NO new blocks, static_save=false)
--------------------------------------------------------------------------------

-- Purely transient flying volcanic rocks/lava bombs rendered with `default` textures.
-- Because `static_save = false`, nothing custom is ever saved into the world database.
local active_ejecta_count = 0

local EJECTA_STYLES = {
	lava = {
		texture = "default_lava.png",
		glow = 14,
		size = 0.72,
		place_node = "default:lava_source",
		damage = 7,
		crater_r = 1,
		hot = true,
	},
	obsidian = {
		texture = "default_obsidian.png",
		glow = 3,
		size = 0.68,
		place_node = "default:obsidian",
		damage = 6,
		crater_r = 1,
		hot = false,
	},
	cobble = {
		texture = "default_cobble.png",
		glow = 2,
		size = 0.62,
		place_node = "default:cobble",
		damage = 5,
		crater_r = 1,
		hot = false,
	},
	scoria = {
		texture = "default_coal_block.png",
		glow = 4,
		size = 0.64,
		place_node = "default:coalblock",
		damage = 5,
		crater_r = 1,
		hot = true,
	},
}

local function ejecta_impact(pos, style)
	local p = {
		x = math_floor(pos.x + 0.5),
		y = math_floor(pos.y + 0.5),
		z = math_floor(pos.z + 0.5),
	}

	-- Impact sound & particles
	if style.hot then
		play_volcano_sound("default_cool_lava", p, 0.9, 0.7 + math_random() * 0.4, 70)
	else
		play_volcano_sound("default_hard_footstep", p, 1.1, 0.5 + math_random() * 0.3, 60)
	end

	if api.add_particlespawner then
		api.add_particlespawner({
			amount = style.hot and 16 or 10,
			time = 0.15,
			minpos = {x = p.x - 0.5, y = p.y - 0.3, z = p.z - 0.5},
			maxpos = {x = p.x + 0.5, y = p.y + 0.5, z = p.z + 0.5},
			minvel = {x = -4, y = 2, z = -4},
			maxvel = {x = 4, y = 7, z = 4},
			minacc = {x = 0, y = -11, z = 0},
			maxacc = {x = 0, y = -9, z = 0},
			minexptime = 0.5,
			maxexptime = 1.3,
			minsize = 1.5,
			maxsize = 3.5,
			collisiondetection = true,
			texture = style.hot and "default_lava.png" or "default_gravel.png",
			glow = style.hot and 14 or 0,
		})
	end

	-- Area impact damage
	apply_blast_damage(p, style.hot and 3.5 or 2.8, style.damage, 5.0)

	-- Carve minor scorch/impact mark (sparing obsidian & protected areas)
	local r = style.crater_r
	for dz = -r, r do
		for dy = -r, 0 do
			for dx = -r, r do
				if (dx * dx + dy * dy + dz * dz) <= (r * r) then
					local np = {x = p.x + dx, y = p.y + dy, z = p.z + dz}
					if not is_node_protected(np) then
						local node = api.get_node_or_nil(np)
						if node and node.name ~= "air" and node.name ~= "ignore"
							and node.name ~= "default:obsidian"
							and node.name ~= "default:lava_source" then
							if dx == 0 and dy == 0 and dz == 0 then
								-- Center node replaced below
							elseif math_random() < 0.45 then
								api.set_node(np, {name = "air"})
							elseif math_random() < 0.35 then
								api.set_node(np, {name = "default:gravel"})
							end
						end
					end
				end
			end
		end
	end

	-- Deposit pure `default` volcanic material at impact point
	if not is_node_protected(p) then
		local cur = api.get_node_or_nil(p)
		if cur and cur.name ~= "ignore" and cur.name ~= "default:obsidian" then
			local place_name = style.place_node
			if place_name == "default:lava_source"
				and (cur.name == "default:lava_source" or cur.name == "default:lava_flowing") then
				place_name = "default:obsidian"
			end
			api.set_node(p, {name = place_name})

			-- Optional flame ignition on adjacent air if Minetest Game `fire` mod is present
			if has_fire_mod and style.hot and math_random() < 0.45 then
				local above = {x = p.x, y = p.y + 1, z = p.z}
				if not is_node_protected(above) then
					local an = api.get_node_or_nil(above)
					if an and an.name == "air" then
						api.set_node(above, {name = "fire:basic_flame"})
					end
				end
			end
		end
	end
end

local function remove_ejecta(self)
	if self.counted then
		self.counted = false
		active_ejecta_count = math_max(0, active_ejecta_count - 1)
	end
	self.object:remove()
end

api.register_entity(modname .. ":ejecta", {
	initial_properties = {
		visual = "cube",
		textures = {
			"default_lava.png", "default_lava.png", "default_lava.png",
			"default_lava.png", "default_lava.png", "default_lava.png",
		},
		visual_size = {x = 0.7, y = 0.7, z = 0.7},
		collisionbox = {-0.3, -0.3, -0.3, 0.3, 0.3, 0.3},
		physical = true,
		collide_with_objects = false,
		pointable = false,
		static_save = false,
		glow = 14,
	},

	on_activate = function(self)
		self.age = 0
		self.trail_timer = 0
		self.style = EJECTA_STYLES.lava
		self.counted = true
		active_ejecta_count = active_ejecta_count + 1
		self.object:set_acceleration({x = 0, y = -14.0, z = 0})
	end,

	on_deactivate = function(self)
		if self.counted then
			self.counted = false
			active_ejecta_count = math_max(0, active_ejecta_count - 1)
		end
	end,

	configure = function(self, style_name, vel)
		local style = EJECTA_STYLES[style_name] or EJECTA_STYLES.lava
		self.style = style
		local t = style.texture
		local s = style.size
		self.object:set_properties({
			textures = {t, t, t, t, t, t},
			visual_size = {x = s, y = s, z = s},
			glow = style.glow,
		})
		self.object:set_velocity(vel)
	end,

	on_step = function(self, dtime, moveresult)
		self.age = (self.age or 0) + dtime
		local pos = self.object:get_pos()
		if not pos or self.age > 12.0 then
			remove_ejecta(self)
			return
		end

		local cur_node = api.get_node_or_nil(pos)
		if not cur_node or cur_node.name == "ignore" then
			remove_ejecta(self)
			return
		end

		-- Trailing ember/smoke particles in flight
		self.trail_timer = (self.trail_timer or 0) + dtime
		if self.trail_timer >= 0.08 and api.add_particle then
			self.trail_timer = 0
			local hot = self.style and self.style.hot
			api.add_particle({
				pos = pos,
				velocity = {x = (math_random() - 0.5) * 1.2, y = 0.8, z = (math_random() - 0.5) * 1.2},
				acceleration = {x = 0, y = hot and -2.0 or 0.4, z = 0},
				expirationtime = 0.55 + math_random() * 0.45,
				size = hot and 2.2 or 2.6,
				collisiondetection = false,
				texture = hot and "default_lava.png" or "default_coal_block.png^[opacity:150",
				glow = hot and 14 or 0,
			})
		end

		-- Grace period so projectiles clear the crater throat before checking collisions
		if self.age < 0.25 then
			return
		end

		local hit = (moveresult and moveresult.collides)
		if not hit and cur_node.name ~= "air"
			and cur_node.name ~= "default:lava_source"
			and cur_node.name ~= "default:lava_flowing" then
			hit = true
		end

		-- Also detonate on landing in lava sea after descending
		local vel = self.object:get_velocity()
		if not hit and vel and vel.y < -1.0
			and (cur_node.name == "default:lava_source" or cur_node.name == "default:lava_flowing") then
			hit = true
		end

		if hit then
			ejecta_impact(pos, self.style or EJECTA_STYLES.lava)
			remove_ejecta(self)
		end
	end,
})

local function launch_ejecta_volley(vent_pos, crater_r, intensity, count)
	for _ = 1, count do
		if active_ejecta_count >= MAX_ACTIVE_EJECTA then
			return
		end
		local r_off = math_random() * math_max(2, crater_r * 0.55)
		local ang_off = math_random() * math_pi * 2
		local spawn_p = {
			x = vent_pos.x + math_cos(ang_off) * r_off,
			y = vent_pos.y + 1.5 + math_random() * 2.5,
			z = vent_pos.z + math_sin(ang_off) * r_off,
		}

		local obj = api.add_entity(spawn_p, modname .. ":ejecta")
		if obj then
			local ent = obj:get_luaentity()
			if ent and ent.configure then
				local roll = math_random()
				local style_name
				if roll < 0.52 then
					style_name = "lava"
				elseif roll < 0.74 then
					style_name = "obsidian"
				elseif roll < 0.88 then
					style_name = "scoria"
				else
					style_name = "cobble"
				end

				local launch_ang = math_random() * math_pi * 2
				local horiz = (6.0 + math_random() * 15.0) * intensity
				local vert = (15.0 + math_random() * 14.0) * intensity
				ent:configure(style_name, {
					x = math_cos(launch_ang) * horiz,
					y = vert,
					z = math_sin(launch_ang) * horiz,
				})
			end
		end
	end
end

--------------------------------------------------------------------------------
-- 12. Crater Explosion & Multi-Phase Eruption Engine
--------------------------------------------------------------------------------

local active_eruptions = {}
local active_eruption_count = 0
local volcano_cooldowns = {}
local world_clock = 0
local check_timer = 0
local smoke_timer = 0

local function find_current_vent_pos(v)
	-- Scan vertically around the expected caldera lava elevation to adapt to terrain changes
	local min_y = math_max(LAVA_SEA_LEVEL + 2, v.lava_y - 10)
	local max_y = v.rim_y + 10
	local top_non_air = nil
	local any_loaded = false

	for y = max_y, min_y, -1 do
		local n = api.get_node_or_nil({x = v.x, y = y, z = v.z})
		if not n or n.name == "ignore" then
			return nil -- Crater area is not currently loaded
		end
		any_loaded = true
		if n.name ~= "air" then
			top_non_air = y
			break
		end
	end

	if not any_loaded then
		return nil
	end
	return {x = v.x, y = top_non_air or v.lava_y, z = v.z}
end

local function detonate_crater(vent_pos, v, intensity)
	ensure_content_ids()

	-- Multi-layered volcanic explosion audio
	if has_tnt_mod then
		play_volcano_sound("tnt_explode", vent_pos, 2.0, 0.75, 190)
	end
	play_volcano_sound("default_cool_lava", vent_pos, 2.0, 0.35, 180)
	play_volcano_sound("default_hard_footstep", vent_pos, 2.0, 0.30, 160)
	play_volcano_sound("default_break_glass", vent_pos, 1.3, 0.25, 150)

	local r = math_floor(math_max(3, math_min(9, BASE_BLAST_RADIUS * intensity)))
	local p1 = {x = vent_pos.x - r - 1, y = vent_pos.y - r - 1, z = vent_pos.z - r - 1}
	local p2 = {x = vent_pos.x + r + 1, y = vent_pos.y + r + 1, z = vent_pos.z + r + 1}

	-- Carve irregular blast cavity and surge fresh `default:lava_source` inside the vent
	local vm = api.get_voxel_manip()
	local emin, emax = vm:read_from_map(p1, p2)
	local area = VoxelArea:new({MinEdge = emin, MaxEdge = emax})
	local data = vm:get_data()

	local pipe_r = math_max(2, math_min(r - 1, math_floor(v.conduit_r)))
	local r_sq = r * r

	for z = p1.z, p2.z do
		local dz = z - vent_pos.z
		for y = p1.y, p2.y do
			local dy = y - vent_pos.y
			for x = p1.x, p2.x do
				local dx = x - vent_pos.x
				local dist_sq = dx * dx + dy * dy * 0.85 + dz * dz
				if dist_sq <= r_sq then
					local wp = {x = x, y = y, z = z}
					local vi = area:index(x, y, z)
					local cur = data[vi]

					if cur ~= c_ignore and not is_node_protected(wp) then
						local horiz_sq = dx * dx + dz * dz
						if y <= vent_pos.y - 1 then
							-- Refill central throat with fresh molten lava so the volcano never dies
							if horiz_sq <= pipe_r * pipe_r then
								data[vi] = c_lava
							elseif cur ~= c_obsidian and dist_sq >= (r - 1.2) * (r - 1.2) and math_random() < 0.5 then
								data[vi] = c_obsidian
							end
						elseif y == vent_pos.y and horiz_sq <= (pipe_r - 0.5) * (pipe_r - 0.5) then
							-- Surging magma dome right in the center
							data[vi] = c_lava
						else
							-- Upper explosion cavity: blow out rock, leave rugged rim
							local edge_factor = dist_sq / r_sq
							if edge_factor < 0.72 or math_random() < 0.65 then
								if cur ~= c_obsidian or edge_factor < 0.35 then
									data[vi] = c_air
								end
							elseif cur ~= c_air and cur ~= c_lava and math_random() < 0.45 then
								data[vi] = (math_random() < 0.5) and c_cobble or c_coalblock
							end
						end
					end
				end
			end
		end
	end

	vm:set_data(data)
	vm:write_to_map(true)
	vm:update_liquids()

	-- Shockwave damage & towering eruption plume
	apply_blast_damage(vent_pos, r * 3.2, math_floor(14 * intensity), 14.0 * intensity)
	spawn_explosion_plume(vent_pos, v.crater_r, intensity)
end

local function start_eruption(v, force_intensity)
	if active_eruptions[v.key] then
		return false, "This volcano is already erupting."
	end
	local vent_pos = find_current_vent_pos(v)
	if not vent_pos then
		return false, "Volcano crater area is not currently loaded."
	end

	local base_int = 1.0
	if v.kind == "stratovolcano" then
		base_int = 1.15
	elseif v.kind == "caldera" then
		base_int = 1.25
	else
		base_int = 0.85
	end
	local intensity = force_intensity or (base_int * (0.85 + math_random() * 0.35))

	local rumble_dur = 4.5 + math_random() * 2.0
	local erupt_dur = 5.5 + math_random() * 3.0
	local aftermath_dur = 6.0

	active_eruptions[v.key] = {
		volcano = v,
		vent_pos = vent_pos,
		intensity = intensity,
		elapsed = 0,
		rumble_dur = rumble_dur,
		erupt_end = rumble_dur + erupt_dur,
		total_dur = rumble_dur + erupt_dur + aftermath_dur,
		next_rumble_fx = 0,
		blast_done = false,
		next_wave = rumble_dur + 0.15,
		aftermath_started = false,
	}
	active_eruption_count = active_eruption_count + 1

	-- Initial seismic warning rumble
	play_volcano_sound("default_cool_lava", vent_pos, 1.5, 0.45, 160)
	play_volcano_sound("default_gravel_footstep", vent_pos, 1.5, 0.38, 140)
	spawn_crater_smoke(vent_pos, v.crater_r, intensity * 1.2, true)

	api.log("action", string.format(
		"[%s] %s eruption started at (%d, %d, %d) intensity=%.2f",
		modname, v.kind, vent_pos.x, vent_pos.y, vent_pos.z, intensity
	))
	return true, vent_pos
end

local function update_active_eruptions(dtime)
	local finished_keys = nil
	for key, er in pairs(active_eruptions) do
		er.elapsed = er.elapsed + dtime
		local v = er.volcano
		local vent = er.vent_pos
		local intensity = er.intensity

		if er.elapsed < er.rumble_dur then
			-- Phase 1: Escalating rumble & smoke warning column
			if er.elapsed >= er.next_rumble_fx then
				er.next_rumble_fx = er.elapsed + 1.25
				local progress = er.elapsed / er.rumble_dur
				play_volcano_sound("default_cool_lava", vent, 1.2 + progress * 0.7, 0.42 + progress * 0.15, 160)
				spawn_crater_smoke(vent, v.crater_r, intensity * (1.0 + progress * 0.9), true)
			end
		elseif er.elapsed < er.erupt_end then
			-- Phase 2: Main volcanic explosion + ballistic lava bomb volleys
			if not er.blast_done then
				er.blast_done = true
				detonate_crater(vent, v, intensity)
			end

			if er.elapsed >= er.next_wave then
				er.next_wave = er.elapsed + 1.15 + math_random() * 0.55
				local volley_size = math_floor(4 + math_random() * 4 * intensity)
				launch_ejecta_volley(vent, v.crater_r, intensity, volley_size)
				spawn_crater_smoke(vent, v.crater_r, intensity * 1.4, true)
				play_volcano_sound("default_cool_lava", vent, 1.4, 0.5 + math_random() * 0.25, 150)
			end
		elseif er.elapsed < er.total_dur then
			-- Phase 3: Ashfall & cooling aftermath
			if not er.aftermath_started then
				er.aftermath_started = true
				spawn_ashfall(vent, v.crater_r, intensity)
				play_volcano_sound("default_cool_lava", vent, 1.0, 0.8, 120)
			end
		else
			finished_keys = finished_keys or {}
			finished_keys[#finished_keys + 1] = key
		end
	end

	if finished_keys then
		for i = 1, #finished_keys do
			local key = finished_keys[i]
			active_eruptions[key] = nil
			active_eruption_count = math_max(0, active_eruption_count - 1)
			volcano_cooldowns[key] = world_clock + ERUPTION_COOLDOWN * (0.8 + math_random() * 0.5)
		end
	end
end

local function collect_player_nearby_volcanoes(radius)
	local players = api.get_connected_players and api.get_connected_players() or {}
	if #players == 0 then
		return {}
	end

	local seen = {}
	local result = {}
	local r_sq = radius * radius

	for i = 1, #players do
		local ppos = players[i]:get_pos()
		if ppos then
			local min_cx = math_floor((ppos.x - radius) / CELL_SIZE)
			local max_cx = math_floor((ppos.x + radius) / CELL_SIZE)
			local min_cz = math_floor((ppos.z - radius) / CELL_SIZE)
			local max_cz = math_floor((ppos.z + radius) / CELL_SIZE)

			for cz = min_cz, max_cz do
				for cx = min_cx, max_cx do
					local v = get_volcano_in_cell(cx, cz)
					if v and not seen[v.key] then
						local dx = v.x - ppos.x
						local dz = v.z - ppos.z
						if (dx * dx + dz * dz) <= r_sq then
							seen[v.key] = true
							result[#result + 1] = v
						end
					end
				end
			end
		end
	end

	return result
end

api.register_globalstep(function(dtime)
	local dt = math_min(dtime, 0.5)
	world_clock = world_clock + dt

	if active_eruption_count > 0 then
		update_active_eruptions(dt)
	end

	-- Periodic ambient crater smoke on dormant loaded volcanoes near players
	if AMBIENT_SMOKE_ENABLED then
		smoke_timer = smoke_timer + dt
		if smoke_timer >= 4.0 then
			smoke_timer = 0
			local nearby = collect_player_nearby_volcanoes(math_min(ACTIVE_RADIUS, 150))
			if #nearby > 0 then
				local v = nearby[math_random(1, #nearby)]
				if not active_eruptions[v.key] then
					local vent = find_current_vent_pos(v)
					if vent then
						spawn_crater_smoke(vent, v.crater_r, 0.65, math_random() < 0.35)
					end
				end
			end
		end
	end

	-- Periodic check to trigger occasional volcanic eruptions near players
	if ERUPTIONS_ENABLED then
		check_timer = check_timer + dt
		if check_timer >= ERUPTION_CHECK_INTERVAL then
			check_timer = 0
			if active_eruption_count < MAX_CONCURRENT then
				local nearby = collect_player_nearby_volcanoes(ACTIVE_RADIUS)
				for i = 1, #nearby do
					if active_eruption_count >= MAX_CONCURRENT then
						break
					end
					local v = nearby[i]
					local cd = volcano_cooldowns[v.key] or 0
					if not active_eruptions[v.key] and world_clock >= cd then
						if math_random() < ERUPTION_CHANCE then
							start_eruption(v)
						end
					end
				end
			end
		end
	end
end)

--------------------------------------------------------------------------------
-- 13. Public Mod API & Utility Chat Commands
--------------------------------------------------------------------------------

function mapgen_volcano.get_volcano_in_cell(cx, cz)
	return get_volcano_in_cell(cx, cz)
end

function mapgen_volcano.get_nearest_volcano(pos, search_cells)
	local rad = search_cells or 2
	local base_cx = math_floor(pos.x / CELL_SIZE)
	local base_cz = math_floor(pos.z / CELL_SIZE)
	local best_v = nil
	local best_dist_sq = math.huge

	for cz = base_cz - rad, base_cz + rad do
		for cx = base_cx - rad, base_cx + rad do
			local v = get_volcano_in_cell(cx, cz)
			if v then
				local dx = v.x - pos.x
				local dz = v.z - pos.z
				local dsq = dx * dx + dz * dz
				if dsq < best_dist_sq then
					best_dist_sq = dsq
					best_v = v
				end
			end
		end
	end

	if best_v then
		return best_v, math_sqrt(best_dist_sq)
	end
	return nil, nil
end

function mapgen_volcano.trigger_eruption(pos, intensity)
	local v, dist = mapgen_volcano.get_nearest_volcano(pos, 2)
	if not v then
		return false, "No volcano found nearby."
	end
	local ok, info = start_eruption(v, intensity)
	return ok, info, v, dist
end

local function compass_direction(dx, dz)
	local ang = atan2(dx, dz) -- +Z = North, +X = East in Luanti
	local oct = math_floor(((ang + math_pi) / (math_pi / 4)) + 0.5) % 8
	local names = {"S", "SW", "W", "NW", "N", "NE", "E", "SE"}
	return names[oct + 1] or "N"
end

api.register_chatcommand("volcano_info", {
	description = "Show distance, direction, and status of the nearest volcano",
	func = function(name)
		local player = api.get_player_by_name(name)
		if not player then
			return false, "Player not found."
		end
		local pos = player:get_pos()
		local v, dist = mapgen_volcano.get_nearest_volcano(pos, 2)
		if not v then
			return false, "No volcano found within range."
		end
		local dir = compass_direction(v.x - pos.x, v.z - pos.z)
		local status = "dormant"
		if active_eruptions[v.key] then
			status = "ERUPTING"
		elseif (volcano_cooldowns[v.key] or 0) > world_clock then
			status = string.format("cooling (%ds)", math_floor(volcano_cooldowns[v.key] - world_clock))
		end
		return true, string.format(
			"Nearest volcano: %s at (%d, %d, %d) — %d nodes %s | status: %s",
			v.kind, v.x, v.rim_y, v.z, math_floor(dist), dir, status
		)
	end,
})

api.register_chatcommand("volcano_erupt", {
	description = "Immediately trigger an explosive eruption at the nearest loaded volcano",
	privs = {server = true},
	func = function(name)
		local player = api.get_player_by_name(name)
		if not player then
			return false, "Player not found."
		end
		local pos = player:get_pos()
		local ok, info, v, dist = mapgen_volcano.trigger_eruption(pos)
		if not ok then
			return false, tostring(info)
		end
		return true, string.format(
			"Triggered %s eruption at (%d, %d, %d) (%d nodes away)!",
			v.kind, info.x, info.y, info.z, math_floor(dist or 0)
		)
	end,
})

api.register_on_mods_loaded(function()
	ensure_content_ids()
	world_seed_hash = parse_world_seed()
	api.log("action", "[" .. modname .. "] Volcanic terrain mapgen initialized (pure default nodes, eruptions=" .. tostring(ERUPTIONS_ENABLED) .. ").")
end)
