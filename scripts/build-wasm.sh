#!/usr/bin/env bash
# scripts/build-wasm.sh — Reproducible Lean 4.36 -> C -> Emscripten WASM pipeline
# Compiles ALL 33 strictly Init-only Lean 4.36 modules (direct GA kernels +
# full Grassmann.Studio: 77 CoffeeShop presets incl. dual-handle sculpted bunny
# #pga3d_slicing, Barth Sextic, Dupin Cyclide, Involute Gears, Terrell-Penrose,
# Maxwell streamlines, 6-stop Guided Tour, 17 Wedge 2D+3D levels, 6 animated
# Wedge tutorials, LiveScript v2 parser/evaluator, bytecode Marching Tetrahedra
# Implicit3D, AD surfaces, marching-triangles contours, GAlculator, exact R3
# rational rotors, WGSL/GLSL/MSL GPU shader codegen)
# + c/grassmann_cabi.c + wasm/lean_wasm_rt.c into wasm/dist/grassmann.{wasm,mjs}!
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
dist_dir="${GRASSMANN_WASM_OUT:-$repo_root/wasm/dist}"
stage_inc="$repo_root/.lake/build/wasm_inc"

command -v emcc >/dev/null 2>&1 || { echo "ERROR: emcc not found in PATH" >&2; exit 1; }
lean_sysroot="$(lake --dir "$repo_root" env lean --print-prefix)"

mods=(
  Grassmann.CABI.Kernels
  Grassmann.CABI.Alg
  Grassmann.Scene.Types
  Grassmann.Scene.Json
  Grassmann.Scene.Binary
  Grassmann.Scene
  Grassmann.Eval.Parser
  Grassmann.Eval.Contour
  Grassmann.Eval.Engine
  Grassmann.Eval.Calc
  Grassmann.Eval.Implicit3D
  Grassmann.Eval.ImplicitExpr
  Grassmann.Eval
  Grassmann.Wedge.Types
  Grassmann.Wedge.Levels2D
  Grassmann.Wedge.Levels3D
  Grassmann.Wedge.Tutorials
  Grassmann.Wedge.Engine
  Grassmann.Wedge
  Grassmann.CoffeeShop.Mesh
  Grassmann.Codegen.GPU
  Grassmann.Codegen.GPUInit
  Grassmann.Codegen
  Grassmann.CoffeeShop.Presets
  Grassmann.CoffeeShop.PresetsExtra
  Grassmann.CoffeeShop.PresetsParity
  Grassmann.CoffeeShop.PresetsShowcase
  Grassmann.CoffeeShop.Tour
  Grassmann.CoffeeShop.Engine
  Grassmann.CoffeeShop
  Grassmann.Studio
  Grassmann.CABI.Studio
  Grassmann.CABI
)

targets=()
for m in "${mods[@]}"; do
  targets+=("${m}:c")
done

echo "[wasm] generating ${#mods[@]} strictly Init-only Lean 4.36 C sources (--wfail)"
lake --dir "$repo_root" build --wfail "${targets[@]}"

c_files=()
while IFS= read -r line; do
  [[ -n "$line" ]] && c_files+=("$line")
done < <(lake --dir "$repo_root" query "${targets[@]}")

if (( ${#c_files[@]} != ${#mods[@]} )); then
  echo "ERROR: expected ${#mods[@]} C files from lake query, got ${#c_files[@]}" >&2
  exit 1
fi
for f in "${c_files[@]}"; do
  [[ -f "$f" ]] || { echo "missing Lean-generated C file: $f" >&2; exit 1; }
done

mkdir -p "$dist_dir" "$stage_inc/lean"
# Stage lean.h for wasm32 with three verified patches:
# 1. Inline no-op lean_inc_heartbeat() to avoid cross-TU calls on every small alloc.
# 2. 8-byte (uint64_t) prefix header in lean_alloc_small_object / lean_small_object_size /
#    lean_free_small_object so EVERY wasm32 heap object (FloatArray, bignat, boxed Float,
#    ctor) is strictly 0 mod 8 instead of 4 mod 8 (sizeof(size_t) == 4 on wasm32).
# 3. __builtin_memcpy in lean_ctor_{get,set}_{uint64,float} so constructors with an odd
#    number of 32-bit object fields (offset = sizeof(void*)*1,3,5) never perform
#    misaligned 8-byte pointer dereferences on wasm32.
uv run python - "$lean_sysroot/include/lean/lean.h" "$stage_inc/lean/lean.h" << 'PY'
import sys
src_path, dst_path = sys.argv[1], sys.argv[2]
text = open(src_path, "r", encoding="utf-8").read()

patches = [
    (
        "LEAN_EXPORT void lean_inc_heartbeat(void);",
        "static inline void lean_inc_heartbeat(void) {}",
        "inline lean_inc_heartbeat",
    ),
    (
        "    void * mem = malloc(sizeof(size_t) + sz);\n"
        "    if (mem == 0) lean_internal_panic_out_of_memory();\n"
        "    *(size_t*)mem = sz;\n"
        "    return (lean_object*)((size_t*)mem + 1);",
        "    void * mem = malloc(sizeof(uint64_t) + (size_t)sz);\n"
        "    if (mem == 0) lean_internal_panic_out_of_memory();\n"
        "    *(uint64_t*)mem = (uint64_t)sz;\n"
        "    return (lean_object*)((uint64_t*)mem + 1);",
        "8-byte aligned lean_alloc_small_object",
    ),
    (
        "    return *((size_t*)o - 1);",
        "    return (unsigned)(*((uint64_t*)o - 1));",
        "8-byte aligned lean_small_object_size",
    ),
    (
        "    size_t* ptr = (size_t*)o - 1;\n"
        "    free_sized(ptr, *ptr + sizeof(size_t));",
        "    uint64_t* ptr = (uint64_t*)o - 1;\n"
        "    free(ptr);",
        "8-byte aligned lean_free_small_object",
    ),
    (
        "static inline uint64_t lean_ctor_get_uint64(b_lean_obj_arg o, unsigned offset) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    return *((uint64_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));\n"
        "}",
        "static inline uint64_t lean_ctor_get_uint64(b_lean_obj_arg o, unsigned offset) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    uint64_t v;\n"
        "    __builtin_memcpy(&v, (uint8_t*)(lean_ctor_obj_cptr(o)) + offset, sizeof(v));\n"
        "    return v;\n"
        "}",
        "unaligned-safe lean_ctor_get_uint64",
    ),
    (
        "static inline double lean_ctor_get_float(b_lean_obj_arg o, unsigned offset) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    return *((double*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));\n"
        "}",
        "static inline double lean_ctor_get_float(b_lean_obj_arg o, unsigned offset) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    double v;\n"
        "    __builtin_memcpy(&v, (uint8_t*)(lean_ctor_obj_cptr(o)) + offset, sizeof(v));\n"
        "    return v;\n"
        "}",
        "unaligned-safe lean_ctor_get_float",
    ),
    (
        "static inline void lean_ctor_set_uint64(b_lean_obj_arg o, unsigned offset, uint64_t v) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    *((uint64_t*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;\n"
        "}",
        "static inline void lean_ctor_set_uint64(b_lean_obj_arg o, unsigned offset, uint64_t v) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    __builtin_memcpy((uint8_t*)(lean_ctor_obj_cptr(o)) + offset, &v, sizeof(v));\n"
        "}",
        "unaligned-safe lean_ctor_set_uint64",
    ),
    (
        "static inline void lean_ctor_set_float(b_lean_obj_arg o, unsigned offset, double v) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    *((double*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;\n"
        "}",
        "static inline void lean_ctor_set_float(b_lean_obj_arg o, unsigned offset, double v) {\n"
        "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
        "    __builtin_memcpy((uint8_t*)(lean_ctor_obj_cptr(o)) + offset, &v, sizeof(v));\n"
        "}",
        "unaligned-safe lean_ctor_set_float",
    ),
]

for old, new, label in patches:
    n = text.count(old)
    if n != 1:
        raise SystemExit(f"ERROR: staged lean.h patch '{label}' matched {n} times (expected 1)")
    text = text.replace(old, new, 1)

open(dst_path, "w", encoding="utf-8").write(text)
PY
cp "$lean_sysroot/include/lean/version.h" "$stage_inc/lean/version.h"
cat > "$stage_inc/lean/config.h" << 'EOF'
#pragma once
#include <lean/version.h>
#define LEAN_EMSCRIPTEN 1
#define LEAN_IS_STAGE0 0
#define GRASSMANN_WASM_INLINE_HEARTBEAT 1
#define GRASSMANN_WASM_ALIGN8_ALLOC 1
EOF
: > "$stage_inc/lean/lean_gmp.h"
: > "$stage_inc/lean/lean_libuv.h"

exported_fns='[
  "_malloc","_free",
  "_grassmann_wasm_alignment_selftest","_grassmann_wasm_misaligned_allocs","_grassmann_wasm_alloc_count",
  "_grassmann_cabi_version","_grassmann_initialize","_grassmann_initialize_module",
  "_grassmann_attach_thread","_grassmann_detach_thread",
  "_grassmann_studio_create","_grassmann_studio_destroy",
  "_grassmann_studio_dispatch_bin","_grassmann_studio_dispatch_json",
  "_grassmann_studio_get_frame","_grassmann_studio_preset_catalog","_grassmann_studio_tour_catalog",
  "_grassmann_cl_mul","_grassmann_cl_wedge","_grassmann_cl_join",
  "_grassmann_cl_left_contract","_grassmann_cl_reverse","_grassmann_cl_dual","_grassmann_cl_sandwich",
  "_grassmann_sta_mul","_grassmann_sta_wedge","_grassmann_sta_left_contract",
  "_grassmann_sta_reverse","_grassmann_sta_boost_rotor","_grassmann_sta_sandwich","_grassmann_sta_spatial_wedge",
  "_grassmann_r3_mul","_grassmann_r3_wedge","_grassmann_r3_reverse","_grassmann_r3_sandwich",
  "_grassmann_r3_apply_rational_rotor","_grassmann_r3_rational_rotor_cayley",
  "_grassmann_pga2_mul","_grassmann_pga2_meet","_grassmann_pga2_join",
  "_grassmann_pga2_left_contract","_grassmann_pga2_reverse","_grassmann_pga2_point","_grassmann_pga2_line","_grassmann_pga2_sandwich",
  "_grassmann_pga3_mul","_grassmann_pga3_meet","_grassmann_pga3_join","_grassmann_pga3_left_contract","_grassmann_pga3_reverse",
  "_grassmann_pga3_make_rotor","_grassmann_pga3_make_translator","_grassmann_pga3_motor_compose",
  "_grassmann_pga3_motor_reverse","_grassmann_pga3_motor_is_unit","_grassmann_pga3_motor_normalize",
  "_grassmann_pga3_motor_inverse","_grassmann_pga3_motor_exp","_grassmann_pga3_motor_log",
  "_grassmann_pga3_motor_slerp","_grassmann_pga3_motor_to_mat4",
  "_grassmann_pga3_motor_apply_xyz","_grassmann_pga3_motor_apply_xyz_batch",
  "_grassmann_cga2_mul","_grassmann_cga2_wedge","_grassmann_cga2_up",
  "_grassmann_cga3_mul","_grassmann_cga3_wedge","_grassmann_cga3_left_contract","_grassmann_cga3_reverse",
  "_grassmann_cga3_sandwich","_grassmann_cga3_up","_grassmann_cga3_down",
  "_grassmann_cga3_dual_sphere","_grassmann_cga3_dual_plane"
]'

obj_dir="$repo_root/.lake/build/wasm_obj"
rm -rf "$obj_dir" && mkdir -p "$obj_dir"
ncpu="$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)"

echo "[wasm] compiling ${#mods[@]} Lean 4.36 C modules + C ABI shim + lean_wasm_rt.c (hybrid -O3 hot / -Oz cold, jobs=${ncpu})"
wasm_objs=()
pids=()
common_cflags=(
  -DNDEBUG -ffunction-sections -fdata-sections -fvisibility=hidden
  -I"$stage_inc" -I"$repo_root/include"
  -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wno-unused-label
)

for idx in "${!mods[@]}"; do
  m="${mods[$idx]}"
  src="${c_files[$idx]}"
  obj="$obj_dir/$(printf "%02d_%s.o" "$idx" "${m//./_}")"
  wasm_objs+=("$obj")
  opt="-Oz"
  case "$m" in
    Grassmann.CABI.Kernels|Grassmann.CABI.Alg|Grassmann.Scene.Binary|Grassmann.Eval.Implicit3D|Grassmann.Eval.ImplicitExpr)
      opt="-O3"
      ;;
  esac
  emcc "$opt" "${common_cflags[@]}" -c "$src" -o "$obj" &
  pids+=($!)
  if (( ${#pids[@]} >= ncpu )); then
    wait "${pids[0]}"
    pids=("${pids[@]:1}")
  fi
done

emcc -O3 "${common_cflags[@]}" -c "$repo_root/c/grassmann_cabi.c" -o "$obj_dir/cabi.o" &
pids+=($!)
emcc -O3 "${common_cflags[@]}" -c "$repo_root/wasm/lean_wasm_rt.c" -o "$obj_dir/lean_wasm_rt.o" &
pids+=($!)
for pid in "${pids[@]}"; do
  wait "$pid"
done
wasm_objs+=("$obj_dir/cabi.o" "$obj_dir/lean_wasm_rt.o")

echo "[wasm] linking with emcc -Oz --gc-sections (dlmalloc, FILESYSTEM=0, SUPPORT_LONGJMP=0)"
emcc -Oz -Wl,--gc-sections \
  -sFILESYSTEM=0 \
  -sSUPPORT_LONGJMP=0 \
  -sASSERTIONS=0 \
  "${wasm_objs[@]}" \
  -sWASM=1 \
  -sALLOW_MEMORY_GROWTH=1 \
  -sINITIAL_MEMORY=33554432 \
  -sMODULARIZE=1 \
  -sEXPORT_ES6=1 \
  -sEXPORT_NAME='createGrassmannRaw' \
  -sEXPORTED_FUNCTIONS="$exported_fns" \
  -sEXPORTED_RUNTIME_METHODS='["HEAPU8","HEAPU32","HEAPF64"]' \
  -o "$dist_dir/grassmann.mjs"

cp "$repo_root/wasm/grassmann_wasm.mjs" "$dist_dir/grassmann_wasm.mjs"

# Emit content-fingerprinted WASM artifacts + wasm-manifest.json alongside canonical names
# so Vercel / CDN deployments can safely use long-lived immutable caching without cache poisoning!
rm -f "$dist_dir"/grassmann.[0-9a-f]*.wasm "$dist_dir"/grassmann.[0-9a-f]*.mjs
wasm_hash="$(shasum -a 256 "$dist_dir/grassmann.wasm" | awk '{print substr($1, 1, 10)}')"
fp_wasm="grassmann.${wasm_hash}.wasm"
fp_mjs="grassmann.${wasm_hash}.mjs"
cp "$dist_dir/grassmann.wasm" "$dist_dir/$fp_wasm"
sed "s/grassmann\.wasm/${fp_wasm}/g" "$dist_dir/grassmann.mjs" > "$dist_dir/$fp_mjs"
if rg -q 'grassmann\.wasm' "$dist_dir/$fp_mjs"; then
  echo "ERROR: fingerprinted loader $fp_mjs still references un-fingerprinted grassmann.wasm" >&2
  exit 1
fi
if ! rg -q "${fp_wasm}" "$dist_dir/$fp_mjs"; then
  echo "ERROR: fingerprinted loader $fp_mjs missing reference to $fp_wasm" >&2
  exit 1
fi

wasm_bytes="$(wc -c < "$dist_dir/grassmann.wasm" | tr -d ' ')"
gz_bytes="$(gzip -9 -c "$dist_dir/grassmann.wasm" | wc -c | tr -d ' ')"
cat > "$dist_dir/wasm-manifest.json" << EOF
{
  "version": 1,
  "hash": "${wasm_hash}",
  "wasmFile": "${fp_wasm}",
  "loaderFile": "${fp_mjs}",
  "canonicalWasmFile": "grassmann.wasm",
  "canonicalLoaderFile": "grassmann.mjs",
  "wrapperFile": "grassmann_wasm.mjs",
  "bytes": ${wasm_bytes},
  "gzipBytes": ${gz_bytes},
  "presetCount": 77
}
EOF

echo "[wasm] built artifacts (content hash=${wasm_hash}):"
ls -lh "$dist_dir/grassmann.wasm" "$dist_dir/grassmann.mjs" "$dist_dir/$fp_wasm" "$dist_dir/$fp_mjs" "$dist_dir/grassmann_wasm.mjs" "$dist_dir/wasm-manifest.json"
echo "[wasm] gzipped wasm size: ${gz_bytes} bytes ($((gz_bytes / 1024)).$(((gz_bytes % 1024) * 10 / 1024)) KB)"

echo "[wasm] running full Node.js verification + benchmark suite (all 77 presets + 6-stop Tour + Dots Round-2 regressions + 8B alignment + 17 Wedge levels)"
node "$repo_root/wasm/test_wasm.mjs"
