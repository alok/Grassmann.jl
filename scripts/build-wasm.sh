#!/usr/bin/env bash
# scripts/build-wasm.sh — Reproducible Lean 4.36 -> C -> Emscripten WASM pipeline
# Compiles ALL 25 strictly Init-only Lean 4.36 modules (direct GA kernels +
# full Grassmann.Studio: 19 CoffeeShop presets incl. sculpted bunny #pga3d_slicing,
# 16 Wedge 2D+3D levels, GA script parser/evaluator, AD surfaces, marching-triangles
# contours, GAlculator, exact R3 rational rotors, WGSL/GLSL/MSL GPU shader codegen)
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
  Grassmann.CoffeeShop.Engine
  Grassmann.CoffeeShop
  Grassmann.Studio
  Grassmann.CABI.Studio
  Grassmann.CABI
)

targets=()
c_files=()
for m in "${mods[@]}"; do
  targets+=("${m}:c")
  c_files+=("$repo_root/.lake/build/ir/${m//.//}.c")
done

echo "[wasm] generating ${#mods[@]} strictly Init-only Lean 4.36 C sources (--wfail)"
lake --dir "$repo_root" build --wfail "${targets[@]}"

for f in "${c_files[@]}"; do
  [[ -f "$f" ]] || { echo "missing Lean-generated C file: $f" >&2; exit 1; }
done

mkdir -p "$dist_dir" "$stage_inc/lean"
cp "$lean_sysroot/include/lean/lean.h" "$stage_inc/lean/lean.h"
cp "$lean_sysroot/include/lean/version.h" "$stage_inc/lean/version.h"
cat > "$stage_inc/lean/config.h" << 'EOF'
#pragma once
#include <lean/version.h>
#define LEAN_EMSCRIPTEN 1
#define LEAN_IS_STAGE0 0
EOF
: > "$stage_inc/lean/lean_gmp.h"
: > "$stage_inc/lean/lean_libuv.h"

exported_fns='[
  "_malloc","_free",
  "_grassmann_cabi_version","_grassmann_initialize","_grassmann_initialize_module",
  "_grassmann_attach_thread","_grassmann_detach_thread",
  "_grassmann_studio_create","_grassmann_studio_destroy",
  "_grassmann_studio_dispatch_bin","_grassmann_studio_dispatch_json",
  "_grassmann_studio_get_frame","_grassmann_studio_preset_catalog",
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

echo "[wasm] compiling ${#mods[@]} Lean 4.36 C modules + C ABI shim + lean_wasm_rt.c via emcc -O3"
emcc -O3 -DNDEBUG -ffunction-sections -fdata-sections -Wl,--gc-sections \
  -I"$stage_inc" \
  -I"$repo_root/include" \
  -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wno-unused-label \
  "${c_files[@]}" \
  "$repo_root/c/grassmann_cabi.c" \
  "$repo_root/wasm/lean_wasm_rt.c" \
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
  "presetCount": 69
}
EOF

echo "[wasm] built artifacts (content hash=${wasm_hash}):"
ls -lh "$dist_dir/grassmann.wasm" "$dist_dir/grassmann.mjs" "$dist_dir/$fp_wasm" "$dist_dir/$fp_mjs" "$dist_dir/grassmann_wasm.mjs" "$dist_dir/wasm-manifest.json"
echo "[wasm] gzipped wasm size: ${gz_bytes} bytes ($((gz_bytes / 1024)).$(((gz_bytes % 1024) * 10 / 1024)) KB)"

echo "[wasm] running full Node.js verification + benchmark suite (all 69 presets + Implicit3D/GPU + Wedge Tutorials/Random)"
node "$repo_root/wasm/test_wasm.mjs"
