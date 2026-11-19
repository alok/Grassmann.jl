#!/usr/bin/env bash
# scripts/build-wasm.sh — Reproducible Lean 4.36 -> C -> Emscripten WASM pipeline
# Compiles 100% genuine Lean 4.36 generated C code (`Grassmann.CABI.*`) +
# `c/grassmann_cabi.c` + `wasm/lean_wasm_rt.c` into `wasm/dist/grassmann.wasm`
# + `wasm/dist/grassmann_wasm.mjs` and runs the Node verification + benchmark suite.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
dist_dir="${GRASSMANN_WASM_OUT:-$repo_root/wasm/dist}"
stage_inc="$repo_root/.lake/build/wasm_inc"

command -v emcc >/dev/null 2>&1 || { echo "ERROR: emcc not found in PATH" >&2; exit 1; }
lean_sysroot="$(lake --dir "$repo_root" env lean --print-prefix)"

echo "[wasm] generating Lean 4.36 C sources (--wfail)"
lake --dir "$repo_root" build --wfail \
  'Grassmann.CABI.Kernels:c' \
  'Grassmann.CABI.ScenePack:c' \
  'Grassmann.CABI.Studio:c' \
  'Grassmann.CABI:c'

c_files=(
  "$repo_root/.lake/build/ir/Grassmann/CABI/Kernels.c"
  "$repo_root/.lake/build/ir/Grassmann/CABI/ScenePack.c"
  "$repo_root/.lake/build/ir/Grassmann/CABI/Studio.c"
  "$repo_root/.lake/build/ir/Grassmann/CABI.c"
)
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
  "_grassmann_cabi_version","_grassmann_initialize",
  "_grassmann_studio_create","_grassmann_studio_destroy",
  "_grassmann_studio_dispatch_bin","_grassmann_studio_dispatch_json",
  "_grassmann_studio_get_frame",
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

echo "[wasm] compiling Lean 4.36 C + C ABI shim + lean_wasm_rt.c via emcc -O3"
emcc -O3 -DNDEBUG \
  -I"$stage_inc" \
  -I"$repo_root/include" \
  -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wno-unused-label \
  "${c_files[@]}" \
  "$repo_root/c/grassmann_cabi.c" \
  "$repo_root/wasm/lean_wasm_rt.c" \
  -sWASM=1 \
  -sALLOW_MEMORY_GROWTH=1 \
  -sINITIAL_MEMORY=16777216 \
  -sMODULARIZE=1 \
  -sEXPORT_ES6=1 \
  -sEXPORT_NAME='createGrassmannRaw' \
  -sEXPORTED_FUNCTIONS="$exported_fns" \
  -sEXPORTED_RUNTIME_METHODS='["HEAPU8","HEAPU32","HEAPF64"]' \
  -o "$dist_dir/grassmann_raw.mjs"

cp "$repo_root/wasm/grassmann_wasm.mjs" "$dist_dir/grassmann_wasm.mjs"
# Rename wasm artifact cleanly? Keep grassmann_raw.wasm referenced by grassmann_raw.mjs
echo "[wasm] built artifacts:"
ls -lh "$dist_dir/grassmann_raw.wasm" "$dist_dir/grassmann_raw.mjs" "$dist_dir/grassmann_wasm.mjs"
gzip -c "$dist_dir/grassmann_raw.wasm" | wc -c | awk '{printf "[wasm] gzipped wasm size: %d bytes (%.1f KB)\n", $1, $1/1024.0}'

echo "[wasm] running Node.js verification + benchmark suite"
node "$repo_root/wasm/test_wasm.mjs"
