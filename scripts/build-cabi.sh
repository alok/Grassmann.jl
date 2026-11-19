#!/usr/bin/env bash
# scripts/build-cabi.sh — Build standalone Init-only Grassmann C ABI library
# Links ALL 25 Init-only modules (direct GA kernels + full Grassmann.Studio:
# 19 CoffeeShop presets, sculpted bunny #pga3d_slicing, 16 Wedge 2D+3D levels,
# GA script evaluator, AD surfaces, marching-triangles contours, GAlculator,
# R3 rational rotors, WGSL/GLSL/MSL GPU shader codegen) into a tiny standalone
# dylib with ZERO libleanshared / libLean / libStd / libLake / libssl deps!
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
out_dir="${GRASSMANN_CABI_OUT:-$repo_root/.lake/build/cabi}"
mkdir -p "$out_dir"

lean_sysroot="$(lake --dir "$repo_root" env lean --print-prefix)"
lean_libdir="$lean_sysroot/lib/lean"
lean_extlib="$lean_sysroot/lib"

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
  Grassmann.CoffeeShop.Engine
  Grassmann.CoffeeShop
  Grassmann.Studio
  Grassmann.CABI.Studio
  Grassmann.CABI
)

targets=()
for m in "${mods[@]}"; do
  targets+=("${m}:o.export")
done

echo "[cabi] building ${#mods[@]} strictly Init-only Lean export objects (--wfail)"
lake --dir "$repo_root" build --wfail "${targets[@]}" Grassmann.CABI.Kernels:c

objs=()
while IFS= read -r line; do
  [[ -n "$line" ]] && objs+=("$line")
done < <(lake --dir "$repo_root" query "${targets[@]}")
kernels_c="$(lake --dir "$repo_root" query Grassmann.CABI.Kernels:c)"

for obj in "${objs[@]}"; do
  [[ -f "$obj" ]] || { echo "missing object: $obj" >&2; exit 1; }
done

echo "[cabi] checking C11 and C++17 public header cleanliness"
cc -std=c11 -Wall -Wextra -Werror -fsyntax-only \
  -I"$lean_sysroot/include" -I"$repo_root/include" \
  "$repo_root/c/grassmann_cabi.c"
c++ -std=c++17 -Wall -Wextra -Werror -fsyntax-only \
  -I"$repo_root/include" \
  "$repo_root/c/cabi_header_probe.cpp"

echo "[cabi] compiling C shim"
cc -std=c11 -O3 -DNDEBUG -fPIC -fvisibility=hidden -Wall -Wextra -Werror \
  -I"$lean_sysroot/include" -I"$repo_root/include" \
  -c "$repo_root/c/grassmann_cabi.c" \
  -o "$out_dir/grassmann_cabi.o"

# Build static archive (for host embedding)
rm -f "$out_dir/libgrassmann_cabi.a"
ar rcs "$out_dir/libgrassmann_cabi.a" "$out_dir/grassmann_cabi.o" "${objs[@]}"

case "$(uname -s)" in
  Darwin)
    dylib="$out_dir/libgrassmann_cabi.dylib"
    echo "[cabi] linking standalone Init-only macOS dylib (dead-stripped, ZERO libleanshared!)"
    cc -O3 -dynamiclib \
      -Wl,-dead_strip \
      -Wl,-install_name,@rpath/libgrassmann_cabi.dylib \
      -Wl,-exported_symbols_list,<(nm -g "$out_dir/grassmann_cabi.o" | awk '$2 == "T" && $3 ~ /^_grassmann_/ {print $3}') \
      "$out_dir/grassmann_cabi.o" "${objs[@]}" \
      "$lean_libdir/libInit.a" \
      "$lean_libdir/libleanrt.a" \
      "$lean_libdir/libcadical.a" \
      "$lean_extlib/libgmp.a" \
      "$lean_extlib/libuv.a" \
      -lc++ -lm -lpthread \
      -o "$dylib"

    echo "[cabi] verifying dylib size and dependencies:"
    ls -lh "$dylib"
    otool -L "$dylib"
    if otool -L "$dylib" | rg -q 'leanshared|libLean|libStd|libLake|libssl|libcrypto'; then
      echo "ERROR: standalone dylib unexpectedly links heavy Lean/SSL libs!" >&2
      exit 1
    fi
    size_bytes="$(stat -f%z "$dylib")"
    echo "[cabi] standalone dylib exact size: $size_bytes bytes ($((size_bytes / 1024)) KB)"
    if (( size_bytes > 15 * 1024 * 1024 )); then
      echo "ERROR: dylib exceeded 15 MB target!" >&2
      exit 1
    fi
    ;;
  Linux)
    dylib="$out_dir/libgrassmann_cabi.so"
    cc -O3 -shared -Wl,--gc-sections \
      -Wl,-soname,libgrassmann_cabi.so \
      "$out_dir/grassmann_cabi.o" "${objs[@]}" \
      "$lean_libdir/libInit.a" \
      "$lean_libdir/libleanrt.a" \
      "$lean_libdir/libcadical.a" \
      -lgmp -luv -lstdc++ -lm -lpthread \
      -o "$dylib"
    ls -lh "$dylib"
    ;;
  *)
    echo "unsupported OS: $(uname -s)" >&2
    exit 2
    ;;
esac

echo "[cabi] checking ALOK-1007 generated-C linearity on hot batch loop (Kernels.c)"
uv run python - "$kernels_c" << 'PY'
import pathlib, re, sys
src = pathlib.Path(sys.argv[1]).read_text()
m = re.search(r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_CABI_Kernels_pga3MotorApplyXYZBatch_go\([^)]*\)\{.*?(?=\nLEAN_EXPORT )", src, re.S)
assert m, "Missing pga3MotorApplyXYZBatch_go loop in Kernels.c"
body = m.group(0)
assert "lean_float_array_fget(" in body or "lean_float_array_uget(" in body, "Missing direct FloatArray get in hot loop"
assert "lean_float_array_push(" in body, "Missing linear lean_float_array_push in hot loop"
assert "goto _start;" in body, "Hot loop not tail-call compiled"
for bad in ("lean_box_float", "lean_alloc_closure", "lean_nat_mul", "l_Float_ofScientific"):
    assert bad not in body, f"ALOK-1007 violation: found {bad} inside hot batch loop"
m2 = re.search(r"LEAN_EXPORT lean_object\* lp_Grassmann_Grassmann_CABI_Kernels_pga3MotorApplyXYZBatch\([^)]*\)\{.*?(?=\nLEAN_EXPORT )", src, re.S)
assert m2 and "lean_mk_empty_float_array(" in m2.group(0), "Missing single preallocated lean_mk_empty_float_array"
print("[cabi] ALOK-1007 linearity PASS (prealloc FloatArray, direct fget/push, tail goto _start, zero boxing/closures/mul)")
PY

echo "[cabi] building and running C11 smoke test + parity dumper + benchmark"
cc -std=c11 -O2 -Wall -Wextra -Werror \
  -I"$repo_root/include" \
  "$repo_root/c/cabi_smoke.c" \
  -L"$out_dir" -lgrassmann_cabi -lm \
  -Wl,-rpath,"$out_dir" \
  -o "$out_dir/cabi_smoke"

cc -std=c11 -O2 -Wall -Wextra -Werror \
  -I"$repo_root/include" \
  "$repo_root/c/cabi_parity_dump.c" \
  -L"$out_dir" -lgrassmann_cabi -lm \
  -Wl,-rpath,"$out_dir" \
  -o "$out_dir/cabi_parity_dump"

"$out_dir/cabi_smoke"
