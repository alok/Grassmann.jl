#!/usr/bin/env bash
# scripts/build-cabi.sh — Build standalone Init-only Grassmann C ABI library
# Produces a tiny ~2–5 MB standalone dylib (vs 182–264 MB with Lean compiler!)
# with ZERO libleanshared / libLean / libStd / libLake dependencies, and runs
# the C++17 header probe + C11 verification & latency benchmark suite.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/.." && pwd)"
out_dir="${GRASSMANN_CABI_OUT:-$repo_root/.lake/build/cabi}"
mkdir -p "$out_dir"

lean_sysroot="$(lake --dir "$repo_root" env lean --print-prefix)"
lean_libdir="$lean_sysroot/lib/lean"
lean_extlib="$lean_sysroot/lib"

echo "[cabi] building Init-only Lean export objects (--wfail)"
LAKE_CACHE_DIR='' lake --dir "$repo_root" --no-cache build --wfail \
  'Grassmann.CABI.Kernels:o.export' \
  'Grassmann.CABI.ScenePack:o.export' \
  'Grassmann.CABI.Studio:o.export' \
  'Grassmann.CABI:o.export'

objs=(
  "$repo_root/.lake/build/ir/Grassmann/CABI/Kernels.c.o.export"
  "$repo_root/.lake/build/ir/Grassmann/CABI/ScenePack.c.o.export"
  "$repo_root/.lake/build/ir/Grassmann/CABI/Studio.c.o.export"
  "$repo_root/.lake/build/ir/Grassmann/CABI.c.o.export"
)
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

# Build static archive (for SwiftPM / visionOS / Xcode embedding)
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

echo "[cabi] building and running C11 smoke test + benchmark"
cc -std=c11 -O2 -Wall -Wextra -Werror \
  -I"$repo_root/include" \
  "$repo_root/c/cabi_smoke.c" \
  -L"$out_dir" -lgrassmann_cabi -lm \
  -Wl,-rpath,"$out_dir" \
  -o "$out_dir/cabi_smoke"

"$out_dir/cabi_smoke"
