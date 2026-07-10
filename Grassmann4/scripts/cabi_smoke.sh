#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
grassmann4_dir="$(cd "$script_dir/.." && pwd)"
outer_dir="$(cd "$grassmann4_dir/.." && pwd)"

# Prefer the authoritative outer package, while allowing an explicit override.
if [[ -n "${GRASSMANN_LAKE_ROOT:-}" ]]; then
  lake_root="$(cd "$GRASSMANN_LAKE_ROOT" && pwd)"
elif [[ -f "$outer_dir/lakefile.toml" || -f "$outer_dir/lakefile.lean" ]]; then
  lake_root="$outer_dir"
else
  lake_root="$grassmann4_dir"
fi

lake_cmd=(lake --dir "$lake_root")
lean_sysroot="$("${lake_cmd[@]}" env lean --print-prefix)"
lean_libdir="$lean_sysroot/lib/lean"
output_dir="${GRASSMANN_CABI_OUT:-$lake_root/.lake/build/cabi}"
include_dir="$grassmann4_dir/include"
c_dir="$grassmann4_dir/c"

mkdir -p "$output_dir"

case "$(uname -s)" in
  Darwin)
    shared_ext="dylib"
    wrapper_link_args=(
      -dynamiclib
      "-Wl,-install_name,@rpath/libgrassmann_cabi.dylib"
    )
    runtime_env_var="DYLD_LIBRARY_PATH"
    ;;
  Linux)
    shared_ext="so"
    wrapper_link_args=(
      -shared
      "-Wl,-soname,libgrassmann_cabi.so"
    )
    runtime_env_var="LD_LIBRARY_PATH"
    ;;
  *)
    echo "unsupported platform: $(uname -s)" >&2
    exit 2
    ;;
esac

kernel_object="$lake_root/.lake/build/ir/Grassmann/PGA3Kernel.c.o.export"
cabi_object="$lake_root/.lake/build/ir/Grassmann/CABI.c.o.export"
wrapper_shared="$output_dir/libgrassmann_cabi.$shared_ext"
smoke_bin="$output_dir/cabi_smoke"

echo "[cabi] package root: $lake_root"
echo "[cabi] checking Lean boundary and C/C++ headers"
# The linker consumes these exact local object facets. Lake's shared artifact
# cache can replay only their trace metadata after a clean build, so disable it
# here instead of accepting a successful fetch with no object on disk.
LAKE_CACHE_DIR='' lake --dir "$lake_root" --no-cache build \
  'Grassmann.PGA3Kernel:o.export' \
  'Grassmann.CABI:o.export'

cc -std=c11 -Wall -Wextra -Werror -fsyntax-only \
  -I"$lean_sysroot/include" \
  -I"$include_dir" \
  "$c_dir/grassmann_cabi.c"

c++ -std=c++17 -Wall -Wextra -Werror -fsyntax-only \
  -I"$include_dir" \
  "$c_dir/cabi_header_probe.cpp"

for object in "$kernel_object" "$cabi_object"; do
  if [[ ! -f "$object" ]]; then
    echo "expected C ABI object is missing: $object" >&2
    exit 1
  fi
done

echo "[cabi] linking public wrapper library"
cc -std=c11 -O3 -DNDEBUG -fPIC \
  "${wrapper_link_args[@]}" \
  -I"$lean_sysroot/include" \
  -I"$include_dir" \
  "$c_dir/grassmann_cabi.c" \
  "$kernel_object" \
  "$cabi_object" \
  -L"$lean_libdir" \
  -lInit_shared -lleanshared_2 -lleanshared_1 -lleanshared \
  -lm \
  -Wl,-rpath,"$lean_libdir" \
  -o "$wrapper_shared"

echo "[cabi] linking C consumer smoke test"
cc -std=c11 -O2 -Wall -Wextra -Werror \
  -pthread \
  -I"$include_dir" \
  "$c_dir/cabi_smoke.c" \
  -L"$output_dir" -lgrassmann_cabi \
  -lm \
  -Wl,-rpath,"$output_dir" \
  -Wl,-rpath,"$lean_libdir" \
  -o "$smoke_bin"

echo "[cabi] checking exported public symbols"
expected_symbols=(
  grassmann_cabi_version_v1
  grassmann_initialize_v1
  grassmann_thread_initialize_v1
  grassmann_thread_finalize_v1
  grassmann_pga3_make_point_v1
  grassmann_pga3_extract_point_v1
  grassmann_pga3_make_rotor_v1
  grassmann_pga3_make_translator_v1
  grassmann_pga3_motor_compose_v1
  grassmann_pga3_motor_reverse_v1
  grassmann_pga3_motor_is_unit_v1
  grassmann_pga3_motor_normalize_v1
  grassmann_pga3_motor_inverse_v1
  grassmann_pga3_motor_apply_point_v1
  grassmann_pga3_motor_apply_xyz_batch_v1
)
symbol_dump="$(nm -g "$wrapper_shared")"
for symbol in "${expected_symbols[@]}"; do
  if ! rg -q "(^|[[:space:]_])${symbol}$" <<<"$symbol_dump"; then
    echo "expected public symbol is missing: $symbol" >&2
    exit 1
  fi
done

echo "[cabi] running foreign consumer"
runtime_paths="$output_dir:$lean_libdir"
if [[ "$runtime_env_var" == "DYLD_LIBRARY_PATH" ]]; then
  DYLD_LIBRARY_PATH="$runtime_paths:${DYLD_LIBRARY_PATH:-}" \
    "$smoke_bin"
else
  LD_LIBRARY_PATH="$runtime_paths:${LD_LIBRARY_PATH:-}" \
    "$smoke_bin"
fi
