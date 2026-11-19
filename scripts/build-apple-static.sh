#!/usr/bin/env bash
# scripts/build-apple-static.sh
# Cross-compiles the strictly Init-only 25-module Grassmann.CABI + Grassmann.Studio
# C sources into arm64 static libraries (`libgrassmann_cabi.a`) for:
#   - macos-arm64            (-target arm64-apple-macos27.0, -mmacosx-version-min=27.0)
#   - xros-arm64-simulator   (-target arm64-apple-xros2.0-simulator, USE_MIMALLOC=OFF)
#   - xros-arm64             (-target arm64-apple-xros2.0, USE_MIMALLOC=OFF)
# and packages them with headers + module.modulemap into GrassmannCABI.xcframework.
#
# Matches LeanVisionOSRuntime.xcframework (leanprover/lean4:v4.36.0, rev 611c117b).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LEAN_PREFIX="$(lake --dir "$ROOT" env lean --print-prefix)"
OUT_ROOT="$ROOT/.lake/build/apple"
STAGE_ROOT="$ROOT/.lake/build/apple-staging"
VISIONOS_INC="$STAGE_ROOT/include-visionos"
XCFRAMEWORK="$OUT_ROOT/GrassmannCABI.xcframework"
STAGE_XCFW="$STAGE_ROOT/GrassmannCABI.xcframework"
NCPU="$(sysctl -n hw.ncpu 2>/dev/null || echo 4)"

MODULES=(
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

C_TARGETS=()
for m in "${MODULES[@]}"; do
  C_TARGETS+=("${m}:c")
done

echo "[apple] Lean toolchain: $(lean --version)"
echo "[apple] generating ${#MODULES[@]} strictly Init-only Lean 4.36 C sources (--wfail)"
lake build --wfail "${C_TARGETS[@]}"

C_FILES=()
while IFS= read -r line; do
  [[ -n "$line" ]] && C_FILES+=("$line")
done < <(lake query "${C_TARGETS[@]}")

if (( ${#C_FILES[@]} != ${#MODULES[@]} )); then
  echo "ERROR: expected ${#MODULES[@]} C files from lake query, got ${#C_FILES[@]}" >&2
  exit 1
fi

rm -rf "$STAGE_ROOT"
mkdir -p "$VISIONOS_INC/lean"

# visionOS / xrsimulator LeanVisionOSRuntime.xcframework is built with
# -DUSE_MIMALLOC=OFF -DUSE_GMP=OFF (only #define LEAN_IS_STAGE0 0 in config.h).
cat > "$VISIONOS_INC/lean/config.h" << 'EOF'
#pragma once
#include <lean/version.h>
#define LEAN_IS_STAGE0 0
EOF

build_slice() {
  local slice="$1"
  local sdk="$2"
  local target="$3"
  local extra_flags="$4"
  local use_visionos_inc="$5"

  local sdk_path
  sdk_path="$(xcrun --sdk "$sdk" --show-sdk-path)"
  local clang_bin
  clang_bin="$(xcrun --sdk "$sdk" --find clang)"
  local libtool_bin
  libtool_bin="$(xcrun --sdk "$sdk" --find libtool)"

  local obj_dir="$STAGE_ROOT/$slice/obj"
  local archive="$STAGE_ROOT/$slice/libgrassmann_cabi.a"
  mkdir -p "$obj_dir"

  local inc_flags=()
  if [[ "$use_visionos_inc" == "1" ]]; then
    inc_flags+=("-I$VISIONOS_INC")
  fi
  inc_flags+=("-I$LEAN_PREFIX/include" "-I$ROOT/include")

  local base_flags=(
    -target "$target"
    -isysroot "$sdk_path"
    -O3 -ffp-contract=off -DNDEBUG
    -fPIC -fwrapv
    -Wno-unused-command-line-argument
  )
  if [[ -n "$extra_flags" ]]; then
    # shellcheck disable=SC2206
    base_flags+=($extra_flags)
  fi

  echo "[apple] compiling slice $slice ($sdk, $target, jobs=$NCPU)"

  local pids=()
  local objs=()
  local idx=0
  for src in "${C_FILES[@]}" "$ROOT/c/grassmann_cabi.c"; do
    local base
    base="$(printf "%02d_%s" "$idx" "$(basename "$src" .c)")"
    local obj="$obj_dir/${base}.o"
    objs+=("$obj")
    idx=$((idx + 1))

    local warn_flags=(-Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-function -Wno-int-conversion)
    if [[ "$src" == "$ROOT/c/grassmann_cabi.c" ]]; then
      warn_flags=(-std=c11 -Wall -Wextra -Werror)
    fi

    "$clang_bin" "${base_flags[@]}" "${warn_flags[@]}" "${inc_flags[@]}" -c "$src" -o "$obj" &
    pids+=($!)
    if (( ${#pids[@]} >= NCPU )); then
      wait "${pids[0]}"
      pids=("${pids[@]:1}")
    fi
  done
  for pid in "${pids[@]}"; do
    wait "$pid"
  done

  "$libtool_bin" -static -o "$archive" "${objs[@]}"
  echo "[apple] archived $archive ($(du -h "$archive" | awk '{print $1}'))"

  # Verify slice architecture & platform metadata via lipo + vtool
  lipo -info "$archive"
  local cabi_obj="$obj_dir/$(printf "%02d_grassmann_cabi.o" "${#C_FILES[@]}")"
  vtool -show-build "$cabi_obj" | rg "platform|minos|sdk"

  # Verify exported C ABI symbols
  local syms
  syms="$(nm -gU "$archive")"
  for req in _grassmann_cabi_version _grassmann_initialize _grassmann_initialize_module \
             _grassmann_attach_thread _grassmann_detach_thread \
             _grassmann_studio_create _grassmann_studio_dispatch_bin _grassmann_studio_dispatch_json \
             _grassmann_studio_get_frame _grassmann_studio_preset_catalog \
             _grassmann_pga3_motor_compose _grassmann_sta_mul _grassmann_r3_apply_rational_rotor; do
    if ! printf "%s\n" "$syms" | rg -q "${req}\$"; then
      echo "ERROR: missing required exported symbol $req in $archive" >&2
      exit 1
    fi
  done

  # Verify strict Init-only purity (zero Lean.* / Std.* / Lake.* module initializers)
  local bad_undef
  bad_undef="$(nm -u "$archive" | rg '^(.* )?(_?initialize_(Lean|Std|Lake)(_|$)|_?lp_(Lean|Std|Lake)_)' || true)"
  if [[ -n "$bad_undef" ]]; then
    echo "ERROR: non-Init compiler/Std undefined module initializers in $archive:" >&2
    printf "%s\n" "$bad_undef" >&2
    exit 1
  fi

  # For visionOS / xrsimulator, verify zero mimalloc / GMP references
  if [[ "$use_visionos_inc" == "1" ]]; then
    local bad_rt
    bad_rt="$(nm -u "$archive" | rg '(_mi_|_lean_alloc_small_object_core|___gmpz_)' || true)"
    if [[ -n "$bad_rt" ]]; then
      echo "ERROR: mimalloc/GMP undefined symbols in visionOS slice $archive:" >&2
      printf "%s\n" "$bad_rt" >&2
      exit 1
    fi
  fi
}

build_slice "macos-arm64"          "macosx"      "arm64-apple-macos27.0"           "-mmacosx-version-min=27.0" 0
build_slice "xros-arm64-simulator" "xrsimulator" "arm64-apple-xros2.0-simulator"   ""                          1
build_slice "xros-arm64"           "xros"        "arm64-apple-xros2.0"             ""                          1

echo "[apple] packaging GrassmannCABI.xcframework"
xcodebuild -create-xcframework \
  -library "$STAGE_ROOT/macos-arm64/libgrassmann_cabi.a"          -headers "$ROOT/include" \
  -library "$STAGE_ROOT/xros-arm64-simulator/libgrassmann_cabi.a" -headers "$ROOT/include" \
  -library "$STAGE_ROOT/xros-arm64/libgrassmann_cabi.a"           -headers "$ROOT/include" \
  -output "$STAGE_XCFW" >/dev/null

# Optional real-world link check against LeanVisionOSRuntime.xcframework (all 3 slices!)
RUNTIME_XCFW="${LEAN_VISIONOS_RUNTIME_XCFW:-/Users/alokbeniwal/LeanVisionOS/build/LeanVisionOSRuntime.xcframework}"
if [[ -d "$RUNTIME_XCFW" ]]; then
  echo "[apple] running live 3-platform link verification against $RUNTIME_XCFW"
  SMOKE_C="$STAGE_ROOT/apple_link_smoke.cpp"
  cat > "$SMOKE_C" << 'EOF'
#include <cassert>
#include <cstdio>
#include <cstring>
#include "grassmann/cabi.h"

int main() {
  assert(grassmann_initialize() == GSIR_OK);
  uint64_t sid = grassmann_studio_create();
  assert(sid > 0);
  uint32_t catLen = 0;
  static char catBuf[65536];
  assert(grassmann_studio_preset_catalog(catBuf, sizeof(catBuf), &catLen) == GSIR_OK);
  assert(catLen > 10000);
  static uint8_t frameBuf[262144];
  uint32_t frameLen = 0;
  assert(grassmann_studio_get_frame(sid, frameBuf, sizeof(frameBuf), &frameLen) == GSIR_OK);
  assert(frameLen >= 100000);
  assert(frameBuf[0] == 'G' && frameBuf[1] == 'S' && frameBuf[2] == 'I' && frameBuf[3] == 'R');
  grassmann_studio_destroy(sid);
  std::printf("[apple smoke] linked & executed against LeanVisionOSRuntime OK (frame=%u B, catalog=%u B)\n",
              frameLen, catLen);
  return 0;
}
EOF

  for entry in \
    "macos-arm64:macosx:arm64-apple-macos27.0:-mmacosx-version-min=27.0" \
    "xros-arm64-simulator:xrsimulator:arm64-apple-xros2.0-simulator:" \
    "xros-arm64:xros:arm64-apple-xros2.0:"; do
    IFS=: read -r slice sdk target extra <<< "$entry"
    rt_lib="$RUNTIME_XCFW/$slice/libCLeanVisionOS.a"
    sdk_path="$(xcrun --sdk "$sdk" --show-sdk-path)"
    clangxx="$(xcrun --sdk "$sdk" --find clang++)"
    bin="$STAGE_ROOT/$slice/apple_link_smoke"
    extra_arr=()
    if [[ -n "$extra" ]]; then
      # shellcheck disable=SC2206
      extra_arr+=($extra)
    fi
    "$clangxx" -target "$target" "${extra_arr[@]}" -isysroot "$sdk_path" \
      -I"$ROOT/include" "$SMOKE_C" \
      "$STAGE_ROOT/$slice/libgrassmann_cabi.a" \
      "$rt_lib" \
      -lz -o "$bin"
    echo "[apple] LINK PASS ($slice): $(du -h "$bin" | awk '{print $1}')"
    if [[ "$slice" == "macos-arm64" ]]; then
      "$bin"
    fi
  done
  rm -f "$SMOKE_C"
fi

# Atomically publish verified artifacts to .lake/build/apple
rm -rf "${OUT_ROOT}.old"
if [[ -d "$OUT_ROOT" ]]; then
  mv "$OUT_ROOT" "${OUT_ROOT}.old"
fi
mv "$STAGE_ROOT" "$OUT_ROOT"
rm -rf "${OUT_ROOT}.old"

ls -lh "$OUT_ROOT"/*/libgrassmann_cabi.a
echo "[apple] XCFramework published: $XCFRAMEWORK"

echo "[apple] ALL 3 APPLE SLICES + XCFRAMEWORK VERIFIED PASS!"
