#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg_root="$(cd "$script_dir/.." && pwd)"

for tool in lake curl rsvg-convert magick; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$tool" >&2
    exit 1
  fi
done

names=(
  plane-1 plane-2 plane-3 plane-4 plane-5 plane-6
  torus helix orbit-2 orbit-4 orb wave
)

reference_base="https://raw.githubusercontent.com/chakravala/Grassmann.jl/master/paper/img"
out_root="$pkg_root/.generated/julia-examples"
work_dir="$out_root/contact-sheet"

cd "$pkg_root"
lake exe jlexamples

rm -rf "$work_dir"
mkdir -p "$work_dir"

pair_paths=()
for name in "${names[@]}"; do
  lean_svg="$out_root/lean/$name.svg"
  lean_png="$work_dir/$name-lean.png"
  julia_png="$work_dir/$name-julia.png"
  lean_frame="$work_dir/$name-lean-frame.png"
  julia_frame="$work_dir/$name-julia-frame.png"
  pair="$work_dir/$name-pair.png"

  if [[ ! -f "$lean_svg" ]]; then
    printf 'missing generated Lean SVG: %s\n' "$lean_svg" >&2
    exit 1
  fi

  rsvg-convert "$lean_svg" > "$lean_png"
  curl -fsSL "$reference_base/$name.png" -o "$julia_png"

  magick "$lean_png" -resize 620x440 -background white -gravity center -extent 620x440 "$lean_frame"
  magick "$julia_png" -resize 620x440 -background white -gravity center -extent 620x440 "$julia_frame"
  magick "$lean_frame" "$julia_frame" +append "$pair"

  pair_paths+=("$pair")
done

contact="$work_dir/contact.png"
magick "${pair_paths[@]}" -append "$contact"

printf 'wrote visual comparison contact sheet to %s\n' "$contact"
