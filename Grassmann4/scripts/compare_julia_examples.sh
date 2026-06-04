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
metrics="$work_dir/metrics.tsv"

cd "$pkg_root"
lake exe jlexamples

rm -rf "$work_dir"
mkdir -p "$work_dir"
printf 'name\tlean_stddev\tjulia_stddev\trmse_diagnostic\n' > "$metrics"

pair_paths=()
for name in "${names[@]}"; do
  lean_svg="$out_root/lean/$name.svg"
  lean_png="$work_dir/$name-lean.png"
  julia_png="$work_dir/$name-julia.png"
  lean_frame="$work_dir/$name-lean-frame.png"
  julia_frame="$work_dir/$name-julia-frame.png"
  pair_body="$work_dir/$name-pair-body.png"
  pair_label_svg="$work_dir/$name-pair-label.svg"
  pair_label="$work_dir/$name-pair-label.png"
  pair="$work_dir/$name-pair.png"

  if [[ ! -f "$lean_svg" ]]; then
    printf 'missing generated Lean SVG: %s\n' "$lean_svg" >&2
    exit 1
  fi

  rsvg-convert "$lean_svg" > "$lean_png"
  curl -fsSL "$reference_base/$name.png" -o "$julia_png"

  magick "$lean_png" -resize 620x440 -background white -gravity center -extent 620x440 "$lean_frame"
  magick "$julia_png" -resize 620x440 -background white -gravity center -extent 620x440 "$julia_frame"
  magick "$lean_frame" "$julia_frame" +append "$pair_body"
  cat > "$pair_label_svg" <<SVG
<svg xmlns="http://www.w3.org/2000/svg" width="1240" height="44" viewBox="0 0 1240 44">
  <rect width="1240" height="44" fill="#ffffff"/>
  <text x="620" y="28" text-anchor="middle" font-family="Arial, Helvetica, sans-serif" font-size="22" fill="#222222">$name: Lean SVG left / Julia-Makie PNG right</text>
</svg>
SVG
  rsvg-convert "$pair_label_svg" -o "$pair_label"
  magick "$pair_label" "$pair_body" -append "$pair"

  lean_stddev="$(magick "$lean_frame" -colorspace Gray -format '%[standard-deviation]' info:)"
  julia_stddev="$(magick "$julia_frame" -colorspace Gray -format '%[standard-deviation]' info:)"
  rmse="$(magick compare -metric RMSE "$lean_frame" "$julia_frame" null: 2>&1 || true)"
  printf '%s\t%s\t%s\t%s\n' "$name" "$lean_stddev" "$julia_stddev" "$rmse" >> "$metrics"

  pair_paths+=("$pair")
done

contact="$work_dir/contact.png"
magick "${pair_paths[@]}" -append "$contact"

printf 'wrote visual comparison contact sheet to %s\n' "$contact"
printf 'wrote diagnostic image metrics to %s\n' "$metrics"
