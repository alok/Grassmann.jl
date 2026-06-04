#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg_root="$(cd "$script_dir/.." && pwd)"
repo_root="$(cd "$pkg_root/.." && pwd)"

for tool in lake curl rsvg-convert magick rg; do
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
julia_docs="$repo_root/docs/src/algebra.md"
minimum_frame_stddev=1200
maximum_rmse_normalized=0.25

contains_name() {
  local needle="$1"
  shift
  for candidate in "$@"; do
    if [[ "$candidate" == "$needle" ]]; then
      return 0
    fi
  done
  return 1
}

numeric_ge() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual >= expected ? 0 : 1) }'
}

numeric_le() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual <= expected ? 0 : 1) }'
}

failures=()

for ((i = 0; i < ${#names[@]}; i++)); do
  for ((j = i + 1; j < ${#names[@]}; j++)); do
    if [[ "${names[$i]}" == "${names[$j]}" ]]; then
      failures+=("duplicate expected example name: ${names[$i]}")
    fi
  done
done

if [[ ! -s "$julia_docs" ]]; then
  failures+=("missing Julia docs source: $julia_docs")
else
  doc_names=()
  while IFS= read -r name; do
    doc_names+=("$name")
  done < <(
    rg -o 'paper/img/[A-Za-z0-9_-]+\.png' "$julia_docs" |
      while IFS= read -r path; do
        base="${path##*/}"
        printf '%s\n' "${base%.png}"
      done |
      sort -u
  )
  for name in "${doc_names[@]}"; do
    if ! contains_name "$name" "${names[@]}"; then
      failures+=("docs/src/algebra.md references an untested plot example: $name")
    fi
  done
  for name in "${names[@]}"; do
    if ! contains_name "$name" "${doc_names[@]}"; then
      failures+=("expected example is not referenced by docs/src/algebra.md: $name")
    fi
  done
fi

cd "$pkg_root"
rm -rf "$out_root/lean" "$out_root/index.html" "$out_root/manifest.json"
lake exe jlexamples

rm -rf "$work_dir"
mkdir -p "$work_dir"
printf 'name\tlean_stddev\tjulia_stddev\trmse_normalized\trmse_diagnostic\n' > "$metrics"

manifest="$out_root/manifest.json"
if [[ ! -s "$manifest" ]]; then
  failures+=("missing generated manifest: $manifest")
else
  manifest_body="$(< "$manifest")"
  for name in "${names[@]}"; do
    if [[ "$manifest_body" != *"\"name\":\"$name\""* ]]; then
      failures+=("manifest missing expected example: $name")
    fi
  done
fi

shopt -s nullglob
generated_svgs=("$out_root/lean"/*.svg)
shopt -u nullglob
if [[ ${#generated_svgs[@]} -ne ${#names[@]} ]]; then
  failures+=("expected ${#names[@]} generated Lean SVGs, found ${#generated_svgs[@]}")
fi

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
  rmse_normalized="$(printf '%s\n' "$rmse" | awk -F '[()]' '{print $2}')"
  printf '%s\t%s\t%s\t%s\t%s\n' "$name" "$lean_stddev" "$julia_stddev" "$rmse_normalized" "$rmse" >> "$metrics"

  if ! numeric_ge "$lean_stddev" "$minimum_frame_stddev"; then
    failures+=("$name Lean frame standard deviation $lean_stddev below $minimum_frame_stddev")
  fi
  if ! numeric_ge "$julia_stddev" "$minimum_frame_stddev"; then
    failures+=("$name Julia frame standard deviation $julia_stddev below $minimum_frame_stddev")
  fi
  if [[ -z "$rmse_normalized" ]]; then
    failures+=("$name RMSE diagnostic did not include a normalized value: $rmse")
  elif ! numeric_le "$rmse_normalized" "$maximum_rmse_normalized"; then
    failures+=("$name normalized RMSE $rmse_normalized above $maximum_rmse_normalized")
  fi

  pair_paths+=("$pair")
done

contact="$work_dir/contact.png"
magick "${pair_paths[@]}" -append "$contact"

if [[ ${#failures[@]} -ne 0 ]]; then
  printf 'visual comparison smoke checks failed:\n' >&2
  for failure in "${failures[@]}"; do
    printf '  - %s\n' "$failure" >&2
  done
  exit 1
fi

printf 'wrote visual comparison contact sheet to %s\n' "$contact"
printf 'wrote diagnostic image metrics to %s\n' "$metrics"
printf 'visual smoke checks passed: %s examples, frame stddev >= %s, normalized RMSE <= %s\n' \
  "${#names[@]}" "$minimum_frame_stddev" "$maximum_rmse_normalized"
