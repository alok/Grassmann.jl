#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
package_root=$(cd "$script_dir/.." && pwd -P)
repo_root=$(cd "$package_root/.." && pwd -P)
output_dir="$script_dir/_site"

command -v bun >/dev/null
command -v lake >/dev/null
command -v pandoc >/dev/null
command -v rsync >/dev/null

cd "$script_dir"
bun install --frozen-lockfile --ignore-scripts
lake build
lake exe sflean-slides

mkdir -p \
  "$output_dir/slides" \
  "$output_dir/demo" \
  "$output_dir/tutorial" \
  "$output_dir/cue-card"

rsync -a --delete "$script_dir/_slides/" "$output_dir/slides/"
cp "$script_dir/site/site.css" "$output_dir/site.css"
cp "$script_dir/site/favicon.svg" "$output_dir/favicon.svg"
cp "$script_dir/site/follow-along.svg" "$output_dir/follow-along.svg"
cp "$script_dir/site/demo/index.html" "$output_dir/demo/index.html"
cp "$package_root/docs/MultivectorFieldFallback.svg" "$output_dir/demo/fallback.svg"

source_commit=$(git -C "$repo_root" rev-parse HEAD)
sed "s/__SOURCE_COMMIT__/$source_commit/g" \
  "$script_dir/site/index.html" > "$output_dir/index.html"

pandoc "$package_root/docs/SFLeanPresenterTutorial.md" \
  --from=gfm \
  --to=html5 \
  --standalone \
  --template="$script_dir/site/page-template.html" \
  --metadata title="Presenter tutorial · Lean's unfair advantage" \
  --metadata page-kind="tutorial" \
  --output="$output_dir/tutorial/index.unversioned.html"
sed "s/__SOURCE_COMMIT__/$source_commit/g" \
  "$output_dir/tutorial/index.unversioned.html" > "$output_dir/tutorial/index.html"

pandoc "$package_root/docs/SFLeanBasicFirstCueCard.md" \
  --from=gfm \
  --to=html5 \
  --standalone \
  --template="$script_dir/site/page-template.html" \
  --metadata title="Speaker cue card · Lean's unfair advantage" \
  --metadata page-kind="cue-card" \
  --output="$output_dir/cue-card/index.unversioned.html"
sed "s/__SOURCE_COMMIT__/$source_commit/g" \
  "$output_dir/cue-card/index.unversioned.html" > "$output_dir/cue-card/index.html"

env NODE_PATH="$script_dir/node_modules" bun build "$script_dir/site/demo/entry.js" \
  --outfile="$output_dir/demo/app.js" \
  --target=browser \
  --minify

(
  cd "$package_root"
  lake exe multivectorscenejson -- "$output_dir/demo/scene.json"
)

rm "$output_dir/tutorial/index.unversioned.html"
rm "$output_dir/cue-card/index.unversioned.html"

test -s "$output_dir/index.html"
test -s "$output_dir/slides/index.html"
test -s "$output_dir/demo/app.js"
test -s "$output_dir/demo/scene.json"
test -s "$output_dir/tutorial/index.html"
test -s "$output_dir/cue-card/index.html"

if rg -n '__SOURCE_COMMIT__' "$output_dir"; then
  echo "site contains an unresolved source-commit placeholder" >&2
  exit 1
fi

echo "site written to $output_dir from source commit $source_commit"
