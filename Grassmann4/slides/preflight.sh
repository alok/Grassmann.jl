#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
cd "$script_dir"

"$script_dir/build-site.sh"

test -s _site/index.html
test -s _site/slides/index.html
test -s _site/slides/sflean-talk.css
test -d _site/slides/lib
test -s _site/follow-along.svg
test -s _site/demo/app.js
test -s _site/demo/scene.json
test -s _site/demo/fallback.svg
test -s _site/tutorial/index.html
test -s _site/cue-card/index.html

if rg -n '<(?:script|link)[^>]+(?:src|href)="https?://' _site --glob '*.html'; then
  echo "generated site loads an external script or stylesheet" >&2
  exit 1
fi

if rg -n '<img[^>]+src="https?://' _site --glob '*.html'; then
  echo "generated site loads an external image" >&2
  exit 1
fi

jq -e '.schemaVersion == 2 and (.frames | length) == 24 and (.frames[0].samples | length) == 25' \
  _site/demo/scene.json >/dev/null

if command -v xmllint >/dev/null 2>&1; then
  xmllint --noout _site/demo/fallback.svg
fi

echo "PASS: deck, site, Lean-generated demo, tutorial, and fallback are offline and stage-ready"
