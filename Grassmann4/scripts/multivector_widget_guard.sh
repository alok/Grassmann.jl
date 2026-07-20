#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
package_root=$(cd "$script_dir/.." && pwd -P)
renderer="$package_root/GrassmannViz/multivectorField.js"

node --check "$renderer"

forbidden='https?://|//[[:alnum:]][^[:space:]]*\.(com|org|net)|\bfetch[[:space:]]*\(|XMLHttpRequest|WebSocket|\beval[[:space:]]*\(|WebGL|\bTHREE\b'
if rg --line-number --regexp "$forbidden" "$renderer"; then
  echo "renderer contains a forbidden online or dynamic-runtime reference" >&2
  exit 1
fi

if rg --line-number --ignore-case --regexp 'ganja|leanplot' "$renderer"; then
  echo "renderer contains a forbidden visualization-runtime reference" >&2
  exit 1
fi

if rg --line-number '^import' "$renderer" |
    rg -v "^[0-9]+:import \\* as React from 'react';$"; then
  echo "renderer imports a module other than the InfoView-provided React runtime" >&2
  exit 1
fi

required_contract=(
  "'data-region'"
  "'data-grade'"
  "'data-glyph'"
  "'data-sample-index'"
  "safeFrameIndex"
  "safeSelectedIndex"
  "frameCount > 1"
  "props.parameterLabel"
  "props.initialSample"
  "event.preventDefault()"
  "vectorMetrics"
  "fitPlanarLattice"
  "onLostPointerCapture"
  "userSelect: 'none'"
)
for token in "${required_contract[@]}"; do
  if ! rg --fixed-strings --quiet "$token" "$renderer"; then
    echo "renderer is missing QA or state-safety contract: $token" >&2
    exit 1
  fi
done

echo "multivector renderer syntax and offline guards passed"
