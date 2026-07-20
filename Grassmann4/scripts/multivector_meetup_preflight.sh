#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
package_root=$(cd "$script_dir/.." && pwd -P)
cd "$package_root"

run() {
  echo
  echo "==> $*"
  "$@"
}

run "$script_dir/multivector_widget_guard.sh"

# The GrassmannViz library declares the embedded JavaScript as a Lake input.
# A source change therefore invalidates the OLean that owns `include_str`.
run env LAKE_ARTIFACT_CACHE=false lake build +GrassmannViz.InfoView

# Materialize local OLeans even when the surrounding developer shell defaults
# to artifact-cache-only builds. These are the same roots selected by Cursor.
run env LAKE_ARTIFACT_CACHE=false lake build \
  Grassmann GrassmannReference GrassmannFields GrassmannViz GrassmannTests

run lake exe multivectorfieldtests
run lake env lean DownstreamLibrarySmoke.lean
run lake env lean MultivectorWidgetCheck.lean
run lake env lean MultivectorFallbackCheck.lean
run lake env lean MultivectorFieldDemo.lean

if command -v xmllint >/dev/null 2>&1; then
  run xmllint --noout docs/MultivectorFieldFallback.svg
fi

run git -C "$package_root/.." diff --check
run git -C "$package_root/.." diff --cached --check

stage_status=$(git -C "$package_root/.." status --short --untracked-files=all -- README.md Grassmann4)
if [[ -n "$stage_status" ]]; then
  echo "$stage_status" >&2
  echo "stage sources are not clean; commit intended work and restore the 5x5 demo" >&2
  exit 1
fi

echo
echo "PASS: multivector field demo is compiled, fresh, offline-guarded, and stage-ready"
echo "Open MultivectorFieldDemo.lean and place the cursor on #html."
