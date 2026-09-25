#!/bin/sh
# Fetch prebuilt mathlib .olean files for exactly the mathlib modules the bridge
# imports (and their transitive imports), instead of all of mathlib.
#
# On the first run Lake clones mathlib and its dependencies at the revisions
# pinned in lake-manifest.json and builds mathlib's `cache` tool (about a
# minute); the download itself is ~1,850 files (~120 MB compressed, ~1.8 GB
# unpacked). A plain `lake exe cache get` would fetch all of mathlib instead.
set -eu
cd "$(dirname "$0")"
mods=$(sed -n 's/^import \(Mathlib\.[A-Za-z0-9_.]*\).*/\1/p' GrassmannBridge.lean GrassmannBridge/*.lean \
  BridgeTests.lean BridgeTests/*.lean | sort -u)
# `MATHLIB_NO_CACHE_ON_UPDATE=1` keeps mathlib's post-update hook from fetching the full cache.
# shellcheck disable=SC2086
MATHLIB_NO_CACHE_ON_UPDATE=1 lake exe cache get $mods
