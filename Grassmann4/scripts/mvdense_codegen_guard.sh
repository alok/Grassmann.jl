#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
grassmann4_dir="$(cd "$script_dir/.." && pwd)"
outer_dir="$(cd "$grassmann4_dir/.." && pwd)"

# The outer Lake package is authoritative. Allow an explicit root only for
# callers embedding Grassmann4 in another checkout.
if [[ -n "${GRASSMANN_LAKE_ROOT:-}" ]]; then
  lake_root="$(cd "$GRASSMANN_LAKE_ROOT" && pwd)"
elif [[ -f "$outer_dir/lakefile.toml" || -f "$outer_dir/lakefile.lean" ]]; then
  lake_root="$outer_dir"
else
  lake_root="$grassmann4_dir"
fi

for tool in lake awk rg; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$tool" >&2
    exit 1
  fi
done

# A normal build is allowed to reuse the shared artifact cache without
# materializing C. Explicitly request the C facet with that cache disabled so
# this guard always witnesses code generated from the current source tree.
LAKE_CACHE_DIR='' lake --dir "$lake_root" --no-cache build +Grassmann.MVDense:c

if [[ -n "${MVDENSE_C_FILE:-}" ]]; then
  c_file="$MVDENSE_C_FILE"
elif [[ -s "$lake_root/.lake/build/ir/Grassmann/MVDense.c" ]]; then
  c_file="$lake_root/.lake/build/ir/Grassmann/MVDense.c"
else
  # Ask Lake for the artifact selected by this exact target. Depending on the
  # Lake version, a freshly built C facet may live in the local build tree or
  # in Lake's content-addressed artifact store.
  candidates="$({
    lake --dir "$lake_root" query +Grassmann.MVDense:c |
      rg '^/.*[.]c$'
  } || true)"
  candidate_count="$(
    printf '%s\n' "$candidates" |
      awk 'NF { count++ } END { print count + 0 }'
  )"
  if [[ "$candidate_count" != 1 ]]; then
    printf 'expected Lake to select exactly one generated MVDense.c, found %s\n' \
      "$candidate_count" >&2
    printf '%s\n' "$candidates" >&2
    exit 1
  fi
  c_file="$(printf '%s\n' "$candidates" | awk 'NF { print; exit }')"
fi

if [[ ! -s "$c_file" ]]; then
  printf 'generated MVDense C file is missing or empty: %s\n' "$c_file" >&2
  exit 1
fi

if ! rg -q '^// Module: Grassmann[.]MVDense$' "$c_file"; then
  printf 'Lake-selected C artifact is not Grassmann.MVDense: %s\n' \
    "$c_file" >&2
  exit 1
fi

printf 'Inspecting freshly generated C: %s\n' "$c_file"

# Extract one complete generated-C definition using brace depth. Definition
# patterns end at `{`, excluding the forward declarations near the file top.
extract_body() {
  local pattern="$1"

  awk -v pattern="$pattern" '
    !inside && $0 ~ pattern { inside = 1 }

    inside {
      print

      line = $0
      opens = gsub(/[{]/, "{", line)
      line = $0
      closes = gsub(/[}]/, "}", line)

      depth += opens - closes
      if (depth == 0) exit
    }
  ' "$c_file"
}

definition_count() {
  local pattern="$1"

  awk -v pattern="$pattern" '
    $0 ~ pattern { count++ }
    END { print count + 0 }
  ' "$c_file"
}

# Extract the braced statement immediately following a marker from an already
# extracted function. This lets public full and packed branches be checked
# independently, rather than merely counting two mutually exclusive buffers.
extract_braced_after() {
  local body="$1"
  local marker="$2"

  printf '%s\n' "$body" |
    awk -v marker="$marker" '
      !seen && $0 ~ marker {
        seen = 1
        next
      }

      seen && !inside {
        if ($0 ~ /^[[:space:]]*[{][[:space:]]*$/) {
          inside = 1
        } else {
          next
        }
      }

      inside {
        print

        line = $0
        opens = gsub(/[{]/, "{", line)
        line = $0
        closes = gsub(/[}]/, "}", line)

        depth += opens - closes
        if (depth == 0) exit
      }
    '
}

count_fixed() {
  local body="$1"
  local needle="$2"

  printf '%s\n' "$body" |
    awk -v needle="$needle" '
      {
        line = $0
        while ((at = index(line, needle)) != 0) {
          count++
          line = substr(line, at + length(needle))
        }
      }
      END { print count + 0 }
    '
}

require_count() {
  local label="$1"
  local body="$2"
  local needle="$3"
  local expected="$4"
  local got

  got="$(count_fixed "$body" "$needle")"
  if [[ "$got" != "$expected" ]]; then
    printf 'FAIL %s: expected %s occurrences of %s, got %s\n' \
      "$label" "$expected" "$needle" "$got" >&2
    exit 1
  fi
}

require_regex_count() {
  local label="$1"
  local body="$2"
  local pattern="$3"
  local expected="$4"
  local got

  got="$(
    printf '%s\n' "$body" |
      awk -v pattern="$pattern" '
        $0 ~ pattern { count++ }
        END { print count + 0 }
      '
  )"
  if [[ "$got" != "$expected" ]]; then
    printf 'FAIL %s: expected %s lines matching %s, got %s\n' \
      "$label" "$expected" "$pattern" "$got" >&2
    exit 1
  fi
}

forbid() {
  local label="$1"
  local body="$2"
  local pattern="$3"

  if printf '%s\n' "$body" | rg -q "$pattern"; then
    printf 'FAIL %s: forbidden generated-C pattern: %s\n' \
      "$label" "$pattern" >&2
    exit 1
  fi
}

require_call_result_return() {
  local label="$1"
  local body="$2"
  local call="$3"
  local assigned

  assigned="$(
    printf '%s\n' "$body" |
      awk -v call="$call" '
        index($0, call) != 0 {
          line = $0
          gsub(/[[:space:]]/, "", line)
          sub(/=.*/, "", line)
          print line
          exit
        }
      '
  )"

  if [[ -z "$assigned" ]] ||
      ! printf '%s\n' "$body" | rg -F -q "return $assigned;"; then
    printf 'FAIL %s: result of %s is not returned directly\n' \
      "$label" "$call" >&2
    exit 1
  fi
}

# Private declaration ordinals are intentionally ignored. The reduced-argument
# clones contain the actual tail loops; the non-reduced helpers are wrappers.
full_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_ofMultivectorFullAux___redArg[(][^;]*[)] [{]$'
packed_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_ofMultivectorPackedAux___redArg[(][^;]*[)] [{]$'

for definition in "$full_re" "$packed_re"; do
  if [[ "$(definition_count "$definition")" != 1 ]]; then
    printf 'FAIL dense ingress: expected exactly one helper definition matching %s\n' \
      "$definition" >&2
    exit 1
  fi
done

full="$(extract_body "$full_re")"
packed="$(extract_body "$packed_re")"

# Full ingress is identity-indexed: one dense callback and one push per
# iteration, with no rank decoding, bounds rechecks, or intermediate arrays.
require_count 'full ingress helper' "$full" lean_apply_1 1
require_regex_count 'full ingress helper callbacks' "$full" 'lean_apply_[0-9]+' 1
require_count 'full ingress helper' "$full" lean_float_array_push 1
require_count 'full ingress helper' "$full" 'goto _start;' 1
require_count 'full ingress helper' "$full" lean_nat_dec_eq 1
require_count 'full ingress helper' "$full" lean_nat_sub 1
require_count 'full ingress helper' "$full" lean_nat_add 1
forbid 'full ingress helper' "$full" \
  'lean_alloc_|lean_box|lean_mk_empty_float_array|lean_nat_(pow|dec_lt|dec_le|mod|lxor)|popcount|lean_float_array_(get|set|size|data)|lean_array_|l_Array_range|Array_(map|mapM|fold|range)|DataArray|computeIndices|__Grassmann_MV_(unpackIdx|packIdx)[(]'
printf 'PASS full dense ingress is an identity-indexed one-buffer tail loop\n'

# Packed ingress performs rank-to-mask arithmetic inline. Two equality checks
# are intentional: loop termination and the explicit n = 0 compatibility path
# that keeps odd scalar storage valid.
require_count 'packed ingress helper' "$packed" lean_apply_1 1
require_regex_count 'packed ingress helper callbacks' "$packed" 'lean_apply_[0-9]+' 1
require_count 'packed ingress helper' "$packed" lean_float_array_push 1
require_count 'packed ingress helper' "$packed" 'goto _start;' 1
require_count 'packed ingress helper' "$packed" lp_Grassmann_Grassmann_popcount 1
require_count 'packed ingress helper' "$packed" lean_nat_dec_eq 2
require_regex_count 'packed ingress n=0 compatibility' "$packed" \
  'lean_nat_dec_eq[(]x_1,' 1
require_count 'packed ingress helper' "$packed" lean_nat_sub 1
require_count 'packed ingress helper' "$packed" lean_nat_add 4
require_count 'packed ingress helper' "$packed" lean_nat_mod 2
require_count 'packed ingress helper' "$packed" lean_nat_lxor 1
forbid 'packed ingress helper' "$packed" \
  'lean_alloc_|lean_box|lean_mk_empty_float_array|lean_nat_(pow|dec_lt|dec_le)|lean_float_array_(get|set|size|data)|lean_array_|l_Array_range|Array_(map|mapM|fold|range)|DataArray|computeIndices|__Grassmann_MV_(indices|unpackIdx|packIdx)[(]'
printf 'PASS packed dense ingress is an arithmetic one-buffer tail loop with n=0 compatibility\n'

# Check both the exported declaration and the reduced-argument clone because
# either may be selected by downstream generated code.
for suffix in '' '___redArg'; do
  label="ofMultivector${suffix}"
  public_re="^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_${label}[(][^;]*[)] [{]$"

  if [[ "$(definition_count "$public_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one public definition\n' "$label" >&2
    exit 1
  fi

  public="$(extract_body "$public_re")"
  full_branch="$(extract_braced_after "$public" \
    '^[[:space:]]*if [(]x_[0-9]+ == 2[)][[:space:]]*$')"
  packed_branch="$(extract_braced_after "$public" \
    '^[[:space:]]*else[[:space:]]*$')"

  if [[ -z "$full_branch" || -z "$packed_branch" ]]; then
    printf 'FAIL %s: could not extract full and packed public branches\n' \
      "$label" >&2
    exit 1
  fi

  require_count "$label full branch" "$full_branch" lean_mk_empty_float_array 1
  require_count "$label full branch" "$full_branch" \
    '__Grassmann_MV_ofMultivectorFullAux___redArg(' 1
  require_count "$label full branch" "$full_branch" \
    '__Grassmann_MV_ofMultivectorPackedAux___redArg(' 0
  require_count "$label full branch" "$full_branch" lean_nat_pow 1
  require_count "$label full branch" "$full_branch" lean_nat_sub 0
  require_count "$label full branch" "$full_branch" return 1
  require_call_result_return "$label full branch" "$full_branch" \
    '__Grassmann_MV_ofMultivectorFullAux___redArg('

  require_count "$label packed branch" "$packed_branch" lean_mk_empty_float_array 1
  require_count "$label packed branch" "$packed_branch" \
    '__Grassmann_MV_ofMultivectorPackedAux___redArg(' 1
  require_count "$label packed branch" "$packed_branch" \
    '__Grassmann_MV_ofMultivectorFullAux___redArg(' 0
  require_count "$label packed branch" "$packed_branch" lean_nat_pow 1
  require_count "$label packed branch" "$packed_branch" lean_nat_sub 1
  require_count "$label packed branch" "$packed_branch" return 1
  require_call_result_return "$label packed branch" "$packed_branch" \
    '__Grassmann_MV_ofMultivectorPackedAux___redArg('

  # No range/map/copy ingress, callback application in the wrapper, duplicate
  # size validation, Option/fallback construction, or borrowed-input RC churn.
  forbid "$label public" "$public" \
    'l_Array_range|Array_(map|mapM|fold|range)|lean_array_|DataArray_(ofArray|replicate)|ofDataArray|lean_float_array_(get|push|set|size|data)|FloatArray_(size|data)|lean_alloc_(closure|ctor)|lean_apply_|lean_box|lean_nat_dec_eq|lean_(inc|dec)_ref'

  printf 'PASS %s allocates one native buffer in each selected branch and returns its helper directly\n' \
    "$label"
done

printf 'PASS dense ingress generated-C guard\n'
