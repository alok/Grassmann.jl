#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
grassmann4_dir="$(cd "$script_dir/.." && pwd)"
outer_dir="$(cd "$grassmann4_dir/.." && pwd)"

# Prefer the authoritative outer package, while allowing an explicit override.
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

lake_cmd=(lake --dir "$lake_root")
"${lake_cmd[@]}" build Grassmann.MV

c_file="${MV_C_FILE:-$lake_root/.lake/build/ir/Grassmann/MV.c}"
if [[ ! -s "$c_file" ]]; then
  printf 'generated MV C file is missing or empty: %s\n' "$c_file" >&2
  exit 1
fi

# Extract one complete generated-C function using brace depth. Definition
# patterns end at `{`, so forward declarations ending in `;` are excluded.
extract_body() {
  local pattern="$1"

  awk -v pattern="$pattern" '
    !inside && $0 ~ pattern { inside = 1 }

    inside {
      print

      line = $0
      opens = gsub(/[\{]/, "{", line)

      line = $0
      closes = gsub(/[\}]/, "}", line)

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

# Count literal substrings without relying on rg's nonzero no-match exit.
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

ops=(smul add sub neg)
arith=(lean_float_mul lean_float_add lean_float_sub lean_float_negate)
gets=(1 2 2 1)

for ((i = 0; i < ${#ops[@]}; i++)); do
  op="${ops[$i]}"

  # Lean's private declaration ordinal can change when another private
  # declaration is inserted, so match the stable helper suffix instead.
  helper_re="^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_${op}Aux[(][^;]*[)] [\{]$"
  public_re="^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_${op}[(][^;]*[)] [\{]$"

  if [[ "$(definition_count "$helper_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one non-boxed helper definition\n' \
      "$op" >&2
    exit 1
  fi

  if [[ "$(definition_count "$public_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one non-boxed public definition\n' \
      "$op" >&2
    exit 1
  fi

  helper="$(extract_body "$helper_re")"
  public="$(extract_body "$public_re")"

  # Each coefficient loop has only its expected reads, arithmetic, output
  # push, and tail jump.
  require_count "$op helper" "$helper" \
    lean_float_array_get "${gets[$i]}"
  require_count "$op helper" "$helper" \
    "${arith[$i]}" 1
  require_count "$op helper" "$helper" \
    lean_float_array_push 1
  require_count "$op helper" "$helper" \
    'goto _start;' 1

  # Reject callbacks, boxed coefficient collections, result allocation inside
  # the loop, second-pass writes, and borrowed-input reference-count churn.
  forbid "$op helper" "$helper" \
    'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|l_Array_range|Array_(map|fold)|lean_array_|lean_float_array_set|lean_(inc|dec)_ref'

  # The public constructor owns exactly one final result buffer and enters the
  # matching coefficient loop exactly once.
  require_count "$op public" "$public" \
    lean_mk_empty_float_array 1
  require_count "$op public" "$public" \
    "__Grassmann_MV_${op}Aux(" 1

  # Arithmetic and coefficient iteration belong in the helper. This rejects
  # reconstruction of the old closure/range/map/copy path and MV wrappers.
  forbid "$op public" "$public" \
    'lean_alloc_|lean_apply_|lean_box|l_Array_range|Array_(map|fold)|lean_array_|lean_float_array_(get|push|set)'

  printf 'PASS %s generated-C structure\n' "$op"
done

# Scalar multiplication carries its scalar unboxed through the hot loop.
smul_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_smulAux[(][^;]*[)] [\{]$'
smul_helper="$(extract_body "$smul_re")"
require_count 'smul helper ABI' "$smul_helper" 'smulAux(double ' 1

printf 'PASS smul scalar ABI is unboxed double\n'
