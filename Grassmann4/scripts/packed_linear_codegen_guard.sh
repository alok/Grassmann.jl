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

# Extract one switch arm from an already-extracted function body while
# respecting nested braces. This pins involute's parity-specific fast paths.
extract_case_body() {
  local body="$1"
  local marker="$2"

  printf '%s\n' "$body" |
    awk -v marker="$marker" '
      !seen && $0 ~ "^[[:space:]]*" marker "[[:space:]]*$" {
        seen = 1
        print
        next
      }

      seen {
        print

        line = $0
        opens = gsub(/[\{]/, "{", line)

        line = $0
        closes = gsub(/[\}]/, "}", line)

        if (opens != 0) inside = 1
        if (inside) {
          depth += opens - closes
          if (depth == 0) exit
        }
      }
    '
}

require_call_result_return() {
  local label="$1"
  local body="$2"
  local call="$3"
  local assigned
  local returned

  assigned="$(
    printf '%s\n' "$body" |
      awk -v call="$call" '
        index($0, call) != 0 {
          line = $0
          gsub(/[[:space:]]/, "", line)
          sub(/=.*/, "", line)
          print line
        }
      '
  )"
  returned="$(
    printf '%s\n' "$body" |
      awk '
        {
          line = $0
          gsub(/[[:space:]]/, "", line)
          if (line ~ /^returnx_[0-9]+;$/) {
            sub(/^return/, "", line)
            sub(/;$/, "", line)
            print line
          }
        }
      '
  )"

  if [[ -z "$assigned" || "$assigned" != "$returned" ]]; then
    printf 'FAIL %s: helper result %s is not returned directly (return=%s)\n' \
      "$label" "$assigned" "$returned" >&2
    exit 1
  fi
}

require_retain_return() {
  local label="$1"
  local body="$2"
  local retained
  local returned

  retained="$(
    printf '%s\n' "$body" |
      awk '
        {
          line = $0
          gsub(/[[:space:]]/, "", line)
          if (line ~ /^lean_inc_ref\(x_[0-9]+\);$/) {
            sub(/^lean_inc_ref\(/, "", line)
            sub(/\);$/, "", line)
            print line
          }
        }
      '
  )"
  returned="$(
    printf '%s\n' "$body" |
      awk '
        {
          line = $0
          gsub(/[[:space:]]/, "", line)
          if (line ~ /^returnx_[0-9]+;$/) {
            sub(/^return/, "", line)
            sub(/;$/, "", line)
            print line
          }
        }
      '
  )"

  if [[ -z "$retained" || "$retained" != "$returned" ]]; then
    printf 'FAIL %s: retained input %s is not returned directly (return=%s)\n' \
      "$label" "$retained" "$returned" >&2
    exit 1
  fi
}

helpers=(
  revFullAux
  revPackedAux
  involuteFullAux
  conjugateFullAux
  conjugatePackedAux
)
packed=(0 1 0 0 1)
nat_subs=(2 2 1 1 1)
nat_adds=(1 1 1 2 2)
nat_muls=(1 1 0 1 1)
nat_shifts=(1 1 0 1 1)

for ((i = 0; i < ${#helpers[@]}; i++)); do
  helper_name="${helpers[$i]}"
  helper_re="^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_${helper_name}[(][^;]*[)] [\{]$"

  if [[ "$(definition_count "$helper_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one non-boxed helper definition\n' \
      "$helper_name" >&2
    exit 1
  fi

  body="$(extract_body "$helper_re")"

  require_count "$helper_name" "$body" lean_float_array_get 1
  require_count "$helper_name" "$body" lean_float_negate 1
  require_count "$helper_name" "$body" lean_float_array_push 1
  require_count "$helper_name" "$body" 'goto _start;' 1
  require_count "$helper_name" "$body" lp_Grassmann_Grassmann_popcount 1
  require_count "$helper_name" "$body" lean_nat_mod 1
  require_count "$helper_name" "$body" lean_nat_dec_eq 2
  require_count "$helper_name" "$body" lean_nat_sub "${nat_subs[$i]}"
  require_count "$helper_name" "$body" lean_nat_add "${nat_adds[$i]}"
  require_count "$helper_name" "$body" lean_nat_mul "${nat_muls[$i]}"
  require_count "$helper_name" "$body" lean_nat_shiftr "${nat_shifts[$i]}"

  if [[ "${packed[$i]}" == 1 ]]; then
    require_count "$helper_name" "$body" lean_array_get_size 1
    require_count "$helper_name" "$body" lean_array_fget_borrowed 1
    require_count "$helper_name" "$body" lean_nat_dec_lt 1
  else
    require_count "$helper_name" "$body" lean_array_get_size 0
    require_count "$helper_name" "$body" lean_array_fget_borrowed 0
    require_count "$helper_name" "$body" lean_nat_dec_lt 0
  fi

  forbid "$helper_name" "$body" \
    'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|l_Array_range|Array_(map|fold)|lean_float_array_set|lean_(inc|dec)_ref'

  printf 'PASS %s generated-C loop structure\n' "$helper_name"
done

involute_re='^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_involute[(][^;]*[)] [\{]$'
if [[ "$(definition_count "$involute_re")" != 1 ]]; then
  printf 'FAIL involute: expected exactly one non-boxed public definition\n' >&2
  exit 1
fi
involute_body="$(extract_body "$involute_re")"
even_body="$(extract_case_body "$involute_body" 'case 0:')"
odd_body="$(extract_case_body "$involute_body" 'case 1:')"
full_body="$(extract_case_body "$involute_body" 'default:')"

require_count 'involute even' "$even_body" lean_inc_ref 1
require_count 'involute even' "$even_body" return 1
forbid 'involute even' "$even_body" \
  'lean_mk_empty_float_array|__Grassmann_MV_(negAux|involuteFullAux)[(]|lean_float_array_|lean_alloc_|lean_apply_|lean_box|l_Array_range|Array_(map|fold)'
require_retain_return 'involute even' "$even_body"
printf 'PASS involute even directly retains and returns its input without allocation\n'

require_count 'involute odd' "$odd_body" lean_mk_empty_float_array 1
require_count 'involute odd' "$odd_body" '__Grassmann_MV_negAux(' 1
require_count 'involute odd' "$odd_body" return 1
forbid 'involute odd' "$odd_body" \
  '__Grassmann_MV_involuteFullAux[(]|lean_float_array_(get|push|set)|lean_alloc_|lean_apply_|lean_box|l_Array_range|Array_(map|fold)'
require_call_result_return 'involute odd' "$odd_body" '__Grassmann_MV_negAux('
printf 'PASS involute odd allocates once and returns negAux directly\n'

require_count 'involute full' "$full_body" lean_mk_empty_float_array 1
require_count 'involute full' "$full_body" '__Grassmann_MV_involuteFullAux(' 1
require_count 'involute full' "$full_body" return 1
forbid 'involute full' "$full_body" \
  '__Grassmann_MV_negAux[(]|lean_float_array_(get|push|set)|lean_alloc_|lean_apply_|lean_box|l_Array_range|Array_(map|fold)'
require_call_result_return 'involute full' "$full_body" '__Grassmann_MV_involuteFullAux('
printf 'PASS involute full allocates once and returns involuteFullAux directly\n'
