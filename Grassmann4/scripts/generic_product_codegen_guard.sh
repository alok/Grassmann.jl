#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
grassmann4_dir="$(cd "$script_dir/.." && pwd)"
outer_dir="$(cd "$grassmann4_dir/.." && pwd)"

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

# Force the C facet from the current source. A normal build may fetch an object
# from Lake's shared cache without materializing the C that this guard audits.
LAKE_CACHE_DIR='' lake --dir "$lake_root" --no-cache build +Grassmann.MV:c

if [[ -n "${MV_C_FILE:-}" ]]; then
  c_file="$MV_C_FILE"
elif [[ -s "$lake_root/.lake/build/ir/Grassmann/MV.c" ]]; then
  c_file="$lake_root/.lake/build/ir/Grassmann/MV.c"
else
  candidates="$({
    lake --dir "$lake_root" query +Grassmann.MV:c |
      rg '^/.*[.]c$'
  } || true)"
  candidate_count="$(
    printf '%s\n' "$candidates" |
      awk 'NF { count++ } END { print count + 0 }'
  )"
  if [[ "$candidate_count" != 1 ]]; then
    printf 'expected exactly one generated Grassmann.MV C file, found %s\n' \
      "$candidate_count" >&2
    printf '%s\n' "$candidates" >&2
    exit 1
  fi
  c_file="$(printf '%s\n' "$candidates" | awk 'NF { print; exit }')"
fi

if [[ ! -s "$c_file" ]]; then
  printf 'generated MV C file is missing or empty: %s\n' "$c_file" >&2
  exit 1
fi

if ! rg -q '^// Module: Grassmann[.]MV$' "$c_file"; then
  printf 'Lake-selected C artifact is not Grassmann.MV: %s\n' "$c_file" >&2
  exit 1
fi

printf 'Inspecting freshly generated C: %s\n' "$c_file"

# Match definitions ending in `{`, excluding forward declarations. Private
# declaration ordinals are deliberately wildcarded; stable Lean helper suffixes
# are the structural contract.
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

sparse_coeff_left_re='^LEAN_EXPORT double .*__Grassmann_MV_productPlanCoeffLeftAux[(][^;]*[)] [{]$'
sparse_coeff_right_re='^LEAN_EXPORT double .*__Grassmann_MV_productPlanCoeffRightAux[(][^;]*[)] [{]$'
sparse_output_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_productPlanOutputAux[(][^;]*[)] [{]$'
geometric_coeff_left_re='^LEAN_EXPORT double .*__Grassmann_MV_geometricPlanCoeffLeftAux[(][^;]*[)] [{]$'
geometric_coeff_right_re='^LEAN_EXPORT double .*__Grassmann_MV_geometricPlanCoeffRightAux[(][^;]*[)] [{]$'
geometric_output_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_geometricPlanOutputAux[(][^;]*[)] [{]$'

for definition in \
    "$sparse_coeff_left_re" "$sparse_coeff_right_re" "$sparse_output_re" \
    "$geometric_coeff_left_re" "$geometric_coeff_right_re" \
    "$geometric_output_re"; do
  if [[ "$(definition_count "$definition")" != 1 ]]; then
    printf 'FAIL planned products: expected one helper matching %s\n' \
      "$definition" >&2
    exit 1
  fi
done

sparse_coeff_left="$(extract_body "$sparse_coeff_left_re")"
sparse_coeff_right="$(extract_body "$sparse_coeff_right_re")"
sparse_output="$(extract_body "$sparse_output_re")"
geometric_coeff_left="$(extract_body "$geometric_coeff_left_re")"
geometric_coeff_right="$(extract_body "$geometric_coeff_right_re")"
geometric_output="$(extract_body "$geometric_output_re")"

planned_forbidden='lean_(inc|dec)_ref|lean_apply_|lean_alloc_closure|lean_mk_closure|Range_forIn|forIn|l_Array_range|lean_array_|lean_float_array_set|lean_mk_empty_float_array|parityJoin|popcount|SignTable|geometricSign|wedgeSign|ContractionSign|reverseSign|packIdx|unpackIdx'

check_coefficient_loop() {
  local label="$1"
  local body="$2"

  require_count "$label" "$body" \
    lean_byte_array_get 1
  require_count "$label" "$body" \
    lean_float_array_get 2
  require_count "$label" "$body" \
    'goto _start;' 1
  require_count "$label" "$body" \
    lean_float_array_push 0
  forbid "$label" "$body" "$planned_forbidden"
  printf 'PASS %s is closed and tail-recursive\n' "$label"
}

check_coefficient_loop 'shared sparse left coefficient loop' \
  "$sparse_coeff_left"
check_coefficient_loop 'shared sparse right coefficient loop' \
  "$sparse_coeff_right"
check_coefficient_loop 'geometric left coefficient loop' \
  "$geometric_coeff_left"
check_coefficient_loop 'geometric right coefficient loop' \
  "$geometric_coeff_right"

check_output_loop() {
  local label="$1"
  local body="$2"
  local left_helper="$3"
  local right_helper="$4"

  # One output-loop iteration computes one scalar coefficient and appends it
  # once. It neither reads nor mutates the result buffer in place.
  require_count "$label" "$body" "$left_helper" 1
  require_count "$label" "$body" "$right_helper" 1
  require_count "$label" "$body" lean_float_array_push 1
  require_count "$label" "$body" lean_float_array_get 0
  require_count "$label" "$body" 'goto _start;' 1
  forbid "$label" "$body" "$planned_forbidden"
  printf 'PASS %s pushes each coefficient exactly once\n' "$label"
}

check_output_loop 'shared sparse output loop' "$sparse_output" \
  __Grassmann_MV_productPlanCoeffLeftAux \
  __Grassmann_MV_productPlanCoeffRightAux
check_output_loop 'geometric output loop' "$geometric_output" \
  __Grassmann_MV_geometricPlanCoeffLeftAux \
  __Grassmann_MV_geometricPlanCoeffRightAux

ops=(mul wedge leftContract rightContract)
fallback_helpers=(mulOutputDirectAux wedgeOutputDirectAux leftContractOutputDirectAux rightContractOutputDirectAux)
planned_helpers=(geometricPlanOutputAux productPlanOutputAux productPlanOutputAux productPlanOutputAux)
other_planned_helpers=(productPlanOutputAux geometricPlanOutputAux geometricPlanOutputAux geometricPlanOutputAux)

for ((i = 0; i < ${#ops[@]}; i++)); do
  op="${ops[$i]}"
  fallback="${fallback_helpers[$i]}"
  planned="${planned_helpers[$i]}"
  other_planned="${other_planned_helpers[$i]}"
  public_re="^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_${op}KernelGeneric[(][^;]*[)] [{]$"

  if [[ "$(definition_count "$public_re")" != 1 ]]; then
    printf 'FAIL %s: expected one generic-kernel definition\n' "$op" >&2
    exit 1
  fi

  public="$(extract_body "$public_re")"
  require_count "$op generic kernel" "$public" lean_mk_empty_float_array 1
  require_count "$op generic kernel" "$public" \
    "__Grassmann_MV_${planned}" 1
  require_count "$op generic kernel" "$public" \
    "__Grassmann_MV_${other_planned}" 0
  require_count "$op generic kernel" "$public" \
    "__Grassmann_MV_${fallback}" 1
  require_count "$op generic kernel" "$public" lean_float_array_get 0
  require_count "$op generic kernel" "$public" lean_float_array_set 0
  require_count "$op generic kernel" "$public" lean_float_array_push 0

  # Parameters x_5 and x_6 are the borrowed packed inputs in all four public
  # signatures. Plan ownership may legitimately release a selected plan, but
  # neither input may be retained or released by this boundary.
  forbid "$op borrowed inputs" "$public" \
    'lean_(inc|dec)(_ref)?[(]x_[56][)]'
  forbid "$op generic kernel" "$public" \
    'lean_apply_|lean_alloc_closure|lean_mk_closure|Range_forIn|forIn|l_Array_range|lean_float_array_set|parityJoin|popcount|SignTable|geometricSign|wedgeSign|ContractionSign|reverseSign'

  printf 'PASS %s owns one result buffer and dispatches to %s\n' \
    "$op" "$planned"
done

printf 'PASS generic product generated-C guard\n'
