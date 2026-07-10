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

# Disable Lake's shared artifact cache and request this module's C facet
# explicitly. A plain module build can report a fetched object without
# materializing the generated C that this guard must inspect.
LAKE_CACHE_DIR='' lake --dir "$lake_root" --no-cache build +Grassmann.MV:c

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

# Require every result assigned from a named helper call to be returned
# directly somewhere in the same generated function. This works for public
# dispatchers with several mutually exclusive return sites.
require_call_results_returned() {
  local label="$1"
  local body="$2"
  local call="$3"
  local assigned
  local found=0

  while IFS= read -r assigned; do
    [[ -z "$assigned" ]] && continue
    found=1
    if ! printf '%s\n' "$body" | rg -F -q "return $assigned;"; then
      printf 'FAIL %s: helper result %s from %s is not returned directly\n' \
        "$label" "$assigned" "$call" >&2
      exit 1
    fi
  done < <(
    printf '%s\n' "$body" |
      awk -v call="$call" '
        index($0, call) != 0 {
          line = $0
          gsub(/[[:space:]]/, "", line)
          sub(/=.*/, "", line)
          print line
        }
      '
  )

  if [[ "$found" == 0 ]]; then
    printf 'FAIL %s: no result assignment found for %s\n' \
      "$label" "$call" >&2
    exit 1
  fi
}

# Require at least one retained input to be returned directly. Public n = 0
# identity branches intentionally need one retain to transfer ownership.
require_direct_retain_return() {
  local label="$1"
  local body="$2"
  local retained
  local found=0

  while IFS= read -r retained; do
    [[ -z "$retained" ]] && continue
    if printf '%s\n' "$body" | rg -F -q "return $retained;"; then
      found=1
      break
    fi
  done < <(
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
  )

  if [[ "$found" == 0 ]]; then
    printf 'FAIL %s: retained input is not returned directly\n' \
      "$label" >&2
    exit 1
  fi
}

# Packed rank/mask conversion is arithmetic in hot paths. Pin the standalone
# valid-input kernels as a compact ABI and reject reconstruction of cached
# Array maps or the checked/public index paths.
unpack_valid_re='^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_unpackIdxValid[(][^;]*[)] [\{]$'
pack_valid_re='^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_packIdxValid[(][^;]*[)] [\{]$'

for definition in "$unpack_valid_re" "$pack_valid_re"; do
  if [[ "$(definition_count "$definition")" != 1 ]]; then
    printf 'FAIL packed valid indexing: expected exactly one matching non-boxed definition: %s\n' \
      "$definition" >&2
    exit 1
  fi
done

unpack_valid="$(extract_body "$unpack_valid_re")"
pack_valid="$(extract_body "$pack_valid_re")"

require_count 'unpackIdxValid' "$unpack_valid" lp_Grassmann_Grassmann_popcount 1
require_count 'unpackIdxValid' "$unpack_valid" lean_nat_add 3
require_count 'unpackIdxValid' "$unpack_valid" lean_nat_mod 2
require_count 'unpackIdxValid' "$unpack_valid" lean_nat_lxor 1
require_count 'unpackIdxValid' "$unpack_valid" lean_nat_dec_eq 1
require_count 'unpackIdxValid full identity' "$unpack_valid" 'lean_inc(x_3);' 1
forbid 'unpackIdxValid' "$unpack_valid" \
  'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|lean_float_array_|lean_array_|l_Array_range|Array_(map|filter|fold|findIdx)|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx[(]|__Grassmann_MV_packIdx[(]|containsMask|lean_(inc|dec)_ref'
printf 'PASS unpackIdxValid is arithmetic and cache-independent\n'

require_count 'packIdxValid' "$pack_valid" lean_nat_shiftr 1
require_count 'packIdxValid full identity' "$pack_valid" 'lean_inc(x_3);' 1
forbid 'packIdxValid' "$pack_valid" \
  'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|lean_float_array_|lean_array_|l_Array_range|Array_(map|filter|fold|findIdx)|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx[(]|__Grassmann_MV_packIdx[(]|containsMask|lp_Grassmann_Grassmann_popcount|lean_nat_(add|mod|lxor)|lean_(inc|dec)_ref'
printf 'PASS packIdxValid is one shift and cache-independent\n'

helpers=(
  revFullAux
  revPackedAux
  involuteFullAux
  conjugateFullAux
  conjugatePackedAux
)
popcounts=(1 1 1 1 1)
nat_mods=(1 3 1 1 3)
nat_eqs=(2 3 2 2 3)
nat_subs=(2 2 1 1 1)
nat_adds=(1 2 1 2 3)
nat_muls=(1 1 0 1 1)
nat_shifts=(1 1 0 1 1)
nat_lxors=(0 1 0 0 1)

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
  require_count "$helper_name" "$body" lp_Grassmann_Grassmann_popcount "${popcounts[$i]}"
  require_count "$helper_name" "$body" lean_nat_mod "${nat_mods[$i]}"
  require_count "$helper_name" "$body" lean_nat_dec_eq "${nat_eqs[$i]}"
  require_count "$helper_name" "$body" lean_nat_sub "${nat_subs[$i]}"
  require_count "$helper_name" "$body" lean_nat_add "${nat_adds[$i]}"
  require_count "$helper_name" "$body" lean_nat_mul "${nat_muls[$i]}"
  require_count "$helper_name" "$body" lean_nat_shiftr "${nat_shifts[$i]}"
  require_count "$helper_name" "$body" lean_nat_lxor "${nat_lxors[$i]}"

  forbid "$helper_name" "$body" \
    'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|l_Array_range|Array_(map|filter|fold|findIdx)|lean_array_|lean_float_array_set|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx|__Grassmann_MV_packIdx|containsMask|lean_(inc|dec)_ref'

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

# Projection and parity widening use four allocation-free coefficient loops.
# Pin their arithmetic index/grade logic, direct FloatArray traffic, and tail
# recursion separately from public allocation and dimension-zero dispatch.
projection_helpers=(
  parityPartAux
  gradeProjectFullAux
  gradeProjectPackedAux
  parityToFullAux
)
projection_pushes=(1 1 1 4)
projection_popcounts=(1 1 1 1)
projection_mods=(2 0 2 2)
projection_eqs=(2 2 3 3)
projection_adds=(4 1 2 1)
projection_lxors=(1 0 1 1)

for ((i = 0; i < ${#projection_helpers[@]}; i++)); do
  helper_name="${projection_helpers[$i]}"
  helper_re="^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_${helper_name}[(][^;]*[)] [\{]$"

  if [[ "$(definition_count "$helper_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one non-boxed projection helper definition\n' \
      "$helper_name" >&2
    exit 1
  fi

  body="$(extract_body "$helper_re")"
  require_count "$helper_name" "$body" lean_float_array_get 1
  require_count "$helper_name" "$body" lean_float_array_push "${projection_pushes[$i]}"
  require_count "$helper_name" "$body" 'goto _start;' 1
  require_count "$helper_name" "$body" lp_Grassmann_Grassmann_popcount "${projection_popcounts[$i]}"
  require_count "$helper_name" "$body" lean_nat_mod "${projection_mods[$i]}"
  require_count "$helper_name" "$body" lean_nat_dec_eq "${projection_eqs[$i]}"
  require_count "$helper_name" "$body" lean_nat_sub 1
  require_count "$helper_name" "$body" lean_nat_add "${projection_adds[$i]}"
  require_count "$helper_name" "$body" lean_nat_lxor "${projection_lxors[$i]}"

  forbid "$helper_name" "$body" \
    'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|lean_nat_pow|l_Array_range|Array_(map|filter|fold|findIdx)|lean_array_|lean_float_array_(set|size)|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx|__Grassmann_MV_packIdx|containsMask|lean_(inc|dec)_ref'

  printf 'PASS %s generated-C projection loop structure\n' "$helper_name"
done

# Public parity extraction and widening wrappers. Check both the exported
# declaration and the compiler's reduced-argument clone because either may be
# selected by downstream generated code.
projection_publics=(evenPart oddPart evenToFull oddToFull)
projection_public_helpers=(parityPartAux parityPartAux parityToFullAux parityToFullAux)
projection_public_empties=(1 1 1 2)
projection_public_retains=(1 1 1 0)
projection_public_replicates=(0 0 0 1)
projection_public_pows=(1 1 2 3)

for ((i = 0; i < ${#projection_publics[@]}; i++)); do
  public_name="${projection_publics[$i]}"
  helper_name="${projection_public_helpers[$i]}"

  for suffix in '' '___redArg'; do
    label="${public_name}${suffix}"
    public_re="^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_${label}[(][^;]*[)] [\{]$"

    if [[ "$(definition_count "$public_re")" != 1 ]]; then
      printf 'FAIL %s: expected exactly one non-boxed public definition\n' \
        "$label" >&2
      exit 1
    fi

    body="$(extract_body "$public_re")"
    require_count "$label" "$body" "__Grassmann_MV_${helper_name}(" 1
    require_count "$label" "$body" lean_mk_empty_float_array \
      "${projection_public_empties[$i]}"
    require_count "$label" "$body" lean_inc_ref \
      "${projection_public_retains[$i]}"
    require_count "$label" "$body" lean_dec_ref 0
    require_count "$label" "$body" DataArray_replicateAux \
      "${projection_public_replicates[$i]}"
    require_count "$label" "$body" lean_nat_pow \
      "${projection_public_pows[$i]}"
    require_call_results_returned "$label" "$body" \
      "__Grassmann_MV_${helper_name}("

    if [[ "${projection_public_retains[$i]}" == 1 ]]; then
      require_direct_retain_return "$label n=0" "$body"
    fi
    if [[ "${projection_public_replicates[$i]}" == 1 ]]; then
      require_call_results_returned "$label n=0 zero" "$body" \
        'DataArray_replicateAux('
    fi

    forbid "$label" "$body" \
      'lean_alloc_|lean_apply_|lean_box|lean_float_array_(get|push|set|size)|l_Array_range|Array_(map|filter|fold|findIdx)|lean_array_|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx|__Grassmann_MV_packIdx|containsMask'

    printf 'PASS %s generated-C allocation and n=0 dispatch\n' "$label"
  done
done

# Grade projection has valid full/packed loops, two structurally separate zero
# paths (invalid grade and the n = 0 non-scalar case), and an n = 0 scalar
# identity path. There are four static empty-buffer sites but only one can run.
for suffix in '' '___redArg'; do
  label="gradeProject${suffix}"
  public_re="^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_${label}[(][^;]*[)] [\{]$"

  if [[ "$(definition_count "$public_re")" != 1 ]]; then
    printf 'FAIL %s: expected exactly one non-boxed public definition\n' \
      "$label" >&2
    exit 1
  fi

  body="$(extract_body "$public_re")"
  require_count "$label" "$body" '__Grassmann_MV_gradeProjectFullAux(' 1
  require_count "$label" "$body" '__Grassmann_MV_gradeProjectPackedAux(' 1
  require_count "$label" "$body" DataArray_replicateAux 2
  require_count "$label" "$body" lean_mk_empty_float_array 4
  require_count "$label" "$body" lean_inc_ref 1
  require_count "$label" "$body" lean_dec_ref 0
  require_count "$label" "$body" lean_nat_dec_lt 1
  require_count "$label" "$body" lean_nat_mod 2
  require_count "$label" "$body" lean_nat_pow 6
  require_call_results_returned "$label full" "$body" \
    '__Grassmann_MV_gradeProjectFullAux('
  require_call_results_returned "$label packed" "$body" \
    '__Grassmann_MV_gradeProjectPackedAux('
  require_call_results_returned "$label zero" "$body" \
    'DataArray_replicateAux('
  require_direct_retain_return "$label n=0 scalar" "$body"

  forbid "$label" "$body" \
    'lean_alloc_|lean_apply_|lean_box|lean_float_array_(get|push|set|size)|l_Array_range|Array_(map|filter|fold|findIdx)|lean_array_|computeIndices|__Grassmann_MV_indices|__Grassmann_MV_unpackIdx|__Grassmann_MV_packIdx|containsMask'

  printf 'PASS %s generated-C valid, zero, and n=0 dispatch\n' "$label"
done

# Hodge dual uses a compact orientation bit stream for dimensions 0--6 and a
# parity fallback above that boundary. Pin the selector ABI, both tail loops,
# and the single-allocation public dispatch independently.
hodge_bits_re='^LEAN_EXPORT uint64_t .*__Grassmann_MV_hodgeDualNegBits[(][^;]*[)] [\{]$'
hodge_small_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_hodgeDualSmallAux[(][^;]*[)] [\{]$'
hodge_large_re='^LEAN_EXPORT lean_object[*] .*__Grassmann_MV_hodgeDualLargeAux[(][^;]*[)] [\{]$'
hodge_public_re='^LEAN_EXPORT lean_object[*] lp_Grassmann_Grassmann_MV_hodgeDual[(][^;]*[)] [\{]$'

for definition in \
  "$hodge_bits_re" \
  "$hodge_small_re" \
  "$hodge_large_re" \
  "$hodge_public_re"; do
  if [[ "$(definition_count "$definition")" != 1 ]]; then
    printf 'FAIL hodge dual: expected exactly one matching non-boxed definition: %s\n' \
      "$definition" >&2
    exit 1
  fi
done

hodge_bits="$(extract_body "$hodge_bits_re")"
hodge_small="$(extract_body "$hodge_small_re")"
hodge_large="$(extract_body "$hodge_large_re")"
hodge_public="$(extract_body "$hodge_public_re")"

require_count 'hodge sign selector' "$hodge_bits" lean_nat_dec_eq 7
require_count 'hodge sign selector ABI' "$hodge_bits" \
  'LEAN_EXPORT uint64_t ' 1
forbid 'hodge sign selector' "$hodge_bits" \
  'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|lean_float_array_|l_Array_range|Array_(map|fold)|lean_array_|BitVec|pseudoscalar|nat_lxor|leftComplementSign|lean_(inc|dec)_ref'
printf 'PASS hodge sign selector is unboxed UInt64\n'

require_count 'hodge small helper ABI' "$hodge_small" \
  'hodgeDualSmallAux(lean_object*' 1
require_count 'hodge small helper ABI' "$hodge_small" \
  'uint64_t x_2, lean_object* x_3' 1
require_count 'hodge small helper' "$hodge_small" lean_float_array_get 1
require_count 'hodge small helper' "$hodge_small" lean_uint64_land 1
require_count 'hodge small helper' "$hodge_small" lean_uint64_dec_eq 1
require_count 'hodge small helper' "$hodge_small" lean_float_negate 1
require_count 'hodge small helper' "$hodge_small" lean_uint64_shift_right 1
require_count 'hodge small helper' "$hodge_small" lean_nat_sub 1
require_count 'hodge small helper' "$hodge_small" lean_float_array_push 1
require_count 'hodge small helper' "$hodge_small" 'goto _start;' 1
forbid 'hodge small helper' "$hodge_small" \
  'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|l_Array_range|Array_(map|fold)|lean_array_|lean_float_array_set|BitVec|pseudoscalar|nat_lxor|leftComplementSign|parityJoinBasic|lean_(inc|dec)_ref'
printf 'PASS hodge small-dimension generated-C loop structure\n'

require_count 'hodge large helper' "$hodge_large" lean_float_array_get 1
require_count 'hodge large helper' "$hodge_large" parityJoinBasic 1
require_count 'hodge large helper' "$hodge_large" lean_float_negate 1
require_count 'hodge large helper' "$hodge_large" lean_nat_sub 1
require_count 'hodge large helper' "$hodge_large" lean_nat_add 1
require_count 'hodge large helper' "$hodge_large" lean_float_array_push 1
require_count 'hodge large helper' "$hodge_large" 'goto _start;' 1
forbid 'hodge large helper' "$hodge_large" \
  'lean_alloc_|lean_apply_|lean_box|lean_mk_empty_float_array|l_Array_range|Array_(map|fold)|lean_array_|lean_float_array_set|BitVec|pseudoscalar|nat_lxor|leftComplementSign|lean_(inc|dec)_ref'
printf 'PASS hodge large-dimension generated-C loop structure\n'

require_count 'hodge public' "$hodge_public" lean_nat_pow 1
require_count 'hodge public' "$hodge_public" lean_mk_empty_float_array 1
require_count 'hodge public' "$hodge_public" lean_nat_dec_le 1
require_count 'hodge public' "$hodge_public" '__Grassmann_MV_hodgeDualNegBits(' 1
require_count 'hodge public' "$hodge_public" '__Grassmann_MV_hodgeDualSmallAux(' 1
require_count 'hodge public' "$hodge_public" '__Grassmann_MV_hodgeDualLargeAux(' 1
forbid 'hodge public' "$hodge_public" \
  'lean_alloc_|lean_apply_|lean_box|l_Array_range|Array_(map|fold)|lean_array_|lean_float_array_(get|push|set)|BitVec|pseudoscalar|nat_lxor|leftComplementSign|lean_(inc|dec)_ref'
printf 'PASS hodge public dispatch allocates one result buffer\n'
