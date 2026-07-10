#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
pkg_root="${GRASSMANN_LAKE_ROOT:-$repo_root}"

if [[ ! -f "$pkg_root/lakefile.toml" || ! -f "$pkg_root/lean-toolchain" ]]; then
  printf 'invalid Grassmann Lake root: %s\n' "$pkg_root" >&2
  exit 1
fi

for tool in lake awk sed; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$tool" >&2
    exit 1
  fi
done

smoke_iters="${PACKED_MV_BENCH_SMOKE_ITERS:-200}"
motor_iters="${PACKED_MV_BENCH_MOTOR_ITERS:-5000}"
subtraction_iters="${PACKED_MV_BENCH_SUBTRACTION_ITERS:-100000}"
linear_iters="${PACKED_MV_BENCH_LINEAR_ITERS:-500000}"
unary_iters="${PACKED_MV_BENCH_UNARY_ITERS:-100000}"
hodge_iters="${PACKED_MV_BENCH_HODGE_ITERS:-100000}"
projection_iters="${PACKED_MV_BENCH_PROJECTION_ITERS:-100000}"
max_correctness_diff="${MAX_PACKED_MV_CORRECTNESS_DIFF:-1e-6}"
max_packed_motor_ns="${MAX_PACKED_PGA_MOTOR_POINT_NS:-20000}"
min_motor_speedup="${MIN_PACKED_PGA_MOTOR_POINT_SPEEDUP:-5}"
max_packed_subtraction_ns="${MAX_PACKED_MV_SUBTRACTION_NS:-500}"
# The composed baseline is now two optimized one-buffer kernels. Direct
# subtraction must still save one traversal and one result buffer.
min_subtraction_speedup="${MIN_PACKED_MV_SUBTRACTION_SPEEDUP:-1.5}"
max_packed_add_ns="${MAX_PACKED_MV_ADD_NS:-500}"
min_packed_add_speedup="${MIN_PACKED_MV_ADD_SPEEDUP:-2.5}"
max_packed_neg_ns="${MAX_PACKED_MV_NEG_NS:-500}"
min_packed_neg_speedup="${MIN_PACKED_MV_NEG_SPEEDUP:-2.5}"
max_packed_smul_ns="${MAX_PACKED_MV_SMUL_NS:-500}"
min_packed_smul_speedup="${MIN_PACKED_MV_SMUL_SPEEDUP:-2.5}"
# The direct CGA3 unary kernels are one-buffer loops, except for the even
# involute identity and odd involute negation fast paths. Separate ceilings
# preserve those stronger guarantees without overfitting one host.
max_packed_full_unary_ns="${MAX_PACKED_MV_FULL_UNARY_NS:-750}"
max_packed_parity_unary_ns="${MAX_PACKED_MV_PARITY_UNARY_NS:-500}"
max_packed_even_involute_ns="${MAX_PACKED_MV_EVEN_INVOLUTE_NS:-100}"
max_packed_odd_involute_ns="${MAX_PACKED_MV_ODD_INVOLUTE_NS:-150}"
min_packed_unary_speedup="${MIN_PACKED_MV_UNARY_SPEEDUP:-20}"
# Four repeated 100k CGA3 runs measured the one-buffer orientation-mask kernel
# at 79-81 ns/iter and the exact old boxed shape at 26.7-27.8 us/iter.
max_packed_hodge_ns="${MAX_PACKED_MV_HODGE_NS:-250}"
min_packed_hodge_speedup="${MIN_PACKED_MV_HODGE_SPEEDUP:-100}"
# Projection and parity-widening kernels traverse at most one input and build
# exactly one output buffer. Keep separate ceilings for full projection,
# half-sized projection, and widening while sharing the boxed-shape speedup
# floor across all seven operations.
max_packed_full_projection_ns="${MAX_PACKED_MV_FULL_PROJECTION_NS:-500}"
max_packed_half_projection_ns="${MAX_PACKED_MV_HALF_PROJECTION_NS:-300}"
max_packed_widening_ns="${MAX_PACKED_MV_WIDENING_NS:-300}"
min_packed_projection_speedup="${MIN_PACKED_MV_PROJECTION_SPEEDUP:-3.0}"

bench_log="${PACKED_MV_BENCH_GUARD_LOG:-}"
if [[ -z "$bench_log" ]]; then
  bench_log="$(mktemp "${TMPDIR:-/tmp}/grassmann-packedmvbench.XXXXXX")"
fi

summary_json="${PACKED_MV_BENCH_GUARD_SUMMARY:-$bench_log.summary.json}"

numeric_le() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual <= expected ? 0 : 1) }'
}

numeric_ge() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual >= expected ? 0 : 1) }'
}

ratio() {
  awk -v numerator="$1" -v denominator="$2" \
    'BEGIN { if (denominator == 0) exit 1; printf "%.3f", numerator / denominator }'
}

extract_timed_value() {
  local label="$1"
  awk -F ': ' -v label="$label" '
    {
      key = $1
      sub(/^[[:space:]]+/, "", key)
      sub(/[[:space:]]+$/, "", key)
    }
    key == label {
      split($2, parts, " ")
      value = parts[1]
      found = 1
    }
    END { if (found) print value; else exit 1 }
  ' "$bench_log"
}

extract_last_value() {
  local label="$1"
  awk -F ': ' -v label="$label" '
    {
      key = $1
      sub(/^[[:space:]]+/, "", key)
      sub(/[[:space:]]+$/, "", key)
    }
    key == label {
      n = split($0, parts, " ")
      value = parts[n]
      found = 1
    }
    END { if (found) print value; else exit 1 }
  ' "$bench_log"
}

get_timed_metric() {
  local label="$1"
  local value
  if ! value="$(extract_timed_value "$label")"; then
    printf 'missing benchmark metric: %s\n' "$label" >&2
    printf 'benchmark log: %s\n' "$bench_log" >&2
    exit 1
  fi
  printf '%s\n' "$value"
}

get_last_metric() {
  local label="$1"
  local value
  if ! value="$(extract_last_value "$label")"; then
    printf 'missing benchmark metric: %s\n' "$label" >&2
    printf 'benchmark log: %s\n' "$bench_log" >&2
    exit 1
  fi
  printf '%s\n' "$value"
}

failures=()

check_le() {
  local label="$1"
  local actual="$2"
  local expected="$3"
  local unit="$4"

  if ! numeric_le "$actual" "$expected"; then
    failures+=("$label $actual $unit above threshold $expected $unit")
  fi
}

check_ge() {
  local label="$1"
  local actual="$2"
  local expected="$3"
  local unit="$4"

  if ! numeric_ge "$actual" "$expected"; then
    failures+=("$label $actual $unit below threshold $expected $unit")
  fi
}

json_escape() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g'
}

write_summary_json() {
  local status="$1"
  {
    printf '{\n'
    printf '  "status": "%s",\n' "$(json_escape "$status")"
    printf '  "benchmark_log": "%s",\n' "$(json_escape "$bench_log")"
    printf '  "thresholds": {\n'
    printf '    "max_correctness_diff": %s,\n' "$max_correctness_diff"
    printf '    "max_packed_motor_ns": %s,\n' "$max_packed_motor_ns"
    printf '    "min_motor_speedup": %s,\n' "$min_motor_speedup"
    printf '    "max_packed_subtraction_ns": %s,\n' "$max_packed_subtraction_ns"
    printf '    "min_subtraction_speedup": %s,\n' "$min_subtraction_speedup"
    printf '    "max_packed_add_ns": %s,\n' "$max_packed_add_ns"
    printf '    "min_packed_add_speedup": %s,\n' "$min_packed_add_speedup"
    printf '    "max_packed_neg_ns": %s,\n' "$max_packed_neg_ns"
    printf '    "min_packed_neg_speedup": %s,\n' "$min_packed_neg_speedup"
    printf '    "max_packed_smul_ns": %s,\n' "$max_packed_smul_ns"
    printf '    "min_packed_smul_speedup": %s,\n' "$min_packed_smul_speedup"
    printf '    "max_packed_full_unary_ns": %s,\n' "$max_packed_full_unary_ns"
    printf '    "max_packed_parity_unary_ns": %s,\n' "$max_packed_parity_unary_ns"
    printf '    "max_packed_even_involute_ns": %s,\n' "$max_packed_even_involute_ns"
    printf '    "max_packed_odd_involute_ns": %s,\n' "$max_packed_odd_involute_ns"
    printf '    "min_packed_unary_speedup": %s,\n' "$min_packed_unary_speedup"
    printf '    "max_packed_hodge_ns": %s,\n' "$max_packed_hodge_ns"
    printf '    "min_packed_hodge_speedup": %s,\n' "$min_packed_hodge_speedup"
    printf '    "max_packed_full_projection_ns": %s,\n' "$max_packed_full_projection_ns"
    printf '    "max_packed_half_projection_ns": %s,\n' "$max_packed_half_projection_ns"
    printf '    "max_packed_widening_ns": %s,\n' "$max_packed_widening_ns"
    printf '    "min_packed_projection_speedup": %s\n' "$min_packed_projection_speedup"
    printf '  },\n'
    printf '  "metrics": {\n'
    printf '    "pga_motor_point_diff": %s,\n' "$motor_point_diff"
    printf '    "dense_motor_point_ns": %s,\n' "$dense_motor_ns"
    printf '    "packed_motor_point_ns": %s,\n' "$packed_motor_ns"
    printf '    "packed_add_neg_subtraction_ns": %s,\n' "$composed_subtraction_ns"
    printf '    "packed_direct_subtraction_ns": %s,\n' "$direct_subtraction_ns"
    printf '    "packed_boxed_add_ns": %s,\n' "$boxed_add_ns"
    printf '    "packed_direct_add_ns": %s,\n' "$direct_add_ns"
    printf '    "packed_boxed_neg_ns": %s,\n' "$boxed_neg_ns"
    printf '    "packed_direct_neg_ns": %s,\n' "$direct_neg_ns"
    printf '    "packed_boxed_smul_ns": %s,\n' "$boxed_smul_ns"
    printf '    "packed_direct_smul_ns": %s,\n' "$direct_smul_ns"
    printf '    "unary_reverse_full_diff": %s,\n' "$reverse_full_diff"
    printf '    "unary_reverse_even_diff": %s,\n' "$reverse_even_diff"
    printf '    "unary_reverse_odd_diff": %s,\n' "$reverse_odd_diff"
    printf '    "unary_involute_full_diff": %s,\n' "$involute_full_diff"
    printf '    "unary_involute_even_diff": %s,\n' "$involute_even_diff"
    printf '    "unary_involute_odd_diff": %s,\n' "$involute_odd_diff"
    printf '    "unary_conjugate_full_diff": %s,\n' "$conjugate_full_diff"
    printf '    "unary_conjugate_even_diff": %s,\n' "$conjugate_even_diff"
    printf '    "unary_conjugate_odd_diff": %s,\n' "$conjugate_odd_diff"
    printf '    "packed_boxed_reverse_full_ns": %s,\n' "$boxed_reverse_full_ns"
    printf '    "packed_direct_reverse_full_ns": %s,\n' "$direct_reverse_full_ns"
    printf '    "packed_boxed_reverse_even_ns": %s,\n' "$boxed_reverse_even_ns"
    printf '    "packed_direct_reverse_even_ns": %s,\n' "$direct_reverse_even_ns"
    printf '    "packed_boxed_reverse_odd_ns": %s,\n' "$boxed_reverse_odd_ns"
    printf '    "packed_direct_reverse_odd_ns": %s,\n' "$direct_reverse_odd_ns"
    printf '    "packed_boxed_involute_full_ns": %s,\n' "$boxed_involute_full_ns"
    printf '    "packed_direct_involute_full_ns": %s,\n' "$direct_involute_full_ns"
    printf '    "packed_boxed_involute_even_ns": %s,\n' "$boxed_involute_even_ns"
    printf '    "packed_direct_involute_even_ns": %s,\n' "$direct_involute_even_ns"
    printf '    "packed_boxed_involute_odd_ns": %s,\n' "$boxed_involute_odd_ns"
    printf '    "packed_direct_involute_odd_ns": %s,\n' "$direct_involute_odd_ns"
    printf '    "packed_boxed_conjugate_full_ns": %s,\n' "$boxed_conjugate_full_ns"
    printf '    "packed_direct_conjugate_full_ns": %s,\n' "$direct_conjugate_full_ns"
    printf '    "packed_boxed_conjugate_even_ns": %s,\n' "$boxed_conjugate_even_ns"
    printf '    "packed_direct_conjugate_even_ns": %s,\n' "$direct_conjugate_even_ns"
    printf '    "packed_boxed_conjugate_odd_ns": %s,\n' "$boxed_conjugate_odd_ns"
    printf '    "packed_direct_conjugate_odd_ns": %s,\n' "$direct_conjugate_odd_ns"
    printf '    "hodge_dual_l1_diff": %s,\n' "$hodge_dual_diff"
    printf '    "packed_boxed_hodge_dual_ns": %s,\n' "$boxed_hodge_dual_ns"
    printf '    "packed_direct_hodge_dual_ns": %s,\n' "$direct_hodge_dual_ns"
    printf '    "projection_full_grade2_l1_diff": %s,\n' "$projection_full_grade2_diff"
    printf '    "projection_even_grade2_l1_diff": %s,\n' "$projection_even_grade2_diff"
    printf '    "projection_odd_grade3_l1_diff": %s,\n' "$projection_odd_grade3_diff"
    printf '    "projection_even_part_l1_diff": %s,\n' "$projection_even_part_diff"
    printf '    "projection_odd_part_l1_diff": %s,\n' "$projection_odd_part_diff"
    printf '    "widening_even_to_full_l1_diff": %s,\n' "$widening_even_to_full_diff"
    printf '    "widening_odd_to_full_l1_diff": %s,\n' "$widening_odd_to_full_diff"
    printf '    "packed_boxed_full_grade2_projection_ns": %s,\n' "$boxed_full_grade2_projection_ns"
    printf '    "packed_direct_full_grade2_projection_ns": %s,\n' "$direct_full_grade2_projection_ns"
    printf '    "packed_boxed_even_grade2_projection_ns": %s,\n' "$boxed_even_grade2_projection_ns"
    printf '    "packed_direct_even_grade2_projection_ns": %s,\n' "$direct_even_grade2_projection_ns"
    printf '    "packed_boxed_odd_grade3_projection_ns": %s,\n' "$boxed_odd_grade3_projection_ns"
    printf '    "packed_direct_odd_grade3_projection_ns": %s,\n' "$direct_odd_grade3_projection_ns"
    printf '    "packed_boxed_even_part_ns": %s,\n' "$boxed_even_part_ns"
    printf '    "packed_direct_even_part_ns": %s,\n' "$direct_even_part_ns"
    printf '    "packed_boxed_odd_part_ns": %s,\n' "$boxed_odd_part_ns"
    printf '    "packed_direct_odd_part_ns": %s,\n' "$direct_odd_part_ns"
    printf '    "packed_boxed_even_to_full_ns": %s,\n' "$boxed_even_to_full_widening_ns"
    printf '    "packed_direct_even_to_full_ns": %s,\n' "$direct_even_to_full_widening_ns"
    printf '    "packed_boxed_odd_to_full_ns": %s,\n' "$boxed_odd_to_full_widening_ns"
    printf '    "packed_direct_odd_to_full_ns": %s\n' "$direct_odd_to_full_widening_ns"
    printf '  },\n'
    printf '  "speedups": {\n'
    printf '    "pga_motor_point": %s,\n' "$motor_speedup"
    printf '    "packed_subtraction": %s,\n' "$subtraction_speedup"
    printf '    "packed_add": %s,\n' "$add_speedup"
    printf '    "packed_neg": %s,\n' "$neg_speedup"
    printf '    "packed_smul": %s,\n' "$smul_speedup"
    printf '    "packed_reverse_full": %s,\n' "$reverse_full_speedup"
    printf '    "packed_reverse_even": %s,\n' "$reverse_even_speedup"
    printf '    "packed_reverse_odd": %s,\n' "$reverse_odd_speedup"
    printf '    "packed_involute_full": %s,\n' "$involute_full_speedup"
    printf '    "packed_involute_even": %s,\n' "$involute_even_speedup"
    printf '    "packed_involute_odd": %s,\n' "$involute_odd_speedup"
    printf '    "packed_conjugate_full": %s,\n' "$conjugate_full_speedup"
    printf '    "packed_conjugate_even": %s,\n' "$conjugate_even_speedup"
    printf '    "packed_conjugate_odd": %s,\n' "$conjugate_odd_speedup"
    printf '    "packed_hodge_dual": %s,\n' "$hodge_dual_speedup"
    printf '    "packed_full_grade2_projection": %s,\n' "$full_grade2_projection_speedup"
    printf '    "packed_even_grade2_projection": %s,\n' "$even_grade2_projection_speedup"
    printf '    "packed_odd_grade3_projection": %s,\n' "$odd_grade3_projection_speedup"
    printf '    "packed_even_part": %s,\n' "$even_part_speedup"
    printf '    "packed_odd_part": %s,\n' "$odd_part_speedup"
    printf '    "packed_even_to_full": %s,\n' "$even_to_full_widening_speedup"
    printf '    "packed_odd_to_full": %s\n' "$odd_to_full_widening_speedup"
    printf '  }\n'
    printf '}\n'
  } > "$summary_json"
}

cd "$pkg_root"
: > "$bench_log"

if ! lake exe packedmvbench all "$smoke_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench all failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench pga-motor-point "$motor_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench pga-motor-point failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench subtraction "$subtraction_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench subtraction failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench linear-arithmetic "$linear_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench linear-arithmetic failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench unary-involutions "$unary_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench unary-involutions failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench hodge-dual "$hodge_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench hodge-dual failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

if ! lake exe packedmvbench projections-widening "$projection_iters" >> "$bench_log" 2>&1; then
  printf 'lake exe packedmvbench projections-widening failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

motor_point_diff="$(get_last_metric "PGA3 motor point transform")"
dense_motor_ns="$(get_timed_metric "dense motor point transform")"
packed_motor_ns="$(get_timed_metric "packed MV motor point transform")"
motor_speedup="$(ratio "$dense_motor_ns" "$packed_motor_ns")"
composed_subtraction_ns="$(get_timed_metric "packed add-neg subtraction")"
direct_subtraction_ns="$(get_timed_metric "packed direct subtraction")"
subtraction_speedup="$(ratio "$composed_subtraction_ns" "$direct_subtraction_ns")"
boxed_add_ns="$(get_timed_metric "boxed CGA3 full add")"
direct_add_ns="$(get_timed_metric "direct CGA3 full add")"
boxed_neg_ns="$(get_timed_metric "boxed CGA3 full neg")"
direct_neg_ns="$(get_timed_metric "direct CGA3 full neg")"
boxed_smul_ns="$(get_timed_metric "boxed CGA3 full smul")"
direct_smul_ns="$(get_timed_metric "direct CGA3 full smul")"
add_speedup="$(ratio "$boxed_add_ns" "$direct_add_ns")"
neg_speedup="$(ratio "$boxed_neg_ns" "$direct_neg_ns")"
smul_speedup="$(ratio "$boxed_smul_ns" "$direct_smul_ns")"
reverse_full_diff="$(get_last_metric "reverse full l1 diff")"
reverse_even_diff="$(get_last_metric "reverse even l1 diff")"
reverse_odd_diff="$(get_last_metric "reverse odd l1 diff")"
involute_full_diff="$(get_last_metric "involute full l1 diff")"
involute_even_diff="$(get_last_metric "involute even l1 diff")"
involute_odd_diff="$(get_last_metric "involute odd l1 diff")"
conjugate_full_diff="$(get_last_metric "conjugate full l1 diff")"
conjugate_even_diff="$(get_last_metric "conjugate even l1 diff")"
conjugate_odd_diff="$(get_last_metric "conjugate odd l1 diff")"
boxed_reverse_full_ns="$(get_timed_metric "boxed CGA3 full reverse")"
direct_reverse_full_ns="$(get_timed_metric "direct CGA3 full reverse")"
boxed_reverse_even_ns="$(get_timed_metric "boxed CGA3 even reverse")"
direct_reverse_even_ns="$(get_timed_metric "direct CGA3 even reverse")"
boxed_reverse_odd_ns="$(get_timed_metric "boxed CGA3 odd reverse")"
direct_reverse_odd_ns="$(get_timed_metric "direct CGA3 odd reverse")"
boxed_involute_full_ns="$(get_timed_metric "boxed CGA3 full involute")"
direct_involute_full_ns="$(get_timed_metric "direct CGA3 full involute")"
boxed_involute_even_ns="$(get_timed_metric "boxed CGA3 even involute")"
direct_involute_even_ns="$(get_timed_metric "direct CGA3 even involute")"
boxed_involute_odd_ns="$(get_timed_metric "boxed CGA3 odd involute")"
direct_involute_odd_ns="$(get_timed_metric "direct CGA3 odd involute")"
boxed_conjugate_full_ns="$(get_timed_metric "boxed CGA3 full conjugate")"
direct_conjugate_full_ns="$(get_timed_metric "direct CGA3 full conjugate")"
boxed_conjugate_even_ns="$(get_timed_metric "boxed CGA3 even conjugate")"
direct_conjugate_even_ns="$(get_timed_metric "direct CGA3 even conjugate")"
boxed_conjugate_odd_ns="$(get_timed_metric "boxed CGA3 odd conjugate")"
direct_conjugate_odd_ns="$(get_timed_metric "direct CGA3 odd conjugate")"
reverse_full_speedup="$(ratio "$boxed_reverse_full_ns" "$direct_reverse_full_ns")"
reverse_even_speedup="$(ratio "$boxed_reverse_even_ns" "$direct_reverse_even_ns")"
reverse_odd_speedup="$(ratio "$boxed_reverse_odd_ns" "$direct_reverse_odd_ns")"
involute_full_speedup="$(ratio "$boxed_involute_full_ns" "$direct_involute_full_ns")"
involute_even_speedup="$(ratio "$boxed_involute_even_ns" "$direct_involute_even_ns")"
involute_odd_speedup="$(ratio "$boxed_involute_odd_ns" "$direct_involute_odd_ns")"
conjugate_full_speedup="$(ratio "$boxed_conjugate_full_ns" "$direct_conjugate_full_ns")"
conjugate_even_speedup="$(ratio "$boxed_conjugate_even_ns" "$direct_conjugate_even_ns")"
conjugate_odd_speedup="$(ratio "$boxed_conjugate_odd_ns" "$direct_conjugate_odd_ns")"
hodge_dual_diff="$(get_last_metric "hodge dual l1 diff")"
boxed_hodge_dual_ns="$(get_timed_metric "boxed CGA3 full hodge dual")"
direct_hodge_dual_ns="$(get_timed_metric "direct CGA3 full hodge dual")"
hodge_dual_speedup="$(ratio "$boxed_hodge_dual_ns" "$direct_hodge_dual_ns")"
projection_full_grade2_diff="$(get_last_metric "projection full grade2 l1 diff")"
projection_even_grade2_diff="$(get_last_metric "projection even grade2 l1 diff")"
projection_odd_grade3_diff="$(get_last_metric "projection odd grade3 l1 diff")"
projection_even_part_diff="$(get_last_metric "projection even part l1 diff")"
projection_odd_part_diff="$(get_last_metric "projection odd part l1 diff")"
widening_even_to_full_diff="$(get_last_metric "widening even to full l1 diff")"
widening_odd_to_full_diff="$(get_last_metric "widening odd to full l1 diff")"
boxed_full_grade2_projection_ns="$(get_timed_metric "boxed CGA3 full grade-2 projection")"
direct_full_grade2_projection_ns="$(get_timed_metric "direct CGA3 full grade-2 projection")"
boxed_even_grade2_projection_ns="$(get_timed_metric "boxed CGA3 even grade-2 projection")"
direct_even_grade2_projection_ns="$(get_timed_metric "direct CGA3 even grade-2 projection")"
boxed_odd_grade3_projection_ns="$(get_timed_metric "boxed CGA3 odd grade-3 projection")"
direct_odd_grade3_projection_ns="$(get_timed_metric "direct CGA3 odd grade-3 projection")"
boxed_even_part_ns="$(get_timed_metric "boxed CGA3 even part")"
direct_even_part_ns="$(get_timed_metric "direct CGA3 even part")"
boxed_odd_part_ns="$(get_timed_metric "boxed CGA3 odd part")"
direct_odd_part_ns="$(get_timed_metric "direct CGA3 odd part")"
boxed_even_to_full_widening_ns="$(get_timed_metric "boxed CGA3 even-to-full widening")"
direct_even_to_full_widening_ns="$(get_timed_metric "direct CGA3 even-to-full widening")"
boxed_odd_to_full_widening_ns="$(get_timed_metric "boxed CGA3 odd-to-full widening")"
direct_odd_to_full_widening_ns="$(get_timed_metric "direct CGA3 odd-to-full widening")"
full_grade2_projection_speedup="$(ratio "$boxed_full_grade2_projection_ns" \
  "$direct_full_grade2_projection_ns")"
even_grade2_projection_speedup="$(ratio "$boxed_even_grade2_projection_ns" \
  "$direct_even_grade2_projection_ns")"
odd_grade3_projection_speedup="$(ratio "$boxed_odd_grade3_projection_ns" \
  "$direct_odd_grade3_projection_ns")"
even_part_speedup="$(ratio "$boxed_even_part_ns" "$direct_even_part_ns")"
odd_part_speedup="$(ratio "$boxed_odd_part_ns" "$direct_odd_part_ns")"
even_to_full_widening_speedup="$(ratio "$boxed_even_to_full_widening_ns" \
  "$direct_even_to_full_widening_ns")"
odd_to_full_widening_speedup="$(ratio "$boxed_odd_to_full_widening_ns" \
  "$direct_odd_to_full_widening_ns")"

check_le "PGA3 motor point transform diff" "$motor_point_diff" "$max_correctness_diff" ""
check_le "Packed PGA3 motor point transform" "$packed_motor_ns" "$max_packed_motor_ns" "ns/iter"
check_ge "PGA3 motor point transform speedup" "$motor_speedup" "$min_motor_speedup" "x"
check_le "Packed direct subtraction" "$direct_subtraction_ns" \
  "$max_packed_subtraction_ns" "ns/iter"
check_ge "Packed subtraction speedup" "$subtraction_speedup" \
  "$min_subtraction_speedup" "x"
check_le "Packed direct addition" "$direct_add_ns" "$max_packed_add_ns" "ns/iter"
check_ge "Packed addition speedup" "$add_speedup" "$min_packed_add_speedup" "x"
check_le "Packed direct negation" "$direct_neg_ns" "$max_packed_neg_ns" "ns/iter"
check_ge "Packed negation speedup" "$neg_speedup" "$min_packed_neg_speedup" "x"
check_le "Packed direct scalar multiplication" "$direct_smul_ns" \
  "$max_packed_smul_ns" "ns/iter"
check_ge "Packed scalar multiplication speedup" "$smul_speedup" \
  "$min_packed_smul_speedup" "x"

unary_diff_labels=(
  "reverse full" "reverse even" "reverse odd"
  "involute full" "involute even" "involute odd"
  "conjugate full" "conjugate even" "conjugate odd"
)
unary_diffs=(
  "$reverse_full_diff" "$reverse_even_diff" "$reverse_odd_diff"
  "$involute_full_diff" "$involute_even_diff" "$involute_odd_diff"
  "$conjugate_full_diff" "$conjugate_even_diff" "$conjugate_odd_diff"
)
unary_speedups=(
  "$reverse_full_speedup" "$reverse_even_speedup" "$reverse_odd_speedup"
  "$involute_full_speedup" "$involute_even_speedup" "$involute_odd_speedup"
  "$conjugate_full_speedup" "$conjugate_even_speedup" "$conjugate_odd_speedup"
)
for ((i = 0; i < ${#unary_diff_labels[@]}; i++)); do
  label="Packed ${unary_diff_labels[$i]}"
  check_le "$label baseline diff" "${unary_diffs[$i]}" "$max_correctness_diff" ""
  check_ge "$label speedup" "${unary_speedups[$i]}" "$min_packed_unary_speedup" "x"
done
check_le "Packed full reverse" "$direct_reverse_full_ns" \
  "$max_packed_full_unary_ns" "ns/iter"
check_le "Packed full involute" "$direct_involute_full_ns" \
  "$max_packed_full_unary_ns" "ns/iter"
check_le "Packed full conjugate" "$direct_conjugate_full_ns" \
  "$max_packed_full_unary_ns" "ns/iter"
check_le "Packed even reverse" "$direct_reverse_even_ns" \
  "$max_packed_parity_unary_ns" "ns/iter"
check_le "Packed odd reverse" "$direct_reverse_odd_ns" \
  "$max_packed_parity_unary_ns" "ns/iter"
check_le "Packed even conjugate" "$direct_conjugate_even_ns" \
  "$max_packed_parity_unary_ns" "ns/iter"
check_le "Packed odd conjugate" "$direct_conjugate_odd_ns" \
  "$max_packed_parity_unary_ns" "ns/iter"
check_le "Packed even involute" "$direct_involute_even_ns" \
  "$max_packed_even_involute_ns" "ns/iter"
check_le "Packed odd involute" "$direct_involute_odd_ns" \
  "$max_packed_odd_involute_ns" "ns/iter"
check_le "Packed Hodge dual baseline diff" "$hodge_dual_diff" \
  "$max_correctness_diff" ""
check_le "Packed Hodge dual" "$direct_hodge_dual_ns" \
  "$max_packed_hodge_ns" "ns/iter"
check_ge "Packed Hodge dual speedup" "$hodge_dual_speedup" \
  "$min_packed_hodge_speedup" "x"

projection_diff_labels=(
  "full grade-2 projection" "even grade-2 projection" "odd grade-3 projection"
  "even part" "odd part" "even-to-full widening" "odd-to-full widening"
)
projection_diffs=(
  "$projection_full_grade2_diff" "$projection_even_grade2_diff"
  "$projection_odd_grade3_diff" "$projection_even_part_diff"
  "$projection_odd_part_diff" "$widening_even_to_full_diff"
  "$widening_odd_to_full_diff"
)
projection_speedups=(
  "$full_grade2_projection_speedup" "$even_grade2_projection_speedup"
  "$odd_grade3_projection_speedup" "$even_part_speedup" "$odd_part_speedup"
  "$even_to_full_widening_speedup" "$odd_to_full_widening_speedup"
)
for ((i = 0; i < ${#projection_diff_labels[@]}; i++)); do
  label="Packed ${projection_diff_labels[$i]}"
  check_le "$label baseline diff" "${projection_diffs[$i]}" \
    "$max_correctness_diff" ""
  check_ge "$label speedup" "${projection_speedups[$i]}" \
    "$min_packed_projection_speedup" "x"
done
check_le "Packed full grade-2 projection" "$direct_full_grade2_projection_ns" \
  "$max_packed_full_projection_ns" "ns/iter"
check_le "Packed even grade-2 projection" "$direct_even_grade2_projection_ns" \
  "$max_packed_half_projection_ns" "ns/iter"
check_le "Packed odd grade-3 projection" "$direct_odd_grade3_projection_ns" \
  "$max_packed_half_projection_ns" "ns/iter"
check_le "Packed even part" "$direct_even_part_ns" \
  "$max_packed_half_projection_ns" "ns/iter"
check_le "Packed odd part" "$direct_odd_part_ns" \
  "$max_packed_half_projection_ns" "ns/iter"
check_le "Packed even-to-full widening" "$direct_even_to_full_widening_ns" \
  "$max_packed_widening_ns" "ns/iter"
check_le "Packed odd-to-full widening" "$direct_odd_to_full_widening_ns" \
  "$max_packed_widening_ns" "ns/iter"

status="passed"
if [[ ${#failures[@]} -ne 0 ]]; then
  status="failed"
fi
write_summary_json "$status"

if [[ ${#failures[@]} -ne 0 ]]; then
  printf 'packed MV benchmark guard failed; benchmark log: %s\n' "$bench_log" >&2
  printf 'benchmark summary: %s\n' "$summary_json" >&2
  for failure in "${failures[@]}"; do
    printf '  - %s\n' "$failure" >&2
  done
  exit 1
fi

printf 'packed MV benchmark guard passed; benchmark log: %s\n' "$bench_log"
printf 'benchmark summary: %s\n' "$summary_json"
printf '  PGA3 motor point diff: %s\n' "$motor_point_diff"
printf '  PGA3 motor point: %s ns/iter packed vs %s ns/iter dense (%sx)\n' \
  "$packed_motor_ns" "$dense_motor_ns" "$motor_speedup"
printf '  Packed subtraction: %s ns/iter direct vs %s ns/iter add-neg (%sx)\n' \
  "$direct_subtraction_ns" "$composed_subtraction_ns" "$subtraction_speedup"
printf '  Packed addition: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
  "$direct_add_ns" "$boxed_add_ns" "$add_speedup"
printf '  Packed negation: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
  "$direct_neg_ns" "$boxed_neg_ns" "$neg_speedup"
printf '  Packed scalar multiplication: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
  "$direct_smul_ns" "$boxed_smul_ns" "$smul_speedup"
unary_boxed_ns=(
  "$boxed_reverse_full_ns" "$boxed_reverse_even_ns" "$boxed_reverse_odd_ns"
  "$boxed_involute_full_ns" "$boxed_involute_even_ns" "$boxed_involute_odd_ns"
  "$boxed_conjugate_full_ns" "$boxed_conjugate_even_ns" "$boxed_conjugate_odd_ns"
)
unary_direct_ns=(
  "$direct_reverse_full_ns" "$direct_reverse_even_ns" "$direct_reverse_odd_ns"
  "$direct_involute_full_ns" "$direct_involute_even_ns" "$direct_involute_odd_ns"
  "$direct_conjugate_full_ns" "$direct_conjugate_even_ns" "$direct_conjugate_odd_ns"
)
for ((i = 0; i < ${#unary_diff_labels[@]}; i++)); do
  printf '  Packed %s: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
    "${unary_diff_labels[$i]}" "${unary_direct_ns[$i]}" \
    "${unary_boxed_ns[$i]}" "${unary_speedups[$i]}"
done
printf '  Packed Hodge dual: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
  "$direct_hodge_dual_ns" "$boxed_hodge_dual_ns" "$hodge_dual_speedup"
projection_boxed_ns=(
  "$boxed_full_grade2_projection_ns" "$boxed_even_grade2_projection_ns"
  "$boxed_odd_grade3_projection_ns" "$boxed_even_part_ns" "$boxed_odd_part_ns"
  "$boxed_even_to_full_widening_ns" "$boxed_odd_to_full_widening_ns"
)
projection_direct_ns=(
  "$direct_full_grade2_projection_ns" "$direct_even_grade2_projection_ns"
  "$direct_odd_grade3_projection_ns" "$direct_even_part_ns" "$direct_odd_part_ns"
  "$direct_even_to_full_widening_ns" "$direct_odd_to_full_widening_ns"
)
for ((i = 0; i < ${#projection_diff_labels[@]}; i++)); do
  printf '  Packed %s: %s ns/iter direct vs %s ns/iter boxed (%sx)\n' \
    "${projection_diff_labels[$i]}" "${projection_direct_ns[$i]}" \
    "${projection_boxed_ns[$i]}" "${projection_speedups[$i]}"
done
