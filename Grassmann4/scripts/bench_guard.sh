#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg_root="$(cd "$script_dir/.." && pwd)"

for tool in lake awk sed; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$tool" >&2
    exit 1
  fi
done

max_correctness_diff="${MAX_BENCH_CORRECTNESS_DIFF:-1e-8}"
max_mv_rotor_ns="${MAX_MV_ROTOR_NS:-500}"
max_mv_sandwich_ns="${MAX_MV_SANDWICH_NS:-300}"
max_mv_motor_ns="${MAX_MV_MOTOR_NS:-2500}"
max_kernel_grad_ns="${MAX_KERNEL_GRAD_NS:-2500}"
min_rotor_speedup="${MIN_ROTOR_SPEEDUP:-40}"
min_sandwich_speedup="${MIN_SANDWICH_SPEEDUP:-150}"
min_gradient_speedup="${MIN_GRADIENT_SPEEDUP:-3}"

bench_log="${BENCH_GUARD_LOG:-}"
if [[ -z "$bench_log" ]]; then
  bench_log="$(mktemp "${TMPDIR:-/tmp}/grassmann-bench.XXXXXX")"
fi

summary_json="${BENCH_GUARD_SUMMARY:-$bench_log.summary.json}"

numeric_le() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual <= expected ? 0 : 1) }'
}

numeric_ge() {
  awk -v actual="$1" -v expected="$2" 'BEGIN { exit(actual >= expected ? 0 : 1) }'
}

ratio() {
  awk -v numerator="$1" -v denominator="$2" \
    'BEGIN { if (denominator == 0) exit 1; printf "%.1f", numerator / denominator }'
}

extract_value() {
  local label="$1"
  awk -F ': ' -v label="$label" '
    $1 == label {
      split($2, parts, " ")
      print parts[1]
      found = 1
    }
    END { if (!found) exit 1 }
  ' "$bench_log"
}

get_metric() {
  local label="$1"
  local value
  if ! value="$(extract_value "$label")"; then
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
    printf '    "max_mv_rotor_ns": %s,\n' "$max_mv_rotor_ns"
    printf '    "max_mv_sandwich_ns": %s,\n' "$max_mv_sandwich_ns"
    printf '    "max_mv_motor_ns": %s,\n' "$max_mv_motor_ns"
    printf '    "max_kernel_grad_ns": %s,\n' "$max_kernel_grad_ns"
    printf '    "min_rotor_speedup": %s,\n' "$min_rotor_speedup"
    printf '    "min_sandwich_speedup": %s,\n' "$min_sandwich_speedup"
    printf '    "min_gradient_speedup": %s\n' "$min_gradient_speedup"
    printf '  },\n'
    printf '  "metrics": {\n'
    printf '    "mv_rotor_diff": %s,\n' "$rotor_diff"
    printf '    "mv_sandwich_diff": %s,\n' "$sandwich_diff"
    printf '    "naive_rotor_ns": %s,\n' "$naive_rotor_ns"
    printf '    "mv_rotor_ns": %s,\n' "$mv_rotor_ns"
    printf '    "naive_sandwich_ns": %s,\n' "$naive_sandwich_ns"
    printf '    "mv_sandwich_ns": %s,\n' "$mv_sandwich_ns"
    printf '    "mv_motor_ns": %s,\n' "$mv_motor_ns"
    printf '    "finite_diff_grad_ns": %s,\n' "$finite_diff_grad_ns"
    printf '    "kernel_grad_ns": %s\n' "$kernel_grad_ns"
    printf '  },\n'
    printf '  "speedups": {\n'
    printf '    "rotor": %s,\n' "$rotor_speedup"
    printf '    "sandwich": %s,\n' "$sandwich_speedup"
    printf '    "gradient": %s\n' "$gradient_speedup"
    printf '  }\n'
    printf '}\n'
  } > "$summary_json"
}

cd "$pkg_root"
if ! lake exe bench > "$bench_log" 2>&1; then
  printf 'lake exe bench failed; benchmark log follows:\n' >&2
  cat "$bench_log" >&2
  exit 1
fi

rotor_diff="$(get_metric "MV rotor diff")"
sandwich_diff="$(get_metric "MV sandwich diff")"
naive_rotor_ns="$(get_metric "Naive rotor (Multivector)")"
mv_rotor_ns="$(get_metric "MV rotor (DataArray)")"
naive_sandwich_ns="$(get_metric "Naive sandwich (Multivector)")"
mv_sandwich_ns="$(get_metric "MV sandwich (DataArray)")"
mv_motor_ns="$(get_metric "MV motor mul (PGA3)")"
finite_diff_grad_ns="$(get_metric "Finite diff gradient")"
kernel_grad_ns="$(get_metric "Compile-time kernel gradient (R3)")"

rotor_speedup="$(ratio "$naive_rotor_ns" "$mv_rotor_ns")"
sandwich_speedup="$(ratio "$naive_sandwich_ns" "$mv_sandwich_ns")"
gradient_speedup="$(ratio "$finite_diff_grad_ns" "$kernel_grad_ns")"

check_le "MV rotor diff" "$rotor_diff" "$max_correctness_diff" ""
check_le "MV sandwich diff" "$sandwich_diff" "$max_correctness_diff" ""
check_le "MV rotor" "$mv_rotor_ns" "$max_mv_rotor_ns" "ns/iter"
check_le "MV sandwich" "$mv_sandwich_ns" "$max_mv_sandwich_ns" "ns/iter"
check_le "MV motor" "$mv_motor_ns" "$max_mv_motor_ns" "ns/iter"
check_le "Kernel gradient" "$kernel_grad_ns" "$max_kernel_grad_ns" "ns/iter"
check_ge "Rotor speedup" "$rotor_speedup" "$min_rotor_speedup" "x"
check_ge "Sandwich speedup" "$sandwich_speedup" "$min_sandwich_speedup" "x"
check_ge "Gradient speedup" "$gradient_speedup" "$min_gradient_speedup" "x"

status="passed"
if [[ ${#failures[@]} -ne 0 ]]; then
  status="failed"
fi
write_summary_json "$status"

if [[ ${#failures[@]} -ne 0 ]]; then
  printf 'benchmark guard failed; benchmark log: %s\n' "$bench_log" >&2
  printf 'benchmark summary: %s\n' "$summary_json" >&2
  for failure in "${failures[@]}"; do
    printf '  - %s\n' "$failure" >&2
  done
  exit 1
fi

printf 'benchmark guard passed; benchmark log: %s\n' "$bench_log"
printf 'benchmark summary: %s\n' "$summary_json"
printf '  correctness diffs: rotor=%s sandwich=%s\n' "$rotor_diff" "$sandwich_diff"
printf '  rotor: %s ns/iter MV vs %s ns/iter dense (%sx)\n' \
  "$mv_rotor_ns" "$naive_rotor_ns" "$rotor_speedup"
printf '  sandwich: %s ns/iter MV vs %s ns/iter dense (%sx)\n' \
  "$mv_sandwich_ns" "$naive_sandwich_ns" "$sandwich_speedup"
printf '  motor: %s ns/iter MV\n' "$mv_motor_ns"
printf '  gradient: %s ns/iter kernel vs %s ns/iter finite diff (%sx)\n' \
  "$kernel_grad_ns" "$finite_diff_grad_ns" "$gradient_speedup"
