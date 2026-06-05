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

smoke_iters="${PACKED_MV_BENCH_SMOKE_ITERS:-200}"
motor_iters="${PACKED_MV_BENCH_MOTOR_ITERS:-5000}"
max_correctness_diff="${MAX_PACKED_MV_CORRECTNESS_DIFF:-1e-6}"
max_packed_motor_ns="${MAX_PACKED_PGA_MOTOR_POINT_NS:-20000}"
min_motor_speedup="${MIN_PACKED_PGA_MOTOR_POINT_SPEEDUP:-5}"

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
    'BEGIN { if (denominator == 0) exit 1; printf "%.1f", numerator / denominator }'
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
    printf '    "min_motor_speedup": %s\n' "$min_motor_speedup"
    printf '  },\n'
    printf '  "metrics": {\n'
    printf '    "pga_motor_point_diff": %s,\n' "$motor_point_diff"
    printf '    "dense_motor_point_ns": %s,\n' "$dense_motor_ns"
    printf '    "packed_motor_point_ns": %s\n' "$packed_motor_ns"
    printf '  },\n'
    printf '  "speedups": {\n'
    printf '    "pga_motor_point": %s\n' "$motor_speedup"
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

motor_point_diff="$(get_last_metric "PGA3 motor point transform")"
dense_motor_ns="$(get_timed_metric "dense motor point transform")"
packed_motor_ns="$(get_timed_metric "packed MV motor point transform")"
motor_speedup="$(ratio "$dense_motor_ns" "$packed_motor_ns")"

check_le "PGA3 motor point transform diff" "$motor_point_diff" "$max_correctness_diff" ""
check_le "Packed PGA3 motor point transform" "$packed_motor_ns" "$max_packed_motor_ns" "ns/iter"
check_ge "PGA3 motor point transform speedup" "$motor_speedup" "$min_motor_speedup" "x"

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
