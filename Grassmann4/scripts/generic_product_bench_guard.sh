#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
pkg_root="${GRASSMANN_LAKE_ROOT:-$repo_root}"

if [[ ! -f "$pkg_root/lakefile.toml" || ! -f "$pkg_root/lean-toolchain" ]]; then
  printf 'invalid Grassmann Lake root: %s\n' "$pkg_root" >&2
  exit 1
fi

for tool in lake awk sort tail; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'missing required tool: %s\n' "$tool" >&2
    exit 1
  fi
done

iters="${GENERIC_PRODUCT_BENCH_ITERS:-100}"
repeats="${GENERIC_PRODUCT_BENCH_REPEATS:-5}"
max_correctness_diff="${MAX_GENERIC_PRODUCT_CORRECTNESS_DIFF:-1e-6}"

# A forward/rewrite ratio of 0.8 permits normal timing noise and at most a 25%
# slowdown relative to the retained pre-rewrite algorithm. Larger median
# slowdowns are material for a performance-motivated kernel rewrite.
min_forward_over_rewritten="${MIN_GENERIC_PRODUCT_FORWARD_OVER_REWRITTEN:-0.80}"
min_dense_over_rewritten="${MIN_GENERIC_PRODUCT_DENSE_OVER_REWRITTEN:-1.00}"

is_positive_integer() {
  awk -v value="$1" 'BEGIN {
    exit(value ~ /^[0-9]+$/ && value + 0 > 0 ? 0 : 1)
  }'
}

if ! is_positive_integer "$iters"; then
  printf 'GENERIC_PRODUCT_BENCH_ITERS must be a positive integer: %s\n' \
    "$iters" >&2
  exit 1
fi

if ! is_positive_integer "$repeats" || (( repeats < 3 || repeats % 2 == 0 )); then
  printf 'GENERIC_PRODUCT_BENCH_REPEATS must be an odd integer >= 3: %s\n' \
    "$repeats" >&2
  exit 1
fi

if [[ -n "${GENERIC_PRODUCT_BENCH_LOG_DIR:-}" ]]; then
  log_dir="$GENERIC_PRODUCT_BENCH_LOG_DIR"
  mkdir -p "$log_dir"
else
  log_dir="$(mktemp -d "${TMPDIR:-/tmp}/grassmann-generic-products.XXXXXX")"
  cleanup_log_dir=1
fi

cleanup() {
  if [[ "${cleanup_log_dir:-0}" == 1 && -d "$log_dir" ]]; then
    rm -rf "$log_dir"
  fi
}
trap cleanup EXIT

ratios_tsv="$log_dir/ratios.tsv"
: > "$ratios_tsv"

expected_cases=$((3 * 9 * 4))

cd "$pkg_root"

for ((run = 1; run <= repeats; run++)); do
  run_log="$log_dir/run-${run}.log"
  printf 'generic product benchmark run %d/%d (%s iterations)\n' \
    "$run" "$repeats" "$iters"

  if ! lake exe packedmvbench generic-products "$iters" > "$run_log" 2>&1; then
    printf 'generic product benchmark run %d failed; tail follows:\n' "$run" >&2
    tail -n 200 "$run_log" >&2
    exit 1
  fi

  if ! awk -v expected="$expected_cases" -v maximum="$max_correctness_diff" '
    function numeric(value) {
      return value ~ /^-?([0-9]+([.][0-9]*)?|[.][0-9]+)([eE][-+]?[0-9]+)?$/
    }

    /^GENERIC_PRODUCT_CHECK / {
      delete field
      for (i = 2; i <= NF; i++) {
        split($i, pair, "=")
        field[pair[1]] = pair[2]
      }
      key = field["signature"] "/" field["layout"] "/" field["op"]
      seen[key]++
      count++
      names[1] = "rewritten_forward_l1"
      names[2] = "rewritten_dense_l1"
      names[3] = "forward_dense_l1"
      names[4] = "rewritten_forward_checksum_diff"
      names[5] = "rewritten_dense_checksum_diff"
      names[6] = "forward_dense_checksum_diff"
      for (j = 1; j <= 6; j++) {
        name = names[j]
        value = field[name]
        if (!numeric(value) || value + 0 < 0 || value + 0 > maximum) {
          printf "FAIL correctness %s %s=%s (maximum %s)\n", \
            key, name, value, maximum > "/dev/stderr"
          failed = 1
        }
      }
    }

    END {
      if (count != expected) {
        printf "FAIL expected %d correctness records, found %d\n", \
          expected, count > "/dev/stderr"
        failed = 1
      }
      for (key in seen) {
        if (seen[key] != 1) {
          printf "FAIL duplicate correctness record %s (%d copies)\n", \
            key, seen[key] > "/dev/stderr"
          failed = 1
        }
      }
      exit failed
    }
  ' "$run_log"; then
    printf 'correctness validation failed in run %d; log: %s\n' \
      "$run" "$run_log" >&2
    exit 1
  fi

  run_ratios="$log_dir/run-${run}-ratios.tsv"
  if ! awk -v expected="$expected_cases" -v run="$run" '
    function numeric(value) {
      return value ~ /^-?([0-9]+([.][0-9]*)?|[.][0-9]+)([eE][-+]?[0-9]+)?$/
    }

    /^GENERIC_PRODUCT_RATIO / {
      delete field
      for (i = 2; i <= NF; i++) {
        split($i, pair, "=")
        field[pair[1]] = pair[2]
      }
      key = field["signature"] "/" field["layout"] "/" field["op"]
      forward = field["forward_over_rewritten"]
      dense = field["dense_over_rewritten"]
      if (!numeric(forward) || !numeric(dense) || forward + 0 <= 0 || dense + 0 <= 0) {
        printf "FAIL invalid timing ratio %s forward=%s dense=%s\n", \
          key, forward, dense > "/dev/stderr"
        failed = 1
      }
      seen[key]++
      count++
      printf "%d\t%s\t%s\t%s\t%s\t%s\n", run, field["signature"], \
        field["layout"], field["op"], forward, dense
    }

    END {
      if (count != expected) {
        printf "FAIL expected %d ratio records, found %d\n", \
          expected, count > "/dev/stderr"
        failed = 1
      }
      for (key in seen) {
        if (seen[key] != 1) {
          printf "FAIL duplicate ratio record %s (%d copies)\n", \
            key, seen[key] > "/dev/stderr"
          failed = 1
        }
      }
      exit failed
    }
  ' "$run_log" > "$run_ratios"; then
    printf 'ratio extraction failed in run %d; log: %s\n' \
      "$run" "$run_log" >&2
    exit 1
  fi
  cat "$run_ratios" >> "$ratios_tsv"
done

median_report="$log_dir/medians.tsv"
if ! awk -F '\t' -v repeats="$repeats" \
    -v min_forward="$min_forward_over_rewritten" \
    -v min_dense="$min_dense_over_rewritten" '
  {
    key = $2 SUBSEP $3 SUBSEP $4
    signature[key] = $2
    layout[key] = $3
    operation[key] = $4

    nextIndex = count[key] + 1
    value = $5 + 0
    insertAt = nextIndex
    while (insertAt > 1 && forward[key, insertAt - 1] > value) {
      forward[key, insertAt] = forward[key, insertAt - 1]
      insertAt--
    }
    forward[key, insertAt] = value

    value = $6 + 0
    insertAt = nextIndex
    while (insertAt > 1 && dense[key, insertAt - 1] > value) {
      dense[key, insertAt] = dense[key, insertAt - 1]
      insertAt--
    }
    dense[key, insertAt] = value
    count[key] = nextIndex
  }

  END {
    medianIndex = (repeats + 1) / 2
    for (key in count) {
      if (count[key] != repeats) {
        printf "FAIL %s/%s/%s has %d ratios, expected %d\n", \
          signature[key], layout[key], operation[key], count[key], repeats \
          > "/dev/stderr"
        failed = 1
        continue
      }
      forwardMedian = forward[key, medianIndex]
      denseMedian = dense[key, medianIndex]
      printf "%s\t%s\t%s\t%.6f\t%.6f\n", signature[key], layout[key], \
        operation[key], forwardMedian, denseMedian
      if (forwardMedian < min_forward) {
        printf "FAIL %s/%s/%s median forward/rewrite %.6f below %.6f\n", \
          signature[key], layout[key], operation[key], forwardMedian, \
          min_forward > "/dev/stderr"
        failed = 1
      }
      if (denseMedian < min_dense) {
        printf "FAIL %s/%s/%s median dense/rewrite %.6f below %.6f\n", \
          signature[key], layout[key], operation[key], denseMedian, \
          min_dense > "/dev/stderr"
        failed = 1
      }
    }
    exit failed
  }
' "$ratios_tsv" > "$median_report"; then
  printf 'generic product median guard failed\n' >&2
  if [[ -n "${GENERIC_PRODUCT_BENCH_LOG_DIR:-}" ]]; then
    printf 'logs retained in: %s\n' "$log_dir" >&2
  fi
  exit 1
fi

sort -t $'\t' -k1,1 -k2,2 -k3,3 "$median_report" |
  awk -F '\t' '{
    printf "PASS %-4s %-9s %-5s median forward/rewrite=%8.3fx dense/rewrite=%8.3fx\n", \
      $1, $2, $3, $4, $5
  }'

printf 'PASS generic product guard: %d cases, %d-run medians, correctness <= %s\n' \
  "$expected_cases" "$repeats" "$max_correctness_diff"

