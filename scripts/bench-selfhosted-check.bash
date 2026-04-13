#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${FO_BENCH_BIN:-$ROOT/build/fo-selfhosted}"
TIMING_MODE="${FO_TIMING_MODE:-packages}"
OUT_DIR="${FO_BENCH_OUT_DIR:-$ROOT/.fo-cache/benchmarks}"
ITERATIONS="${FO_BENCH_ITERATIONS:-1}"
COLD_MODE="${FO_BENCH_COLD:-0}"
SUMMARY_PHASE="${FO_BENCH_PHASE:-command_total}"
REBUILD_MODE="${FO_BENCH_REBUILD:-0}"
REBUILD_SCRIPT="${FO_BENCH_REBUILD_SCRIPT:-$ROOT/scripts/build-selfhosted-cli.sh}"
DEFAULT_SELFHOSTED_BIN="$ROOT/build/fo-selfhosted"
REBUILD_SEED_BIN="${FO_BENCH_REBUILD_SEED:-$BIN}"

if [[ "$REBUILD_MODE" != "0" && "$REBUILD_MODE" != "1" ]]; then
  echo "FO_BENCH_REBUILD must be 0 or 1, got: $REBUILD_MODE" >&2
  exit 1
fi

if [[ "$REBUILD_MODE" == "0" && ! -x "$BIN" ]]; then
  echo "missing compiler binary: $BIN" >&2
  exit 1
fi

if ! [[ "$ITERATIONS" =~ ^[1-9][0-9]*$ ]]; then
  echo "FO_BENCH_ITERATIONS must be a positive integer, got: $ITERATIONS" >&2
  exit 1
fi

if [[ "$COLD_MODE" != "0" && "$COLD_MODE" != "1" ]]; then
  echo "FO_BENCH_COLD must be 0 or 1, got: $COLD_MODE" >&2
  exit 1
fi

if [[ "$REBUILD_MODE" == "1" ]]; then
  if [[ "$BIN" != "$DEFAULT_SELFHOSTED_BIN" ]]; then
    echo "FO_BENCH_REBUILD=1 currently requires FO_BENCH_BIN=$DEFAULT_SELFHOSTED_BIN" >&2
    exit 1
  fi
  if [[ ! -x "$REBUILD_SEED_BIN" ]]; then
    echo "missing rebuild seed compiler: $REBUILD_SEED_BIN" >&2
    exit 1
  fi
  if [[ ! -f "$REBUILD_SCRIPT" ]]; then
    echo "missing rebuild script: $REBUILD_SCRIPT" >&2
    exit 1
  fi
fi

if [[ $# -eq 0 ]]; then
  TARGETS=(./cmd/...)
else
  TARGETS=("$@")
fi

mkdir -p "$OUT_DIR"

stamp="$(date +%Y%m%d-%H%M%S-%N)"
slug="$(printf '%s\n' "${TARGETS[@]}" | tr ' /:' '_' | tr -s '_' '-')"
phase_slug="$(printf '%s\n' "$SUMMARY_PHASE" | tr ' /:' '_' | tr -s '_' '-')"
prefix="check-${slug}-${phase_slug}-${stamp}-pid$$"
log_path="$OUT_DIR/${prefix}.log"
summary_path="$OUT_DIR/${prefix}.summary"

time_cmd=()
if [[ -x /usr/bin/time ]]; then
  time_cmd=(/usr/bin/time -f 'wall=%E user=%U sys=%S maxrss_kb=%M')
fi

duration_to_us() {
  perl -e '
    my $d = shift;
    if ($d =~ /^([0-9.]+)ns$/) { printf "%.6f", $1 / 1000; exit 0; }
    if ($d =~ /^([0-9.]+)µs$/) { printf "%.6f", $1; exit 0; }
    if ($d =~ /^([0-9.]+)ms$/) { printf "%.6f", $1 * 1000; exit 0; }
    if ($d =~ /^([0-9.]+)s$/)  { printf "%.6f", $1 * 1000000; exit 0; }
    die "unsupported duration: $d\n";
  ' "$1"
}

format_us() {
  perl -e '
    my $us = shift;
    if ($us >= 1000000) { printf "%.3fs", $us / 1000000; exit 0; }
    if ($us >= 1000)    { printf "%.3fms", $us / 1000; exit 0; }
    printf "%.3fµs", $us;
  ' "$1"
}

extract_phase_elapsed() {
  local path="$1"
  local phase="$2"
  local line
  line="$(grep -E "fo timing: ${phase} elapsed=" "$path" | tail -n 1 || true)"
  if [[ -z "$line" ]]; then
    return 1
  fi
  sed -E 's/.*elapsed=([^ ]+).*/\1/' <<<"$line"
}

echo "benchmark bin: $BIN"
echo "benchmark targets: ${TARGETS[*]}"
echo "benchmark timing: $TIMING_MODE"
echo "benchmark iterations: $ITERATIONS"
echo "benchmark cache_mode: $([[ "$COLD_MODE" == "1" ]] && echo cold || echo ambient)"
echo "benchmark summary_phase: $SUMMARY_PHASE"
echo "benchmark rebuild: $([[ "$REBUILD_MODE" == "1" ]] && echo enabled || echo disabled)"
if [[ "$REBUILD_MODE" == "1" ]]; then
  echo "benchmark rebuild_script: $REBUILD_SCRIPT"
  echo "benchmark rebuild_seed: $REBUILD_SEED_BIN"
fi
echo "benchmark log: $log_path"
echo "benchmark summary: $summary_path"

if [[ "$REBUILD_MODE" == "1" ]]; then
  echo "benchmark rebuilding: $BIN"
  (
    cd "$ROOT"
    env FO_BIN="$REBUILD_SEED_BIN" "$REBUILD_SCRIPT"
  )
fi

phase_rows=()
: > "$log_path"

for ((run = 1; run <= ITERATIONS; run++)); do
  run_log="$OUT_DIR/${prefix}-run${run}.log"
  cache_root=""
  env_cmd=(env FO_TIMING="$TIMING_MODE")
  if [[ "$COLD_MODE" == "1" ]]; then
    cache_root="$(mktemp -d "$ROOT/.cold-bench.XXXXXX")"
    env_cmd+=(FO_CACHE_ROOT="$cache_root")
  fi

  {
    echo "== run $run/$ITERATIONS =="
    if [[ -n "$cache_root" ]]; then
      echo "cache_root=$cache_root"
    fi
    (
      cd "$ROOT"
      "${env_cmd[@]}" "${time_cmd[@]}" "$BIN" check "${TARGETS[@]}"
    )
    echo
  } 2>&1 | tee "$run_log"

  cat "$run_log" >> "$log_path"

  if phase_value="$(extract_phase_elapsed "$run_log" "$SUMMARY_PHASE")"; then
    phase_rows+=("$(duration_to_us "$phase_value")"$'\t'"$phase_value")
  else
    echo "warning: missing phase '$SUMMARY_PHASE' in $run_log" | tee -a "$log_path"
  fi

  if [[ -n "$cache_root" ]]; then
    rm -rf "$cache_root"
  fi
done

if [[ ${#phase_rows[@]} -gt 0 ]]; then
  sorted_rows="$(mktemp)"
  printf '%s\n' "${phase_rows[@]}" | sort -n > "$sorted_rows"
  run_count="${#phase_rows[@]}"
  median_index=$(( (run_count + 1) / 2 ))
  best_raw="$(awk -F '\t' 'NR == 1 { print $2 }' "$sorted_rows")"
  median_raw="$(awk -F '\t' -v target="$median_index" 'NR == target { print $2 }' "$sorted_rows")"
  worst_raw="$(awk -F '\t' 'END { print $2 }' "$sorted_rows")"
  avg_us="$(awk -F '\t' '{ sum += $1 } END { if (NR > 0) printf "%.6f", sum / NR }' "$sorted_rows")"

  {
    echo "summary phase: $SUMMARY_PHASE"
    echo "summary runs: $run_count"
    echo "summary best: $best_raw"
    echo "summary median: $median_raw"
    echo "summary average: $(format_us "$avg_us")"
    echo "summary worst: $worst_raw"
  } | tee "$summary_path"

  rm -f "$sorted_rows"
fi

echo "saved benchmark log: $log_path"
echo "saved benchmark summary: $summary_path"
