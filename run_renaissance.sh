#!/usr/bin/env bash
set -u

JAVA_BIN="./build/linux-x86_64-server-release/jdk/bin/java"
JAR_PATH="../../test/benchmark/renaissance-gpl-0.16.1.jar"

LOG_DIR="renaissance_logs"
mkdir -p "$LOG_DIR"

TIMEOUT="15m"

JAVA_OPTS=(
  "-Xlog:gc+task"
  "-Djava.security.manager=allow"
)

BENCHMARKS=(
  scrabble
  page-rank
  future-genetic
  movie-lens
  scala-doku
  chi-square
  fj-kmeans
  rx-scrabble
  db-shootout
  neo4j-analytics
  finagle-http
  dec-tree
  naive-bayes
  als
  par-mnemonics
  scala-kmeans
  philosophers
  log-regression
  gauss-mix
  mnemonics
  dotty
  finagle-chirper
  reactors
  scala-stm-bench7
)
# akka-uct not run

for bench in "${BENCHMARKS[@]}"; do
  echo "============================================================"
  echo "Running benchmark: $bench"
  echo "Start time: $(date)"
  echo "Timeout: $TIMEOUT"
  echo "============================================================"

  LOG_FILE="$LOG_DIR/${bench}.log"

  timeout "$TIMEOUT" \
    "$JAVA_BIN" \
    "${JAVA_OPTS[@]}" \
    -jar "$JAR_PATH" \
    "$bench" \
    > "$LOG_FILE" 2>&1

  status=$?

  if [ $status -eq 0 ]; then
    echo "[OK] $bench finished successfully"
  elif [ $status -eq 124 ]; then
    echo "[TIMEOUT] $bench exceeded $TIMEOUT, marked as FAIL"
    echo "[TIMEOUT] exceeded $TIMEOUT" >> "$LOG_FILE"
  else
    echo "[FAILED] $bench exited with status $status"
  fi

  echo "End time: $(date)"
  echo
	
  rm -rf harness-* hs_*
done

echo "All benchmarks finished."
