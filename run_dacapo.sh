#!/usr/bin/env bash
set -u

JAVA_BIN="./build/linux-x86_64-server-release/jdk/bin/java"
JAR_PATH="../../test/benchmark/dacapo/dacapo-23.11-MR2-chopin.jar"

LOG_DIR="dacapo_logs"
mkdir -p "$LOG_DIR"

TIMEOUT="15m"

JAVA_OPTS=(
  "-Xlog:gc+task"
  "-Djava.security.manager=allow"
)

BENCHMARKS=(
	avrora
	batik
	biojava
	cassandra
	eclipse
	fop
	graphchi
	eclipse
	h2
	h2o
	jme
	jython
	kafka
	luindex
	lusearch
	pmd
	spring
	sunflow
	tomcat
	zxing
	xalan
)

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
	
  rm -rf scratch hs_*
done

echo "All benchmarks finished."
