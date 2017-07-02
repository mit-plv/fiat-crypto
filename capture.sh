#!/bin/sh
set -eu

machine=$(etc/machine.sh)
freq=$(etc/freq.sh)
compiler=$($1/compiler.sh -dumpversion)
measurement=$($1/measure $2 | (LC_ALL=C sort -n || true) | head "-$(($2/2))" | tail -1)
revision=$(git rev-parse --short HEAD)

(
  grep -v "$machine" "$1/measurements.txt" 2>/dev/null || true;
  echo "$measurement	$machine	$freq	$compiler	$revision"
) | (LC_ALL=C sort -n || true) > "$1/measurements.txt.tmp"

mv "$1/measurements.txt.tmp" "$1/measurements.txt"
