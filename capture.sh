#!/bin/sh
set -eu

grep -q constant_tsc /proc/cpuinfo || (echo "need constant_tsc" ; exit 100 )

machine=$(etc/machine.sh)
cpufreq=$(etc/cpufreq)
tscfreq=$(etc/tscfreq)
compiler=$($1/compiler.sh -dumpversion)
revision=$(git rev-parse --short HEAD)
status=$(git status -u no --porcelain >/dev/null && echo '+')
tsccycles=$($1/measure $2 | (LC_ALL=C sort -n || true) | head "-$(($2/2))" | tail -1)
cpucycles_expr="$tsccycles*$cpufreq/$tscfreq"
cpucycles=$(echo "$cpucycles_expr" | bc)

(
  grep -v "$machine" "$1/measurements.txt" 2>/dev/null || true;
  echo "$cpucycles  =$cpucycles_expr	$machine	$compiler	$revision$status"
) | (LC_ALL=C sort -n || true) > "$1/measurements.txt.tmp"

mv "$1/measurements.txt.tmp" "$1/measurements.txt"
