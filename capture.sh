#!/bin/sh
set -eu

machine=$(etc/machine.sh)
measurement=$($1/measure | (LC_ALL=C sort -n || true) | head -1024 | tail -1)
revision=$(git rev-parse --short HEAD)

(
  grep -v "$machine" "$1/measurements.txt" 2>/dev/null || true;
  echo "$measurement  $machine  $revision"
) | (LC_ALL=C sort -n || true) > "$1/measurements.txt.tmp"

mv "$1/measurements.txt.tmp" "$1/measurements.txt"
