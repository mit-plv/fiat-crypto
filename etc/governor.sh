#!/bin/sh
set -eu

usage() {
  generators="$1"
  echo "USAGE: $0 <$(echo "$generators" | tr ' ' '|')>"
  exit 111
}


for cpu in "/sys/devices/system/cpu/cpu"[0-9]* ; do
  if grep -vq '^1$' "$cpu/online" 2>/dev/null; then
    continue
  fi
  generators="$(cat "$cpu/cpufreq/scaling_available_governors")"
  if [ "$#" -eq 0 ] || [ -z "$1" ]; then
    usage "$generators"
  elif (echo -n "$generators" | tr ' ' '\n' | grep -q "^$1\$" 2>/dev/null); then
    if grep -vq "^$1\$" "$cpu/cpufreq/scaling_governor" 2>/dev/null; then
      echo "$1" > "$cpu/cpufreq/scaling_governor"
    fi
  else
    usage "$generators"
  fi
done
