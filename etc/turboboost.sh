#!/bin/sh
set -eu

case $1 in
  on) echo 0 > /sys/devices/system/cpu/intel_pstate/no_turbo ;;
  off) echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo ;;
  *) echo "USAGE: $0 <on|off>" ; exit 111
esac
