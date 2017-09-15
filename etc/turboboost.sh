#!/bin/sh
set -eu

usage() {
  echo "USAGE: $0 <on|off>" ; exit 111
}

if [ "$#" -eq 0 ]; then
  usage
fi

case $1 in
  on) echo 0 > /sys/devices/system/cpu/intel_pstate/no_turbo ;;
  off) echo 1 > /sys/devices/system/cpu/intel_pstate/no_turbo ;;
  *) usage
esac
