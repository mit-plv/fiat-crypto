#!/bin/sh
set -eu

usage() {
  echo "USAGE: $0 <on|off>" ; exit 111
}

if [ "$#" -eq 0 ]; then
  usage
fi

case $1 in
   on)
     for f in "/sys/devices/system/cpu/cpu"[0-9]*/online; do
       echo 1 > "$f"
     done
     ;;
  off)
    cores=""
    for cpu in "/sys/devices/system/cpu/cpu"[0-9]* ; do
      if grep -vq '^1$' "$cpu/online" 2>/dev/null; then
        continue
      fi
      coreid=$(cat "$cpu/topology/core_id")
      if echo "$cores" | grep -- "$coreid" ; then
        echo 0 > "$cpu/online"
      fi
      cores=$(printf "$cores\n$coreid")
    done
    ;;
  *) usage
esac
