#!/bin/sh
set -eu

online_governors() {
  for cpu in "/sys/devices/system/cpu/cpu"[0-9]* ; do
    if grep -vq '^1$' "$cpu/online" 2>/dev/null; then
      continue
    fi
    cat "$cpu/cpufreq/scaling_governor"
  done
}

printf "$(hostname)"
printf -
grep -q '[^0-9]' /sys/devices/system/cpu/cpu[0-9]*/topology/thread_siblings_list && printf ht || printf noht
printf -
if [ -f /sys/devices/system/cpu/intel_pstate/no_turbo ]; then
  grep -q 1 /sys/devices/system/cpu/intel_pstate/no_turbo && printf notb || printf tb
else
  printf notb_support
fi
printf -
if [ -f /sys/class/power_supply/AC/online ]; then
  grep -q 1 /sys/class/power_supply/AC/online && printf ac || printf noac
else
  printf nops
fi
printf -
printf "$(echo -n "$(online_governors | uniq)" | tr '\n' '_')"
printf -
printf "$(gcc -march=native -Q --help=target|grep march | cut -d= -f2 | grep -ow '\S*')"
printf '\n'
