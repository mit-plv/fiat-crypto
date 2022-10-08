#!/bin/sh
set -eu

online_governors() {
  FOUND=""
  for cpu in "/sys/devices/system/cpu/cpu"[0-9]* ; do
    if grep -vq '^1$' "$cpu/online" 2>/dev/null; then
      continue
    fi
    if [ ! -e "$cpu/cpufreq" ]; then
      continue
    fi
    cat "$cpu/cpufreq/scaling_governor"
    FOUND=1
  done
  if [ -z "$FOUND" ]; then
    echo "nocpufreq_support"
  fi
}

# hostname is not on arch
if command -v hostname >/dev/null 2>/dev/null; then
    printf "$(hostname)"
elif command -v hostnamectl >/dev/null 2>/dev/null; then
    printf "$(hostnamectl --static)"
else
    printf "unknown_host"
fi
printf -
if ls /sys/devices/system/cpu/cpu[0-9]*/topology/thread_siblings_list >/dev/null 2>/dev/null; then
  grep -q '[^0-9]' /sys/devices/system/cpu/cpu[0-9]*/topology/thread_siblings_list && printf ht || printf noht
else
  printf unknown_ht
fi
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
printf "$(printf "%s" "$(online_governors | uniq)" | tr '\n' '_')"
printf -
printf "$(gcc -march=native -Q --help=target | grep -v 'Known valid arguments' | grep march | cut -d= -f2 | grep -ow '\S*')"
printf '\n'
