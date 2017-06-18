#!/bin/sh
set -eu

printf "$(hostname)"
printf -
grep -q '[^0-9]' /sys/devices/system/cpu/cpu[0-9]*/topology/thread_siblings_list && printf ht || printf noht
printf -
grep -q 1 /sys/devices/system/cpu/intel_pstate/no_turbo && printf notb || printf tb
printf -
if [ -f /sys/class/power_supply/AC/online ]; then
  grep -q 1 /sys/class/power_supply/AC/online && printf ac || printf noac
else
  printf nops
fi
printf -
printf "$(gcc -march=native -Q --help=target|grep march | cut -d= -f2 | grep -ow '\S*')"
printf -

for cpu in $(seq 1 $(nproc)); do
	echo "scale=100000;pi=4*a(1);0" | bc -l &
	echo $!
done | ( \
	sleep .1 ;
        mhz=$(cat /proc/cpuinfo | grep "^[c]pu MHz" | cut -d: -f2 | tr -d ' ' | sort -nr | head -1);
	printf "$(echo "scale=2; ($mhz + 5)/1000" | bc)ghz"
        while IFS= read -r pid; do
		kill "$pid";
	done )

printf '\n'
