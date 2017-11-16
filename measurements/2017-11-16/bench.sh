#!/bin/sh
set -e
for p in $(cat primes.txt | sed 's:#.*::g' | grep . | tr -d ' ' | tr '^*+-' 'expm'); do
  for synth in solinas64 solinas32 montgomery64 montgomery32; do
    impls=$(ls -d "src/Specific/${synth}_${p}_"*"limbs" 2>/dev/null || true)
    if [ -z "$impls" ]; then
      printf "# MISSING src/Specific/%s_%s_*limbs\n" "$synth" "$p";
      continue
    fi
    for impl in $impls; do
      if [ ! -x "$impl/fibe" ]; then
        printf "# MISSING %s\n" "$impl/fibe"
        continue
      fi
      /usr/bin/time -f "$impl/fibe\t%e" "$impl/fibe"
    done
  done
  for ref in gmpvar gmpsec gmpxx; do
    impl=$(ls -d "src/Specific/montgomery64_$p"* 2>/dev/null || true)
    if [ ! -x "$impl/$ref" ]; then
      printf "# MISSING %s\n" "$impl/$ref"
      continue
    fi
    /usr/bin/time -f "$impl/$ref\t%e" "$impl/$ref"
  done
done
