#!/bin/sh
set -e
export PATH="$PATH:$HOME/android-toolchain/bin/"
for p in $(cat primes.txt | sed 's:#.*::g' | grep . | tr -d ' ' | tr '^*+-' 'expm'); do
  for synth in solinas32 montgomery32; do
    impls=$(ls -d "src/Specific/${synth}_${p}_"*"limbs" 2>/dev/null || true)
    if [ -z "$impls" ]; then
      printf "# MISSING src/Specific/%s_%s_*limbs\n" "$synth" "$p";
      continue
    fi
    for impl in $impls; do
      if ! sh -c "arm-linux-androideabi-gcc -pie \
        $(tail -1 "$impl/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
        -I \"$impl\" \
        -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
        src/Specific/Framework/bench/fibe.c \
        -o /tmp/main" \
        > /dev/null 2> /dev/null
      then
        printf "# MISSING %s\n" "$impl/fibe"
        continue
      fi
      adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null
      printf "$impl/fibe"
      adb shell "time /data/local/tmp/main 2>/dev/null" | sed 's:0m::g' | sed 's:s\sreal.*::g'
    done
  done
  for ref in gmpvar gmpsec; do
    impl=$(ls -d "src/Specific/montgomery32_$p"* 2>/dev/null || true)
    if ! sh -c "arm-linux-androideabi-gcc -pie \
      $(tail -1 "$impl/compiler.sh" | tr ' ' '\n' | grep -A99999 -- -D  | grep -v '"$@"' | tr '\n' ' ') \
      -I \"$impl\" \
      -I ~/android-toolchain/gmp-6.1.2/ \
      -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing \
      src/Specific/Framework/bench/$ref.c \
      $HOME/android-toolchain/gmp-6.1.2/.libs/libgmp.a \
      -o /tmp/main" \
      > /dev/null 2> /dev/null
    then
      printf "# MISSING %s\n" "$impl/$ref"
      continue
    fi
    adb push /tmp/main /data/local/tmp/main >/dev/null 2>/dev/null
    printf "$impl/$ref"
    adb shell "time /data/local/tmp/main 2>/dev/null" | sed 's:0m::g' | sed 's:s\sreal.*::g'
  done
done

