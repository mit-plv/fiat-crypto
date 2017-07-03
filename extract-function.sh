#!/bin/sh
set -eu

case "$#" in
  0)
    funcname=f
    ;;
  1)
    funcname="$1"
    ;;
  *)
    exit 111
    ;;
esac

cat <<EOF
#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "$funcname.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#undef force_inline
#define force_inline __attribute__((always_inline))

EOF

lines=0
show=false
while IFS= read -r line; do
  case "$line" in
    *"λ '"*)
      echo -n "void force_inline $funcname("
      echo -n "uint64_t* out"
      echo "$line" | grep -owP -- '\w+\d+' | \
        while IFS= read -r arg; do
          echo -n ", uint64_t $arg"
        done
        echo ')'
      show=true
      ;;
    *"Return "*|*"return "*)
      i=0
      echo "$line" | \
        sed 's:return::g' | sed 's:Return::g' | tr -d '(' | tr -d ')' | tr , '\n' | sed 's/^\s\+//g' | \
        ( while IFS= read -r ret; do
            echo "out[$i] = $ret;"
            i=$((i+1))
          done;
          seq 2 "$lines" | while IFS= read -r _; do
            echo -n "}"
          done
          echo "}"
          echo "// caller: uint64_t out[$i];" )
      show=false
      break
      ;;
    *)
      case "$show" in
        true)
          lines=$((lines+1))
          line="$(echo "$line" | \
            sed s':^\([^,]*\),\(\s*\)\([^ ]*\) \([^ ]*\)\(.*\)\(mulx.*\))\([; ]*\)$: \3 \4;\2\1\5_\6, \&\4)\7:' | \
            sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(addcarryx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:' | \
            sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(subborrow.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:')"
          echo "{ $line"
          ;;
      esac
      ;;
  esac
done

