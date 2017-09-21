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

cat <<"EOF"
#include <stdint.h>

#undef force_inline
#define force_inline __attribute__((always_inline))

EOF

if [ -z "${BITWIDTH}" ]; then
  BITWIDTH=64
fi

while IFS= read -r line; do
  case "$line" in
    *"λ '"*)
      echo -n "void force_inline $funcname("
      echo -n "uint${BITWIDTH}_t* out"
      echo "$line" | grep -owP -- '\w+\d+' | \
        while IFS= read -r arg; do
          echo -n ", uint${BITWIDTH}_t $arg"
        done
        echo ');'
      break
      ;;
  esac
done
