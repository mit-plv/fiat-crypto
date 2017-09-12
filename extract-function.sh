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

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

EOF

lines=0
show=false
brace='{ '
close_brace='}'
function_open_brace=''
if [ ! -z "${FIAT_CRYPTO_EXTRACT_FUNCTION_IS_ASM}" ]; then
  function_open_brace=' {'
  brace=''
  close_brace=''
fi
while IFS= read -r line; do
  case "$line" in
    *"λ '"*)
      echo -n "void force_inline $funcname("
      echo -n "uint64_t* out"
      echo "$line" | grep -owP -- '\w+\d+' | \
        while IFS= read -r arg; do
          echo -n ", uint64_t $arg"
        done
        echo -n ')'
        echo "${function_open_brace}"
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
            echo -n "${close_brace}"
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
          line="$(printf "%s" "$line" | \
            sed s':^\([^,]*\),\(\s*\)\([^ ]*\) \([^ ]*\)\(.*\)\(mulx.*\))\([; ]*\)$: \3 \4;\2\1\5_\6, \&\4)\7:' | \
            sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(addcarryx.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:' | \
            sed s':^\([^,]*\) \([^, ]*\)\(\s*\),\(.*\)\(subborrow.*\))\([; ]*\)$:\1 \2\3;\4_\5, \&\2)\6:')"
          printf "%s%s\n" "${brace}" "${line}"
          ;;
      esac
      ;;
  esac
done
