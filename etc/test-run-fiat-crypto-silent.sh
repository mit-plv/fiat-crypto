#!/bin/sh

set -e

fiat_crypto="$1"

if [ -z "${fiat_crypto}" ]; then
    printf "USAGE: %s /path/to/fiat_crypto\n" "$0"
    exit 1
fi

for prog in word-by-word-montgomery unsaturated-solinas saturated-solinas base-conversion; do
  lang_line="$("${fiat_crypto}" $prog -h | grep -- --lang)"
  search='[Bb]edrock2'
  printf "%s\n" "${lang_line}" | grep -q "$search" || { printf "::error::%s: Missing %s in %s\n" "${prog}" "${search}" "${lang_line}"; exit 1; }
  search='Defaults to C if'
  printf "%s\n" "${lang_line}" | grep -q "$search" || { printf "::error::%s: Missing %s in %s\n" "${prog}" "${search}" "${lang_line}"; exit 1; }
done
