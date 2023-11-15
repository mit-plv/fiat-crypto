#!/bin/sh

set -e

fiat_crypto="$1"

if [ -z "${fiat_crypto}" ]; then
    printf "USAGE: %s /path/to/fiat_crypto\n" "$0"
    exit 1
fi

echo "::group::fiat_crypto"
"${fiat_crypto}" -h
echo "::endgroup::"
for prog in word-by-word-montgomery unsaturated-solinas saturated-solinas base-conversion; do
  echo "::group::$prog"
  "${fiat_crypto}" $prog -h
  echo "::endgroup::"
  lang_line="$("${fiat_crypto}" $prog -h | grep -- --lang)"
  echo "::group::$prog bedrock2 check"
  search='[Bb]edrock2'
  printf "%s\n" "${lang_line}" | grep -q "$search" || { printf "::error::Missing %s in %s\n" "${search}" "${lang_line}"; exit 1; }
  echo "::endgroup::"
  echo "::group::$prog default C check"
  search='Defaults to C if'
  printf "%s\n" "${lang_line}" | grep -q "$search" || { printf "::error::Missing %s in %s\n" "${search}" "${lang_line}"; exit 1; }
  echo "::endgroup::"
done
