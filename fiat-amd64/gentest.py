#!/usr/bin/env python3
# USAGE: ./fiat-amd64/gentest.py fiat-amd64/*.asm | while IFS= read -r line; do eval $line 2>/dev/null > /dev/null && echo "$line" || echo "# $line" ; done
import shlex
import sys

# in Python 3.9 and newer, this is primitive as str.removesuffix
def removesuffix(s, suffix):
    if s.endswith(suffix): return s[:-len(suffix)]
    return s

# grep -oP "src/.*square" fiat-c/src/*64*.c
solinasprimes = dict(
        curve25519=('5', '2^255 - 19'),
        p448=('8', '2^448 - 2^224 - 1'),
        p521=('9', '2^521 - 1'),
        poly1305=('3', '2^130 - 5'))

montgomeryprimes = dict(
  p224='2^224 - 2^96 + 1',
  p256='2^256 - 2^224 + 2^192 + 2^96 - 1',
  p384='2^384 - 2^128 - 2^96 + 2^32 - 1',
  p434='2^216 * 3^137 - 1',
  secp256k1='2^256 - 2^32 - 977')

for fname in sys.argv[1:]:
    op, name = removesuffix(fname, '.asm').replace('_solinas','').split('_')[-2:]
    if name in solinasprimes.keys():
        n, prime = solinasprimes[name]
        print ('src/ExtractionOCaml/unsaturated_solinas', name, '64', n, shlex.quote(prime), dict(mul='carry_mul',square='carry_square')[op], '--no-wide-int', '--shiftr-avoid-uint1', '--tight-bounds-mul-by', '1.000001', '--hints-file', shlex.quote(fname), '-o', '/dev/null', '--output-asm', '/dev/null')
    elif name in montgomeryprimes.keys():
        prime = montgomeryprimes[name]
        print ('src/ExtractionOCaml/word_by_word_montgomery', name, '64', shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1', '--hints-file', shlex.quote(fname), '-o', '/dev/null', '--output-asm', '/dev/null')
    else:
        assert False, name
