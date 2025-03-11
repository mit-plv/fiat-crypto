#!/usr/bin/env python3
# USAGE: ./fiat-amd64/gentest.py fiat-amd64/*.asm | while IFS= read -r line; do eval $line 2>/dev/null > /dev/null && echo "$line" || echo "# $line" ; done
import shlex
import sys
import math
import re
import os
from collections import OrderedDict

# in Python 3.9 and newer, this is primitive as str.removesuffix
def removesuffix(s, suffix):
    if s.endswith(suffix): return s[:-len(suffix)]
    return s
def removeprefix(s, prefix):
    if s.startswith(prefix): return s[len(prefix):]
    return s

# grep -oP "src/.*square" fiat-c/src/*64*.c

#unsaturated_solinas
solinasprimes = dict( # num limbs, prime
        curve25519=('5', '2^255 - 19'),
        p448_solinas=('8', '2^448 - 2^224 - 1'),
        p521=('9', '2^521 - 1'),
        poly1305=('3', '2^130 - 5'))

montgomeryprimes = dict(
  curve25519_scalar='2^252 + 27742317777372353535851937790883648493',
  p224='2^224 - 2^96 + 1',
  p256='2^256 - 2^224 + 2^192 + 2^96 - 1',
  p256_scalar='2^256 - 2^224 + 2^192 - 89188191075325690597107910205041859247',
  p384='2^384 - 2^128 - 2^96 + 2^32 - 1',
  p384_scalar='2^384 - 1388124618062372383947042015309946732620727252194336364173',
  p434='2^216 * 3^137 - 1',
  secp256k1_montgomery='2^256 - 2^32 - 977',
  secp256k1_scalar='2^256 - 432420386565659656852420866394968145599')

saturatedsolinasprimes = dict(
  curve25519_solinas=('2^255 - 19'))

dettmanprimes = dict( # last limb width, limbs, last reduction, prime
  secp256k1_dettman=('48', '5', '2', '2^256 - 4294968273'))

output_makefile = ('--makefile' in sys.argv[1:])
directories = tuple(i for i in sys.argv[1:] if i not in ('--makefile',))

asm_op_names = OrderedDict()

regex = re.compile(r'fiat_(?P<name>[^_]+(_(solinas|montgomery|dettman))?)_(?P<op>(carry_)?(square|mul|from_bytes|to_bytes|add|sub|opp))')
for dirname in directories:
    m = regex.match(os.path.basename(dirname))
    if m:
        for fname in os.listdir(dirname):
            groups = m.groupdict()
            asm_op_names.setdefault((groups['name'], groups['op']), []).append(os.path.join(dirname,fname))

def asm_op_names_key(val):
    (name, op), fnames = val
    n = 0

    if name in dettmanprimes.keys():
        kind = 0
        limbwidth, n, last_reduction, prime = dettmanprimes[name]

    elif name in saturatedsolinasprimes.keys():
        kind = 1
        prime = saturatedsolinasprimes[name]

    elif name in montgomeryprimes.keys():
        kind = 2
        prime = montgomeryprimes[name]

    elif name in solinasprimes.keys():
        kind = 3
        n, prime = solinasprimes[name]

    else:
        assert False, name

    return (kind, n, prime, op, name, fnames)

def is_small(val):
    (kind, n, prime, op, name, fnames) = asm_op_names_key(val)
    prime = eval(prime.replace('^', '**'))
    return math.log2(prime) / 64 <= 4

asm_op_names_items = tuple(sorted(asm_op_names.items(), key=asm_op_names_key))
small_asm_op_names_items = tuple(val for val in asm_op_names_items if is_small(val))

status_file_stems = [f'fiat-amd64/{name}-{op}' for (name, op), _fnames in asm_op_names_items]
small_status_file_stems = [f'fiat-amd64/{name}-{op}' for (name, op), _fnames in small_asm_op_names_items]

status_files = [stem + '.status' for stem in status_file_stems]
only_status_files = [stem + '.only-status' for stem in status_file_stems]
small_status_files = [stem + '.status' for stem in small_status_file_stems]
small_only_status_files = [stem + '.only-status' for stem in small_status_file_stems]

if output_makefile:
    print(f'''

# Allow SLOWEST_FIRST=1 to be passed to test files in reverse order.
# When testing interactively, we probably want to test quicker files
# first, to be more snappy.  But on CI, testing the slowest files
# first probably allows for slightly better scheduling when there's
# more parallelism.

AMD64_ASM_STATUS_FILES := $(if $(SLOWEST_FIRST),{' '.join(reversed(status_files))},{' '.join(status_files)})
AMD64_ASM_ONLY_STATUS_FILES := $(if $(SLOWEST_FIRST),{' '.join(reversed(only_status_files))},{' '.join(only_status_files)})
AMD64_ASM_SMALL_STATUS_FILES := $(if $(SLOWEST_FIRST),{' '.join(reversed(small_status_files))},{' '.join(small_status_files)})
AMD64_ASM_SMALL_ONLY_STATUS_FILES := $(if $(SLOWEST_FIRST),{' '.join(reversed(small_only_status_files))},{' '.join(small_only_status_files)})

''')

for item in asm_op_names_items:
    (kind, n, prime, op, name, fnames) = asm_op_names_key(item)
    if kind == 0:
        binary = 'src/ExtractionOCaml/dettman_multiplication'
        binary_descr = 'Dettman Multiplication'
        limbwidth, _n, last_reduction, _prime = dettmanprimes[name]
        invocation = ' '.join([binary, name, '64', n, limbwidth, last_reduction, shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1'] +                                         [item for fname in fnames for item in ('--hints-file', shlex.quote(fname))])
    elif kind == 1:
        binary = 'src/ExtractionOCaml/solinas_reduction'
        binary_descr = 'Saturated Solinas'
        invocation = ' '.join([binary, name, '64', shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1'] +                                         [item for fname in fnames for item in ('--hints-file', shlex.quote(fname))])
    elif kind == 2:
        binary = 'src/ExtractionOCaml/word_by_word_montgomery'
        binary_descr = 'Word-by-Word Montgomery'
        invocation = ' '.join([binary, name, '64', shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1'] +                                         [item for fname in fnames for item in ('--hints-file', shlex.quote(fname))])
    elif kind == 3:
        binary = 'src/ExtractionOCaml/unsaturated_solinas'
        binary_descr = 'Unsaturated Solinas'
        invocation = ' '.join([binary, name, '64', n, shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1', '--tight-bounds-mul-by', '1.000001'] + [item for fname in fnames for item in ('--hints-file', shlex.quote(fname))])
    else:
        assert False, name
    if output_makefile:
        short_fnames = [removesuffix(os.path.basename(fname),'.asm') for fname in fnames]
        description = f'{name} {prime.replace(" ", "")} ({op}) ({binary_descr}) ({" ".join(short_fnames)})'
        output_name = f'fiat-amd64/{name}-{op}'
        print(f'''
only-test-amd64-files-print-report:: {output_name}.only-status
\t@ test $$(cat $<) -eq 0 || echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'

test-amd64-files-print-report:: {output_name}.status
\t@ test $$(cat $<) -eq 0 || echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'

clean::
\t$(HIDE)rm -f {output_name}.status {output_name}.only-status {output_name}.invocation {output_name}.description {output_name}.out {output_name}.out-asm {output_name}.stdout

.PHONY: {output_name}.only-status

{output_name}.status: {binary}

{output_name}.status {output_name}.only-status: {' '.join(fnames)}
\t$(SHOW)'TEST AMD64 {description} ...'
\t$(HIDE)rm -f $@
\t$(HIDE)echo {shlex.quote(invocation + ' -o /dev/null --output-asm /dev/null')} > {output_name}.invocation
\t$(HIDE)echo '{description}' > {output_name}.description
\t$(HIDE)$(TIMER) $(PERF_RECORDER) {invocation} -o {output_name}.out --output-asm {output_name}.out-asm >{output_name}.stdout && \\
\t  {{ echo $$? > $@; echo 'TEST AMD64 {description} ... \t$(GREEN)$(BOLD)PASSED$(NORMAL)$(NC)'; }} || \\
\t  {{ echo $$? > $@; echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'; \\
\t       echo '================== stdout =================='; \\
\t       cat {output_name}.stdout; \\
\t       echo '============================================'; \\
\t       exit 1; }}
''')
    else:
        print(invocation, '-o', '/dev/null', '--output-asm', '/dev/null')
