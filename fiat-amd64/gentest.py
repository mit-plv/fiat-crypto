#!/usr/bin/env python3
# USAGE: ./fiat-amd64/gentest.py fiat-amd64/*.asm | while IFS= read -r line; do eval $line 2>/dev/null > /dev/null && echo "$line" || echo "# $line" ; done
import shlex
import sys

# in Python 3.9 and newer, this is primitive as str.removesuffix
def removesuffix(s, suffix):
    if s.endswith(suffix): return s[:-len(suffix)]
    return s
def removeprefix(s, prefix):
    if s.startswith(prefix): return s[len(prefix):]
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

output_makefile = ('--makefile' in sys.argv[1:])
asm_files = tuple(i for i in sys.argv[1:] if i not in ('--makefile',))

for fname in asm_files:
    op, name = removesuffix(fname, '.asm').replace('_solinas','').split('_')[-2:]
    if name in solinasprimes.keys():
        n, prime = solinasprimes[name]
        binary = 'src/ExtractionOCaml/unsaturated_solinas'
        binary_descr = 'Unsaturated Solinas'
        invocation = ' '.join((binary, name, '64', n, shlex.quote(prime), dict(mul='carry_mul',square='carry_square')[op], '--no-wide-int', '--shiftr-avoid-uint1', '--tight-bounds-mul-by', '1.000001', '--hints-file', shlex.quote(fname)))
    elif name in montgomeryprimes.keys():
        prime = montgomeryprimes[name]
        binary = 'src/ExtractionOCaml/word_by_word_montgomery'
        binary_descr = 'Word-by-Word Montgomery'
        invocation = ' '.join((binary, name, '64', shlex.quote(prime), op, '--no-wide-int', '--shiftr-avoid-uint1', '--hints-file', shlex.quote(fname)))
    else:
        assert False, name
    if output_makefile:
        short_fname = '_'.join(removesuffix(removeprefix(fname, 'fiat-amd64/'),'.asm').replace('_solinas','').split('_')[:-2])
        description = f'{name} {prime.replace(" ", "")} ({op}) ({binary_descr}) ({short_fname})'
        print(f'''
only-test-amd64-files-print-report:: {fname}.only-status
\t@ test $$(cat $<) -eq 0 || echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'

test-amd64-files-print-report:: {fname}.status
\t@ test $$(cat $<) -eq 0 || echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'

clean::
\t$(HIDE)rm -f {fname}.status {fname}.only-status {fname}.invocation {fname}.description {fname}.out {fname}.out-asm {fname}.stdout

.PHONY: {fname}.only-status

{fname}.status: | {binary}

{fname}.status {fname}.only-status: {fname}
\t$(SHOW)'TEST AMD64 {description} ...'
\t$(HIDE)rm -f $@
\t$(HIDE)echo {shlex.quote(invocation + ' -o /dev/null --output-asm /dev/null')} > $<.invocation
\t$(HIDE)echo '{description}' > $<.description
\t$(HIDE)$(TIMER) {invocation} -o $<.out --output-asm $<.out-asm >$<.stdout && \\
\t  {{ echo $$? > $@; echo 'TEST AMD64 {description} ... \t$(GREEN)$(BOLD)PASSED$(NORMAL)$(NC)'; }} || \\
\t  {{ echo $$? > $@; echo 'TEST AMD64 {description} ... \t$(RED)$(BOLD)FAILED$(NORMAL)$(NC)'; \\
\t       echo '================== stdout =================='; \\
\t       cat $<.stdout;                                       \\
\t       echo '============================================'; \\
\t       exit 1; }}
''')
    else:
        print(invocation, '-o', '/dev/null', '--output-asm', '/dev/null')
