#!/usr/bin/env python3
import sys, re, os

SCRIPT_DIRECTORY = os.path.dirname(os.path.realpath(__file__))
GENERATED_DIRECTORY = os.path.join(SCRIPT_DIRECTORY, 'generated')
EXTRACTION_DIRECTORY = os.path.realpath(os.path.join(SCRIPT_DIRECTORY, '..', '..', '..', 'ExtractionOCaml'))
BITWIDTHS = ('32', '64')
MKINDS = (('unsaturated_solinas', 'UnsaturatedSolinas', (' 0%nat', ' 1%nat')), ('word_by_word_montgomery', 'WordByWordMontgomery', ('',)))
VKINDS = ('GallinaAxOf', 'GallinaAxComputedOf', 'PipelineOf', 'GallinaDefOf')

def get_input(fname):
    if fname == '-':
        return sys.stdin.readlines()
    else:
        with open(fname, 'r') as f:
            return f.readlines()

def filter_lines(lines):
    for line in lines:
        line = re.sub('#.*', '', line).strip(' \n').replace(' ', '')
        if line != '':
            yield line

def write_if_different(fname, contents):
    if os.path.exists(fname):
        with open(fname, 'r') as f:
            old_contents = f.read()
        if old_contents == contents: return
    with open(fname, 'w') as f:
        f.write(contents)

def prime_to_fname(prime, bitwidth, descr, ext=''):
    return 'p%s__x%s__%s%s' % (prime.replace('^', '').replace('-', 'm').replace('+', 'p').replace('*', 't'), bitwidth, descr.replace('%nat', '').replace(' ', '_'), ext)

def write_files(prime):
    if not os.path.exists(GENERATED_DIRECTORY): os.mkdir(GENERATED_DIRECTORY)
    for bitwidth in BITWIDTHS:
        for mdescr, mkind, extra_args in MKINDS:
            for extra_arg in extra_args:
                for vkind in VKINDS:
                    write_if_different(os.path.join(GENERATED_DIRECTORY, prime_to_fname(prime, bitwidth, mdescr + '_' + vkind + extra_arg, ext='.v')),
                                       r'''Require Import Crypto.Rewriter.PerfTesting.Core.
Global Set Printing Width 1000000.
Goal True.
  %s.perf%s "%s" %s%s.
  exact I.
Defined.
''' % (mkind, vkind, prime, bitwidth, extra_arg))
                write_if_different(os.path.join(GENERATED_DIRECTORY, prime_to_fname(prime, bitwidth, mdescr + '_extracted' + extra_arg, ext='.sh')),
                                   r'''#!/usr/bin/env bash
%s "%s" %s%s
''' % (os.path.join(EXTRACTION_DIRECTORY, 'perf_' + mdescr), prime, bitwidth, extra_arg.replace('%nat', '')))

def write_makefile(primes):
    if not os.path.exists(GENERATED_DIRECTORY): os.mkdir(GENERATED_DIRECTORY)
    vos = ' \\\n\t'.join('src/Rewriter/PerfTesting/Specific/generated/%s' % prime_to_fname(prime, bitwidth, mdescr + '_' + vkind + extra_arg, ext='.vo')
                         for prime in primes
                         for bitwidth in BITWIDTHS
                         for mdescr, mkind, extra_args in MKINDS
                         for extra_arg in extra_args
                         for vkind in VKINDS)
    shs = ' \\\n\t'.join('src/Rewriter/PerfTesting/Specific/generated/%s' % prime_to_fname(prime, bitwidth, mdescr + '_extracted' + extra_arg, ext='.sh')
                         for prime in primes
                         for bitwidth in BITWIDTHS
                         for mdescr, mkind, extra_args in MKINDS
                         for extra_arg in extra_args)

    # We unconditionally write to primes.mk, so that invoking this target actually updates the timestamp
    with open(os.path.join(GENERATED_DIRECTORY, 'primes.mk'), 'w') as f:
        f.write(r'''PERF_PRIME_VOS := %s
PERF_PRIME_SHS := %s
''' % (vos, shs))

if __name__ == '__main__':
    primes = tuple(filter_lines(get_input(sys.argv[1])))
    for prime in primes: write_files(prime)
    write_makefile(primes)
