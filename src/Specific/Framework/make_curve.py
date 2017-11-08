#!/usr/bin/env python
from __future__ import with_statement
import json, sys, os, math, re, shutil, io
from fractions import Fraction

DEFAULT_A24_FOR_BENCH = 121665
def compute_bitwidth(base):
    return 2**int(math.ceil(math.log(base, 2)))
def compute_sz(modulus, base):
    return 1 + int(math.ceil(math.log(modulus, 2) / base))
def default_carry_chains(sz):
    return ['seq 0 (pred %(sz)s)' % locals(), '[0; 1]']
def compute_s(modulus_str):
    base, exp, rest = re.match(r'\s*'.join(('^', '(2)', r'\^', '([0-9]+)', r'([0-9\^ +\*-]*)$')), modulus_str).groups()
    return '%s^%s' % (base, exp)
def reformat_base(base):
    if '.' not in base: return base
    int_part, frac_part = base.split('.')
    return int_part + ' + ' + str(Fraction('.' + frac_part))
def compute_c(modulus_str):
    base, exp, rest = re.match(r'\s*'.join(('^', '(2)', r'\^', '([0-9]+)', r'([0-9\^ +\*-]*)$')), modulus_str).groups()
    if rest.strip() == '': return []
    assert(rest.strip()[0] == '-')
    rest = negate_numexpr(rest.strip()[1:])
    ret = []
    for part in re.findall(r'(-?[0-9\^\*]+)', rest.replace(' ', '')):
        if part.isdigit() or (part[:1] == '-' and part[1:].isdigit()):
            ret.append(('1', part))
        elif part[:2] == '2^' and part[2:].isdigit():
            ret.append((part, '1'))
        elif part[:3] == '-2^' and part[3:].isdigit():
            ret.append((part[1:], '-1'))
        elif len(part.split('*')) == 2:
            a, b = part.split("*")
            if "^" not in b:
                ret.append((part, '1'))
            else:
                assert(b.replace(' ', '')[:2] == '2^')
                ret.append((a.strip(), b.strip()))
        else:
            raw_input('Unhandled part: %s' % part)
            ret = None
            break
    if ret is not None:
        return list(reversed(ret))
    # XXX FIXME: Is this the right way to extract c?
    return [('1', rest)]

def parse_base(base):
    ret = 0
    for term in base.split('+'):
        term = term.strip()
        if term.isdigit():
            ret += int(term)
        elif '.' in term and '/' not in term:
            ret += float(term)
        elif '/' in term and '.' not in term:
            ret += Fraction(term)
        else:
            raw_input('Unhandled: %s' % term)
            assert(False)
    return ret

def negate_numexpr(expr):
    remap = dict([(d, d) for d in '0123456789^* '] + [('-', '+'), ('+', '-')])
    return ''.join(remap[ch] for ch in expr)

def usage(exitcode=0, errmsg=None):
    print('USAGE: %s [-f|--force] PARAMETERS.json OUTPUT_FOLDER' % sys.argv[0])
    if errmsg is not None:
        print(errmsg)
    sys.exit(exitcode)

def get_file_root(folder=os.path.dirname(__file__), filename='Makefile'):
    dir_path = os.path.realpath(folder)
    while not os.path.isfile(os.path.join(dir_path, filename)) and dir_path != '/':
        dir_path = os.path.realpath(os.path.join(dir_path, '..'))
    if not os.path.isfile(os.path.join(dir_path, filename)):
        print('ERROR: Could not find Makefile in the root of %s' % folder)
        raise Exception
    return dir_path

def repeat_until_unchanged(update, arg):
    changed = True
    while changed:
        last = repr(arg)
        arg = update(arg)
        changed = (repr(arg) != last)
    return arg

def format_c_code(header, code, numargs, sz, indent='      ', closing_indent='            '):
    if closing_indent is None: closing_indent = indent
    if code is None or code.strip() == '':
        return 'None'
    ARGS = 'abcdefghijklmnopqrstuvwxyz'
    assert(numargs <= len(ARGS))
    if header is None:
        header = ''
    else:
        header = '\n%s%s' % (indent, header)
    ret = 'Some (fun %s =>%s' % (' '.join(ARGS[:numargs]), header)
    input_map = {}
    lines = [line for line in code.strip().split(';')]
    lines = [line.replace('do {', '') for line in lines]
    lines = [re.sub(r'\(u?int[0-9]+_t\) ', '', line) for line in lines]
    lines = [re.sub(r'\(limb\) ', '', line) for line in lines]
    lines = [re.sub(r'\(s32\) ', '', line) for line in lines]
    lines = [repeat_until_unchanged((lambda line: re.sub(r'\(([A-Za-z0-9_]+)\)', r'\1', line)),
                                    line)
             for line in lines]
    lines = [repeat_until_unchanged((lambda line: re.sub(r'\(([A-Za-z0-9_]+\[[0-9]+\])\)', r'\1', line)),
                                    line)
             for line in lines]
    out_match = re.match(r'^\s*u?int[0-9]+_t ([A-Za-z_][A-Za-z_0-9]*)\[([0-9]+)\]$', lines[0])
    if out_match is not None:
        out_var, out_count = out_match.groups()
        assert(int(out_count) == sz)
    else:
        assert('output[' in ';\n'.join(lines))
        out_var = 'output'
    ret_code = []
    do_fix = (lambda line: re.sub(r'([A-Za-z_][A-Za-z0-9_]*)\[([0-9]+)\]', r'\1\2', line))
    for line in lines:
        out_match = re.match(r'^\s*u?int[0-9]+_t [A-Za-z_0-9]+\[[0-9]+\]$', line)
        limb_match = re.match(r'^\s*limb [a-zA-Z0-9, ]+$', line)
        in_match = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*in([0-9]*)\[([0-9]+)\]$', line)
        fixed_line = do_fix(line)
        normal_match = re.match(r'^(\s*)([A-Za-z_][A-Za-z0-9_]*)(\s*)=(\s*)([A-Za-z_0-9\(\)\s<>*+-]+)$', fixed_line)
        upd_match = re.match(r'^(\s*)([A-Za-z_][A-Za-z0-9_]*)(\s*)([*+])=(\s*)([A-Za-z_0-9\(\)\s<>*+-]+)$', fixed_line)
        if line == '':
            ret_code.append(line)
        elif out_match or limb_match: pass
        elif in_match:
            var, in_num, idx = in_match.groups()
            if in_num == '':
                assert('in1[' not in code)
                in_num = '1'
            in_num = int(in_num) - 1
            idx = int(idx)
            input_map[in_num] = input_map.get(in_num, {})
            input_map[in_num][idx] = var
        elif normal_match:
            s0, var, s1, s2, val = normal_match.groups()
            ret_code.append('%sdlet %s%s:=%s%s in' % (s0, var, s1, s2, val))
        elif upd_match:
            s0, var, s1, op, s2, val = upd_match.groups()
            ret_code.append('%sdlet %s%s:=%s%s %s %s in' % (s0, var, s1, s2, var, op, val))
        else:
            print('Unhandled line:')
            raw_input(line)
    ret_code = ' '.join(ret_code).strip().split('\n')
    ret_code = [((indent + i.strip(' \n')) if i.strip()[:len('dlet ')] == 'dlet '
                 else (indent + '  ' + i.rstrip(' \n'))).rstrip()
                for i in ret_code]
    main_code = '\n'.join(ret_code)
    arg_code = []
    for in_count in sorted(input_map.keys()):
        arg_code.append("%slet '(%s) := %s in"
                        % (indent,
                           ', '.join(v for k, v in sorted(input_map[in_count].items(), reverse=True)),
                           ARGS[in_count]))
    if len(input_map.keys()) == 0:
        for in_count in range(numargs):
            in_str = str(in_count + 1)
            if in_count == 0: in_str = ''
            arg_code.append("%slet '(%s) := %s in"
                            % (indent,
                               ', '.join(do_fix('in%s[%d]' % (in_str, v)) for v in reversed(range(sz))),
                               ARGS[in_count]))
    ret += '\n%s\n' % '\n'.join(arg_code)
    ret += main_code
    ret += '\n%s(%s)' % (indent, ', '.join(do_fix('%s[%d]' % (out_var, i)) for i in reversed(range(sz))))
    ret += '\n%s)' % closing_indent
    return ret

def nested_list_to_string(v):
    if isinstance(v, bool):
        return {True:'true', False:'false'}[v]
    elif isinstance(v, str) or isinstance(v, int) or isinstance(v, unicode):
        return str(v)
    elif isinstance(v, list):
        return '[%s]' % '; '.join(map(nested_list_to_string, v))
    elif isinstance(v, tuple):
        return '(%s)' % ', '.join(map(nested_list_to_string, v))
    else:
        print('ERROR: Invalid type in nested_list_to_string: %s' % str(type(v)))
        assert(False)

def as_bool(v):
    if isinstance(v, str) or isinstance(v, unicode): return {'true':True, 'false':False}[v]
    if isinstance(v, bool): return v
    raise Exception('Not a bool: %s' % repr(v))

def make_curve_parameters(parameters):
    def fix_option(term, scope_string=''):
        if not isinstance(term, str) and not isinstance(term, unicode):
            return term
        if term[:len('Some ')] != 'Some ' and term != 'None':
            if ' ' in term and (term[0] + term[-1]) not in ('()', '[]'):
                return 'Some (%s)%s' % (term, scope_string)
            return 'Some %s%s' % (term, scope_string)
        return term
    replacements = dict(parameters)
    assert(all(ch in '0123456789^+-* ' for ch in parameters['modulus']))
    modulus = eval(parameters['modulus'].replace('^', '**'))
    base = parse_base(parameters['base'])
    replacements['reformatted_base'] = reformat_base(parameters['base'])
    replacements['bitwidth'] = parameters.get('bitwidth', str(compute_bitwidth(base)))
    bitwidth = int(replacements['bitwidth'])
    replacements['sz'] = parameters.get('sz', str(compute_sz(modulus, base)))
    sz = int(replacements['sz'])
    replacements['a24'] = fix_option(parameters.get('a24', 'None'))
    replacements['carry_chains'] = fix_option(parameters.get('carry_chains', 'None'))
    if isinstance(replacements['carry_chains'], list):
        defaults = default_carry_chains(replacements['sz'])
        replacements['carry_chains'] \
            = ('Some %s%%nat'
               % nested_list_to_string([(v if v != 'default' else defaults[i])
                                        for i, v in enumerate(replacements['carry_chains'])]))
    elif replacements['carry_chains'] in ('default', 'Some default'):
        replacements['carry_chains'] = 'Some %s%%nat' % nested_list_to_string(default_carry_chains(replacements['sz']))
    replacements['s'] = parameters.get('s', compute_s(parameters['modulus']))
    replacements['c'] = parameters.get('c', compute_c(parameters['modulus']))
    for op, nargs in (('mul', 2), ('square', 1)):
        replacements[op] = format_c_code(parameters.get(op + '_header', None),
                                         parameters.get(op + '_code', None),
                                         nargs,
                                         sz)
    replacements['coef_div_modulus_raw'] = replacements.get('coef_div_modulus', '0')
    replacements['freeze'] = fix_option(nested_list_to_string(replacements.get('freeze', 'freeze' in parameters.get('operations', []))))
    replacements['ladderstep'] = nested_list_to_string(replacements.get('ladderstep', any(f in parameters.get('operations', []) for f in ('ladderstep', 'xzladderstep'))))
    for k, scope_string in (('upper_bound_of_exponent_loose', ''),
                            ('upper_bound_of_exponent_tight', ''),
                            ('allowable_bit_widths', '%nat'),
                            ('freeze_extra_allowable_bit_widths', '%nat'),
                            ('coef_div_modulus', '%nat'),
                            ('modinv_fuel', '%nat'),
                            ('karatsuba', ''),
                            ('goldilocks', '')):
        replacements[k] = fix_option(nested_list_to_string(replacements.get(k, 'None')), scope_string=scope_string)
    for k in ('montgomery', ):
        if k not in replacements.keys():
            replacements[k] = False
    for k in ('s', 'c', 'karatsuba', 'goldilocks', 'montgomery'):
        replacements[k] = nested_list_to_string(replacements[k])
    for k in ('extra_prove_mul_eq', 'extra_prove_square_eq'):
        if k not in replacements.keys():
            replacements[k] = 'idtac'
    ret = r"""Require Import Crypto.Specific.Framework.RawCurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : %(modulus)s
Base: %(base)s
***)

Definition curve : CurveParameters :=
  {|
    sz := %(sz)s%%nat;
    base := %(reformatted_base)s;
    bitwidth := %(bitwidth)s;
    s := %(s)s;
    c := %(c)s;
    carry_chains := %(carry_chains)s;

    a24 := %(a24)s;
    coef_div_modulus := %(coef_div_modulus)s;

    goldilocks := %(goldilocks)s;
    karatsuba := %(karatsuba)s;
    montgomery := %(montgomery)s;
    freeze := %(freeze)s;
    ladderstep := %(ladderstep)s;

    mul_code := %(mul)s;

    square_code := %(square)s;

    upper_bound_of_exponent_loose := %(upper_bound_of_exponent_loose)s;
    upper_bound_of_exponent_tight := %(upper_bound_of_exponent_tight)s;
    allowable_bit_widths := %(allowable_bit_widths)s;
    freeze_extra_allowable_bit_widths := %(freeze_extra_allowable_bit_widths)s;
    modinv_fuel := %(modinv_fuel)s
  |}.

Ltac extra_prove_mul_eq _ := %(extra_prove_mul_eq)s.
Ltac extra_prove_square_eq _ := %(extra_prove_square_eq)s.
""" % replacements
    return ret

def make_synthesis(prefix):
    return r"""Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import %s.CurveParameters.

Module P <: PrePackage.
  Definition package : Tag.Context.
  Proof. make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq. Defined.
End P.

Module Export S := PackageSynthesis P.
""" % prefix

def make_synthesized_arg(fearg, prefix, montgomery=False):
    def make_from_arg(arg, nargs, phi_arg_postfix='', phi_output_postfix='', prefix=prefix):
        LETTERS = 'abcdefghijklmnopqrstuvwxyz'
        assert(nargs <= len(LETTERS))
        arg_names = ' '.join(LETTERS[:nargs])
        if not montgomery:
            arg_types = ' -> '.join(['feBW%s' % phi_arg_postfix] * nargs)
            mapped_args = ' '.join('(phiBW%s %s)' % (phi_arg_postfix, l)
                                   for l in LETTERS[:nargs])
            feBW_output = 'feBW' + phi_output_postfix
            phi_output = 'phiBW' + phi_output_postfix
        else:
            arg_types = ' -> '.join(['feBW_small'] * nargs)
            mapped_args = ' '.join('(phiM_small %s)' % l
                                   for l in LETTERS[:nargs])
            feBW_output = 'feBW_small'
            phi_output = 'phiM_small'
        return locals()
    GEN_PREARG = r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition %(arg)s :
  { %(arg)s : %(arg_types)s -> %(feBW_output)s
  | forall %(arg_names)s, %(phi_output)s (%(arg)s %(arg_names)s) = """
    GEN_MIDARG = "F.%(arg)s %(mapped_args)s"
    SQUARE_MIDARG = "F.mul %(mapped_args)s %(mapped_args)s"
    CARRY_MIDARG = "%(mapped_args)s"
    GEN_POSTARG = r""" }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(arg)s.
"""
    GEN_ARG = GEN_PREARG + GEN_MIDARG + GEN_POSTARG
    SQUARE_ARG = GEN_PREARG + SQUARE_MIDARG + GEN_POSTARG
    CARRY_ARG = GEN_PREARG + CARRY_MIDARG + GEN_POSTARG
    nargs_map = {'mul':2, 'sub':2, 'add':2, 'square':1, 'opp':1, 'carry':1}
    special_args = {'fecarry':CARRY_ARG, 'fecarry_square':SQUARE_ARG, 'fesquare':SQUARE_ARG}
    if fearg in ('fecarry_mul', 'fecarry_sub', 'fecarry_add', 'fecarry_square', 'fecarry_opp'):
        nargs = nargs_map[fearg.split('_')[-1]]
        ARG = special_args.get(fearg, GEN_ARG)
        return ARG % make_from_arg(fearg[2:], nargs=nargs, phi_arg_postfix='_tight', phi_output_postfix='_tight')
    elif fearg in ('femul', 'fesquare', 'fecarry'):
        ARG = special_args.get(fearg, GEN_ARG)
        nargs = nargs_map[fearg[2:]]
        return ARG % make_from_arg(fearg[2:], nargs=nargs, phi_arg_postfix='_loose', phi_output_postfix='_tight')
    if fearg in ('fesub', 'feadd', 'feopp'):
        nargs = nargs_map[fearg[2:]]
        return GEN_ARG % make_from_arg(fearg[2:], nargs=nargs, phi_arg_postfix='_tight', phi_output_postfix='_loose')
    elif fearg in ('freeze',):
        return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition freeze :
  { freeze : feBW_tight -> feBW_limbwidths
  | forall a, phiBW_limbwidths (freeze a) = phiBW_tight a }.
Proof.
  Set Ltac Profiling.
  Time synthesize_freeze ().
  Show Ltac Profile.
Time Defined.

Print Assumptions freeze.
""" % {'prefix':prefix}
    elif fearg in ('fenz',):
        assert(fearg == 'fenz')
        assert(montgomery)
        full_arg = 'nonzero'
        return r"""Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.
Local Open Scope Z_scope.

(* TODO : change this to field once field isomorphism happens *)
Definition %(full_arg)s :
  { %(full_arg)s : feBW_small -> BoundedWord.BoundedWord 1 adjusted_bitwidth bound1
  | forall a, (BoundedWord.BoundedWordToZ _ _ _ (%(full_arg)s a) =? 0) = (if Decidable.dec (phiM_small a = F.of_Z m 0) then true else false) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(full_arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(full_arg)s.
""" % {'prefix':prefix, 'full_arg':full_arg}
    elif fearg in ('ladderstep', 'xzladderstep'):
        return r"""Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.Ladderstep.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition xzladderstep :
  { xzladderstep : feW -> feW * feW -> feW * feW -> feW * feW * (feW * feW)
  | forall x1 Q Q',
      let xz := xzladderstep x1 Q Q' in
      let eval := B.Positional.Fdecode wt in
      feW_tight_bounded x1
      -> feW_tight_bounded (fst Q) /\ feW_tight_bounded (snd Q)
      -> feW_tight_bounded (fst Q') /\ feW_tight_bounded (snd Q')
      -> ((feW_tight_bounded (fst (fst xz)) /\ feW_tight_bounded (snd (fst xz)))
          /\ (feW_tight_bounded (fst (snd xz)) /\ feW_tight_bounded (snd (snd xz))))
         /\ Tuple.map (n:=2) (Tuple.map (n:=2) phiW) xz = FMxzladderstep (m:=m) (eval (proj1_sig a24_sig)) (phiW x1) (Tuple.map (n:=2) phiW Q) (Tuple.map (n:=2) phiW Q') }.
Proof.
  Set Ltac Profiling.
  synthesize_xzladderstep ().
  Show Ltac Profile.
Time Defined.

Print Assumptions xzladderstep.
""" % {'prefix':prefix}
    else:
        print('ERROR: Unsupported operation: %s' % fearg)
        raise ArgumentError


def make_display_arg(fearg, prefix):
    file_name = fearg
    function_name = fearg
    if fearg in ('femul', 'fesub', 'feadd', 'fesquare', 'feopp', 'fecarry',
                 'fecarry_mul', 'fecarry_sub', 'fecarry_add', 'fecarry_square', 'fecarry_opp'):
        function_name = fearg[2:]
    elif fearg in ('freeze', 'xzladderstep'):
        pass
    elif fearg in ('fenz',):
        function_name = 'nonzero'
    elif fearg in ('ladderstep', ):
        function_name = 'xzladderstep'
    else:
        print('ERROR: Unsupported operation: %s' % fearg)
        raise ArgumentError
    return r"""Require Import %(prefix)s.%(file_name)s.
Require Import Crypto.Specific.Framework.IntegrationTestDisplayCommon.

Check display %(function_name)s.
""" % locals()

def make_compiler(compiler):
    return r"""#!/bin/sh
set -eu

%s "$@"
""" % compiler

def make_py_interpreter(parameters):
    q = repr(str(parameters['modulus'])).replace('^', '**')
    modulus_bytes = repr(str(parameters['base']))
    a24 = repr(str(parameters.get('a24', DEFAULT_A24_FOR_BENCH)))
    return r"""#!/bin/sh
set -eu

/usr/bin/env python3 "$@" -Dq=%(q)s -Dmodulus_bytes=%(modulus_bytes)s -Da24=%(a24)s
""" % locals()


DONT_EDIT_STR = 'WARNING: This file was copied from %s.\n If you edit it here, changes will be erased the next time remake_curves.sh is run.'
DONT_EDIT_HEADERS = {
    '.c' : '/* ' + DONT_EDIT_STR + ' */',
    '.h' : '/* ' + DONT_EDIT_STR + ' */',
    '.v' : '(* ' + DONT_EDIT_STR + ' *)',
    '.ml' : '(* ' + DONT_EDIT_STR + ' *)',
    '.ml4' : '(* ' + DONT_EDIT_STR + ' *)',
    '.py' : '# ' + DONT_EDIT_STR.replace('\n', '\n# '),
}



def main(*args):
    if '--help' in args[1:] or '-h' in args[1:]: usage(0)
    force = any(f in args[1:] for f in ('-f', '--force'))
    args = [args[0]] + [arg for arg in args[1:] if arg not in ('-f', '--force')]
    if len(args) != 3: usage(1, errmsg='Error: Invalid number of arguments %d (%s)' % (len(args), ' '.join(args)))
    with open(args[1], 'r') as f:
        parameters = f.read()
    output_folder = os.path.realpath(args[2])
    parameters_folder = os.path.dirname(os.path.realpath(args[1]))
    parameters = json.loads(parameters, strict=False)
    root = get_file_root(folder=output_folder)
    output_prefix = 'Crypto.' + os.path.normpath(os.path.relpath(output_folder, os.path.join(root, 'src'))).replace(os.sep, '.')
    outputs = {}
    outputs['CurveParameters.v'] = make_curve_parameters(parameters)
    outputs['Synthesis.v'] = make_synthesis(output_prefix)
    for arg in parameters['operations']:
        outputs[arg + '.v'] = make_synthesized_arg(arg, output_prefix, montgomery=as_bool(parameters.get('montgomery', 'false')))
        outputs[arg + 'Display.v'] = make_display_arg(arg, output_prefix)
    for fname in parameters.get('extra_files', []):
        _, ext = os.path.splitext(fname)
        header = ''
        if ext in DONT_EDIT_HEADERS.keys():
            header = DONT_EDIT_HEADERS[ext] % os.path.relpath(fname, os.path.join(root, 'src'))
        outputs[os.path.basename(fname)] = header + '\n' + open(os.path.join(parameters_folder, fname), 'r').read()
    if 'compiler' in parameters.keys():
        outputs['compiler.sh'] = make_compiler(parameters['compiler'])
    if 'compilerxx' in parameters.keys():
        outputs['compilerxx.sh'] = make_compiler(parameters['compilerxx'])
    outputs['py_interpreter.sh'] = make_py_interpreter(parameters)
    file_list = tuple((k, os.path.join(output_folder, k)) for k in sorted(outputs.keys()))
    if not force:
        extant_files = [os.path.relpath(fname, os.getcwd())
                        for k, fname in file_list
                        if os.path.isfile(fname) and open(fname, 'r').read() != outputs[k]]
        if len(extant_files) > 0:
            print('ERROR: The files %s already exist; pass --force to overwrite them' % ', '.join(extant_files))
            sys.exit(1)
    if not os.path.isdir(output_folder):
        os.makedirs(output_folder)
    new_files = []
    for k, fname in file_list:
        if os.path.isfile(fname):
            if open(fname, 'r').read() == outputs[k]:
                continue
        new_files.append(fname)
        with io.open(fname, 'w', newline='\n') as f:
            f.write(unicode(outputs[k]))
            if any(fname.endswith(name) for name in ('compiler.sh', 'compilerxx.sh', 'py_interpreter.sh')):
                mode = os.fstat(f.fileno()).st_mode
                mode |= 0o111
                mode &= 0o7777
                if 'fchmod' in os.__dict__.keys():
                    os.fchmod(f.fileno(), mode)
                else:
                    os.chmod(f.name, mode)
    if len(new_files) > 0:
        print('git add ' + ' '.join('"%s"' % i for i in new_files))

if __name__ == '__main__':
    main(*sys.argv)
