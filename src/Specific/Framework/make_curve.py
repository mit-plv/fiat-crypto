#!/usr/bin/env python
from __future__ import with_statement
import json, sys, os, math, re, shutil, io

def compute_bitwidth(base):
    return 2**int(math.ceil(math.log(base, 2)))
def compute_sz(modulus, base):
    return 1 + int(math.ceil(math.log(modulus, 2) / base))
def default_carry_chains(sz):
    return ['seq 0 (pred %(sz)s)' % locals(), '[0; 1]']
def compute_s(modulus_str):
    base, exp, rest = re.match(r'\s*'.join(('^', '(2)', r'\^', '([0-9]+)', r'([0-9\^ +\*-]*)$')), modulus_str).groups()
    return '%s^%s' % (base, exp)
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
        else:
            raw_input('Unhandled part: %s' % part)
            ret = None
            break
    if ret is not None:
        return list(reversed(ret))
    # XXX FIXME: Is this the right way to extract c?
    return [('1', rest)]
def compute_goldilocks(s, c):
    # true if the prime is of the form 2^2k - 2^k - 1
    ms = re.match(r'^2\^([0-9]+)$', s)
    if ms is None: return False
    two_k = int(ms.groups()[0])
    assert(isinstance(c, list))
    if len(c) != 2: return False
    one_vs = [str(v) for k, v in c if str(k) == '1']
    others = [(str(k), str(v)) for k, v in c if str(k) != '1']
    if len(one_vs) != 1 or len(others) != 1 or one_vs[0] != '1' or others[0][1] != '1': return False
    mk = re.match(r'^2\^([0-9]+)$', others[0][0])
    if mk is None: return False
    k = int(mk.groups()[0])
    if two_k != 2 * k: return False
    return True



def negate_numexpr(expr):
    remap = dict([(d, d) for d in '0123456789^ '] + [('-', '+'), ('+', '-')])
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
    assert(all(ch in '0123456789^+- ' for ch in parameters['modulus']))
    modulus = eval(parameters['modulus'].replace('^', '**'))
    base = float(parameters['base'])
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
    replacements['goldilocks'] = parameters.get('goldilocks', compute_goldilocks(replacements['s'], replacements['c']))
    for op, nargs in (('mul', 2), ('square', 1)):
        replacements[op] = format_c_code(parameters.get(op + '_header', None),
                                         parameters.get(op + '_code', None),
                                         nargs,
                                         sz)
    replacements['coef_div_modulus_raw'] = replacements.get('coef_div_modulus', '0')
    for k, scope_string in (('upper_bound_of_exponent', ''),
                            ('allowable_bit_widths', '%nat'),
                            ('freeze_extra_allowable_bit_widths', '%nat'),
                            ('coef_div_modulus', '%nat'),
                            ('modinv_fuel', '%nat'),
                            ('goldilocks', '')):
        replacements[k] = fix_option(nested_list_to_string(replacements.get(k, 'None')), scope_string=scope_string)
    for k in ('montgomery', ):
        if k not in replacements.keys():
            replacements[k] = False
    for k in ('s', 'c', 'goldilocks', 'montgomery'):
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
    bitwidth := %(bitwidth)s;
    s := %(s)s;
    c := %(c)s;
    carry_chains := %(carry_chains)s;

    a24 := %(a24)s;
    coef_div_modulus := %(coef_div_modulus)s;

    goldilocks := %(goldilocks)s;
    montgomery := %(montgomery)s;

    mul_code := %(mul)s;

    square_code := %(square)s;

    upper_bound_of_exponent := %(upper_bound_of_exponent)s;
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
    if fearg in ('femul', 'fesub', 'feadd'):
        if not montgomery:
            return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition %(arg)s :
  { %(arg)s : feBW -> feBW -> feBW
  | forall a b, phiBW (%(arg)s a b) = F.%(arg)s (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(arg)s.
""" % {'prefix':prefix, 'arg':fearg[2:]}
        else:
            return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition %(arg)s :
  { %(arg)s : feBW_small -> feBW_small -> feBW_small
  | forall a b, phiM_small (%(arg)s a b) = F.%(arg)s (phiM_small a) (phiM_small b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(arg)s.
""" % {'prefix':prefix, 'arg':fearg[2:]}
    elif fearg in ('fesquare',):
        return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition square :
  { square : feBW -> feBW
  | forall a, phiBW (square a) = F.mul (phiBW a) (phiBW a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_square ().
  Show Ltac Profile.
Time Defined.

Print Assumptions square.
""" % {'prefix':prefix}
    elif fearg in ('freeze',):
        return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition freeze :
  { freeze : feBW -> feBW
  | forall a, phiBW (freeze a) = phiBW a }.
Proof.
  Set Ltac Profiling.
  Time synthesize_freeze ().
  Show Ltac Profile.
Time Defined.

Print Assumptions freeze.
""" % {'prefix':prefix}
    elif fearg in ('feopp',):
        if not montgomery:
            return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition %(arg)s :
  { %(arg)s : feBW -> feBW
  | forall a, phiBW (%(arg)s a) = F.%(arg)s (phiBW a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(arg)s.
""" % {'prefix':prefix, 'arg':fearg[2:]}
        else:
            return r"""Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import %(prefix)s.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition %(arg)s :
  { %(arg)s : feBW_small -> feBW_small
  | forall a, phiM_small (%(arg)s a) = F.%(arg)s (phiM_small a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_%(arg)s ().
  Show Ltac Profile.
Time Defined.

Print Assumptions %(arg)s.
""" % {'prefix':prefix, 'arg':fearg[2:]}
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
      feW_bounded x1
      -> feW_bounded (fst Q) /\ feW_bounded (snd Q)
      -> feW_bounded (fst Q') /\ feW_bounded (snd Q')
      -> ((feW_bounded (fst (fst xz)) /\ feW_bounded (snd (fst xz)))
          /\ (feW_bounded (fst (snd xz)) /\ feW_bounded (snd (snd xz))))
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
    if fearg in ('femul', 'fesub', 'feadd', 'fesquare', 'feopp'):
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
        outputs[os.path.basename(fname)] = open(os.path.join(parameters_folder, fname), 'r').read()
    if 'compiler' in parameters.keys():
        outputs['compiler.sh'] = make_compiler(parameters['compiler'])
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
            if fname[-len('compiler.sh'):] == 'compiler.sh':
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
