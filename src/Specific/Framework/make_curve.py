#!/usr/bin/env python
from __future__ import with_statement
import json, sys, os, math, re, shutil

def compute_bitwidth(base):
    return 2**int(math.ceil(math.log(base, 2)))
def compute_sz(modulus, base):
    return 1 + int(math.ceil(math.log(modulus, 2) / base))
def default_carry_chain(cc):
    assert(cc == 'carry_chain1')
    return 'Some (seq 0 (pred sz))'
def compute_s(modulus_str):
    base, exp, rest = re.match(r'\s*'.join(('^', '(2)', r'\^', '([0-9]+)', '([0-9^ +-]*)$')), modulus_str).groups()
    return '%s^%s' % (base, exp)
def compute_c(modulus_str):
    base, exp, rest = re.match(r'\s*'.join(('^', '(2)', r'\^', '([0-9]+)', '([0-9^ +-]*)$')), modulus_str).groups()
    if rest.strip() == '': return '[]'
    assert(rest.strip()[0] == '-')
    rest = negate_numexpr(rest.strip()[1:])
    # XXX FIXME: Is this the right way to extract c?
    return '[(1, %s)]' % rest

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

def make_curve_parameters(parameters):
    replacements = dict(parameters)
    assert(all(ch in '0123456789^+- ' for ch in parameters['modulus']))
    modulus = eval(parameters['modulus'].replace('^', '**'))
    base = float(parameters['base'])
    replacements['bitwidth'] = parameters.get('bitwidth', str(compute_bitwidth(base)))
    bitwidth = int(replacements['bitwidth'])
    replacements['sz'] = parameters.get('sz', str(compute_sz(modulus, base)))
    sz = int(replacements['sz'])
    for cc in ('carry_chain1', 'carry_chain2'):
        if cc in replacements.keys() and isinstance(replacements[cc], list):
            replacements[cc] = 'Some [%s]%%nat' % '; '.join(map(str, replacements[cc]))
        elif replacements[cc] == 'default':
            replacements[cc] = default_carry_chain(cc)
        elif isinstance(replacements[cc], str):
            if replacements[cc][:len('Some ')] != 'Some ' and replacements[cc][:len('None')] != 'None':
                if ' ' in replacements[cc]: replacements[cc] = '(%s)' % replacements[cc]
                replacements[cc] = 'Some %s' % replacements[cc]
        elif cc not in replacements.keys():
            replacements[cc] = 'None'
    replacements['s'] = parameters.get('s', compute_s(parameters['modulus']))
    replacements['c'] = parameters.get('c', compute_c(parameters['modulus']))
    if isinstance(replacements['c'], list):
        replacements['c'] = '[%s]' % '; '.join('(%s, %s)' % (str(w), str(v)) for w, v in replacements['c'])
    for op, nargs in (('mul', 2), ('square', 1)):
        replacements[op] = format_c_code(parameters.get(op + '_header', None),
                                         parameters.get(op + '_code', None),
                                         nargs,
                                         sz)
    for k in ('upper_bound_of_exponent', 'allowable_bit_widths', 'freeze_extra_allowable_bit_widths'):
        if k not in replacements.keys():
            replacements[k] = 'None'
    for k in ('extra_prove_mul_eq', 'extra_prove_square_eq'):
        if k not in replacements.keys():
            replacements[k] = 'idtac'
    ret = r"""Require Import Crypto.Specific.Framework.CurveParameters.
Require Import Crypto.Util.LetIn.

(***
Modulus : %(modulus)s
Base: %(base)s
***)

Module Curve <: CurveParameters.
  Definition sz : nat := %(sz)s%%nat.
  Definition bitwidth : Z := %(bitwidth)s.
  Definition s : Z := %(s)s.
  Definition c : list limb := %(c)s.
  Definition carry_chain1 : option (list nat) := Eval vm_compute in %(carry_chain1)s.
  Definition carry_chain2 : option (list nat) := Eval vm_compute in %(carry_chain2)s.

  Definition a24 : Z := %(a24)s.
  Definition coef_div_modulus : nat := %(coef_div_modulus)s%%nat. (* add %(coef_div_modulus)s*modulus before subtracting *)

  Definition mul_code : option (Z^sz -> Z^sz -> Z^sz)
    := %(mul)s.

  Definition square_code : option (Z^sz -> Z^sz)
    := %(square)s.

  Definition upper_bound_of_exponent : option (Z -> Z) := %(upper_bound_of_exponent)s.
  Definition allowable_bit_widths : option (list nat) := %(allowable_bit_widths)s.
  Definition freeze_extra_allowable_bit_widths : option (list nat) := %(freeze_extra_allowable_bit_widths)s.
  Ltac extra_prove_mul_eq := %(extra_prove_mul_eq)s.
  Ltac extra_prove_square_eq := %(extra_prove_square_eq)s.
End Curve.
""" % replacements
    return ret

def make_synthesis(prefix):
    return r"""Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import %s.CurveParameters.

Module Import T := MakeSynthesisTactics Curve.

Module P <: SynthesisPrePackage.
  Definition Synthesis_package' : Synthesis_package'_Type.
  Proof. make_synthesis_package (). Defined.

  Definition Synthesis_package
    := Eval cbv [Synthesis_package' projT2] in projT2 Synthesis_package'.
End P.

Module Export S := PackageSynthesis Curve P.
""" % prefix

def make_synthesized_arg(fearg, prefix):
    if fearg in ('femul', 'fesub', 'feadd'):
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
""" % {'prefix':prefix}
    elif fearg in ('ladderstep', 'xzladderstep'):
        return r"""Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.Framework.LadderstepSynthesisFramework.
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
""" % {'prefix':prefix}
    else:
        print('ERROR: Unsupported operation: %s' % fearg)
        raise ArgumentError


def make_display_arg(fearg, prefix):
    file_name = fearg
    function_name = fearg
    if fearg in ('femul', 'fesub', 'feadd', 'fesquare'):
        function_name = fearg[2:]
    elif fearg in ('freeze', 'xzladderstep'):
        pass
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
        outputs[arg + '.v'] = make_synthesized_arg(arg, output_prefix)
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
        with open(fname, 'w') as f:
            f.write(outputs[k])
            if fname[-len('compiler.sh'):] == 'compiler.sh':
                mode = os.fstat(f.fileno()).st_mode
                mode |= 0o111
                os.fchmod(f.fileno(), mode & 0o7777)
    if len(new_files) > 0:
        print('git add ' + ' '.join('"%s"' % i for i in new_files))

if __name__ == '__main__':
    main(*sys.argv)
