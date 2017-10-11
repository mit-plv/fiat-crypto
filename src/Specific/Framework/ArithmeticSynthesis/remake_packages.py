#!/usr/bin/env python
from __future__ import with_statement
import re, os
import io

PACKAGE_NAMES = [('../CurveParameters.v', [])]
CP_LIST = ['../CurveParametersPackage.v']
CP_BASE_LIST = ['../CurveParametersPackage.v', 'BasePackage.v']
CP_BASE_DEFAULTS_LIST = ['../CurveParametersPackage.v', 'BasePackage.v', 'DefaultsPackage.v']
CP_BASE_DEFAULTS_FREEZE_LADDERSTEP_LIST = ['../CurveParametersPackage.v', 'BasePackage.v', 'DefaultsPackage.v', 'FreezePackage.v', 'LadderstepPackage.v']
NORMAL_PACKAGE_NAMES = [('Base.v', (CP_LIST, None)),
                        ('Defaults.v', (CP_BASE_LIST, 'not_exists')),
                        ('../ReificationTypes.v', (CP_BASE_LIST, None)),
                        ('Freeze.v', (CP_BASE_LIST, 'not_exists')),
                        ('Ladderstep.v', (CP_BASE_DEFAULTS_LIST, 'not_exists')),
                        ('Karatsuba.v', (CP_BASE_DEFAULTS_LIST, 'goldilocks'))]
ALL_FILE_NAMES = PACKAGE_NAMES + NORMAL_PACKAGE_NAMES # PACKAGE_CP_NAMES + WITH_CURVE_BASE_NAMES + ['../ReificationTypes.v']
CONFIGS = ('goldilocks', )

EXCLUDES = ('constr:((wt_divides_chain, wt_divides_chains))', )

contents = {}
lines = {}
fns = {}

PY_FILE_NAME = os.path.basename(__file__)

def init_contents(lines=lines, contents=contents):
    for fname, _ in ALL_FILE_NAMES:
        with open(fname, 'r') as f:
            contents[fname] = f.read()
    lines.update(dict((k, v.split('\n')) for k, v in contents.items()))

def strip_prefix(name, prefix='local_'):
    if name.startswith(prefix): return name[len(prefix):]
    return name

def init_fns(lines=lines, fns=fns):
    header = 'Ltac pose_'
    for fname, _ in ALL_FILE_NAMES:
        stripped_lines = [i.strip() for i in lines[fname]]
        fns[fname] = [(strip_prefix(name, 'local_'), args.strip(), name.startswith('local_'))
                      for line in stripped_lines
                      if line.startswith(header)
                      for name, args in re.findall('Ltac pose_([^ ]*' + ') ([A-Za-z0-9_\' ]*' + ')', line.strip())]

def get_file_root(folder=os.path.dirname(__file__), filename='Makefile'):
    dir_path = os.path.realpath(folder)
    while not os.path.isfile(os.path.join(dir_path, filename)) and dir_path != '/':
        dir_path = os.path.realpath(os.path.join(dir_path, '..'))
    if not os.path.isfile(os.path.join(dir_path, filename)):
        print('ERROR: Could not find Makefile in the root of %s' % folder)
        raise Exception
    return dir_path

def modname_of_file_name(fname):
    assert(fname[-2:] == '.v')
    return 'Crypto.' + os.path.normpath(os.path.relpath(os.path.realpath(fname), os.path.join(root, 'src'))).replace(os.sep, '.')[:-2]

def split_args(name, args_str, indent=''):
    args = [arg.strip() for arg in args_str.split(' ')]
    pass_args = [arg for arg in args if arg.startswith('P_')]
    extract_args = [arg for arg in args if arg not in pass_args and arg != name]
    if name not in args:
        print('Error: %s not in %s' % (name, repr(args)))
        assert(name in args)
    assert(len(pass_args) + len(extract_args) + 1 == len(args))
    pass_args_str = ' '.join(pass_args)
    if pass_args_str != '': pass_args_str += ' '
    extract_args_str = ''
    nl_indent = ('\n%(indent)s  ' % locals())
    if len(extract_args) > 0:
        extract_args_str = nl_indent + nl_indent.join('let %s := Tag.get pkg TAG.%s in' % (arg, arg) for arg in extract_args)
    return args, pass_args, extract_args, pass_args_str, extract_args_str

def make_add_from_pose(name, args_str, indent='', only_if=None, local=False):
    args, pass_args, extract_args, pass_args_str, extract_args_str = split_args(name, args_str, indent=indent)
    ret = r'''%(indent)sLtac add_%(name)s pkg %(pass_args_str)s:=''' % locals()
    local_str = ('local_' if local else '')
    if_not_exists_str = ''
    body = r'''%(extract_args_str)s
%(indent)s  let %(name)s := fresh "%(name)s" in
%(indent)s  ''' % locals()
    body += r'''let %(name)s := pose_%(local_str)s%(name)s %(args_str)s in
%(indent)s  ''' % locals()
    if only_if == 'not_exists':
        assert(not local)
        body += 'constr:(%(name)s)' % locals()
        body = body.strip('\n ').replace('\n', '\n                 ')
        ret += r'''
%(indent)s  Tag.update_by_tac_if_not_exists
%(indent)s    pkg
%(indent)s    TAG.%(name)s
%(indent)s    ltac:(fun _ => %(body)s).''' % locals()
    else:
        body += r'''Tag.%(local_str)supdate pkg TAG.%(name)s %(name)s''' % locals()
        if only_if is None:
            ret += body + '.\n'
        else:
            body = body.strip('\n ').replace('\n', '\n                 ')
            ret += r'''
%(indent)s  if_%(only_if)s
%(indent)s    pkg
%(indent)s    ltac:(fun _ => %(body)s)
%(indent)s    ltac:(fun _ => pkg)
%(indent)s    ().''' % locals()
    return ret

def make_add_all(fname, indent=''):
    modname, ext = os.path.splitext(os.path.basename(fname))
    all_items = [(name, split_args(name, args_str, indent=indent)) for name, args_str, local in fns[fname]]
    all_pass_args = []
    for name, (args, pass_args, extract_args, pass_args_str, extract_args_str) in all_items:
        for arg in pass_args:
            if arg not in all_pass_args: all_pass_args.append(arg)
    all_pass_args_str = ' '.join(all_pass_args)
    if all_pass_args_str != '': all_pass_args_str += ' '
    ret = r'''%(indent)sLtac add_%(modname)s_package pkg %(all_pass_args_str)s:=''' % locals()
    nl_indent = ('\n%(indent)s  ' % locals())
    ret += nl_indent + nl_indent.join('let pkg := add_%s pkg %sin' % (name, pass_args_str)
                                      for name, (args, pass_args, extract_args, pass_args_str, extract_args_str) in all_items)
    ret += nl_indent + 'Tag.strip_local pkg.\n'
    return ret

def make_if(name, indent=''):
    ret = r'''%(indent)sLtac if_%(name)s pkg tac_true tac_false arg :=
%(indent)s  let %(name)s := Tag.get pkg TAG.%(name)s in
%(indent)s  let %(name)s := (eval vm_compute in (%(name)s : bool)) in
%(indent)s  lazymatch %(name)s with
%(indent)s  | true => tac_true arg
%(indent)s  | false => tac_false arg
%(indent)s  end.
''' % locals()
    return ret

def write_if_changed(fname, value):
    if os.path.isfile(fname):
        with open(fname, 'r') as f:
            old_value = f.read()
        if old_value == value: return
    value = unicode(value)
    print('Writing %s...' % fname)
    with io.open(fname, 'w', newline='\n') as f:
        f.write(value)

def do_replace(fname, headers, new_contents):
    lines = contents[fname].split('\n')
    ret = []
    for line in lines:
        if any(header in line for header in headers):
            ret.append(new_contents)
            break
        else:
            ret.append(line)
    ret = unicode('\n'.join(ret))
    write_if_changed(fname, ret)

def get_existing_tags(fname, deps):
    return set(name for dep in deps for name, args, local in fns[dep.replace('Package.v', '.v')])

def make_package(fname, deps, extra_modname_prefix='', extra_imports=None, prefix=None, add_package=True):
    py_file_name = PY_FILE_NAME
    existing_tags = get_existing_tags(fname, deps)
    full_mod = modname_of_file_name(fname)
    modname, ext = os.path.splitext(os.path.basename(fname))
    ret = (r'''(* This file is autogenerated from %(modname)s.v by %(py_file_name)s *)
''' % locals())
    if extra_imports is not None:
        ret += extra_imports
    ret += (r'''Require Export %(full_mod)s.
Require Import Crypto.Specific.Framework.Packages.
Require Import Crypto.Util.TagList.
''' % locals())
    if prefix is not None:
        ret += prefix
    new_names = [name for name, args, local in fns[fname] if name not in existing_tags and not local]
    if add_package: # and len(new_names) > 0:
        ret += (r'''

Module Make%(extra_modname_prefix)s%(modname)sPackage (PKG : PrePackage).
  Module Import Make%(extra_modname_prefix)s%(modname)sPackageInternal := MakePackageBase PKG.
''' % locals())
        for name in new_names:
            ret += ("\n  Ltac get_%s _ := get TAG.%s." % (name, name))
            ret += ("\n  Notation %s := (ltac:(let v := get_%s () in exact v)) (only parsing)." % (name, name))
        ret += ('\nEnd Make%(extra_modname_prefix)s%(modname)sPackage.\n' % locals())
    return ret

def make_tags(fname, deps):
    existing_tags = get_existing_tags(fname, deps)
    new_tags = [name for name, args, local in fns[fname] if name not in existing_tags]
    if len(new_tags) == 0: return ''
    names = ' | '.join(new_tags)
    return r'''Module TAG.
  Inductive tags := %s.
End TAG.
''' % names

def write_package(fname, pkg):
    pkg_name = fname[:-2] + 'Package.v'
    write_if_changed(pkg_name, pkg)

def update_CurveParameters(fname='../CurveParameters.v'):
    endline = contents[fname].strip().split('\n')[-1]
    assert(endline.startswith('End '))
    header = '(* Everything below this line autogenerated by %s *)' % PY_FILE_NAME
    assert(header in contents[fname])
    ret = '  %s' % header
    for name, args, local in fns[fname]:
        ret += '\n' + make_add_from_pose(name, args, indent='  ', local=local)
    ret += '\n' + make_add_all(fname, indent='  ')
    ret += endline
    prefix = ''
    for name in CONFIGS:
        prefix += '\n' + make_if(name, indent='')
    pkg = make_package(fname, [], prefix=prefix)
    do_replace(fname, (header,), ret)
    write_package(fname, pkg)

def make_normal_package(fname, deps, only_if=None):
    prefix = ''
    extra_imports = ''
    for dep in deps:
        extra_imports += 'Require Import %s.\n' % modname_of_file_name(dep)
    prefix += '\n' + make_tags(fname, deps)
    for name, args, local in fns[fname]:
        prefix += '\n' + make_add_from_pose(name, args, indent='', only_if=only_if, local=local)
    prefix += '\n' + make_add_all(fname, indent='')
    return make_package(fname, deps, extra_imports=extra_imports, prefix=prefix)

def update_normal_package(fname, deps, only_if=None):
    pkg = make_normal_package(fname, deps, only_if=only_if)
    write_package(fname, pkg)

root = get_file_root()
init_contents()
init_fns()
update_CurveParameters()
for fname, (deps, only_if) in NORMAL_PACKAGE_NAMES:
    update_normal_package(fname, deps, only_if=only_if)
