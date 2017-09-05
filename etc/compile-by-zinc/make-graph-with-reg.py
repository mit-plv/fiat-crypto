#!/usr/bin/env python
from __future__ import with_statement
from memoize import memoize
import codecs, re, sys, os
import subprocess

LAMBDA = u'\u03bb'

OP_NAMES = {'*':'MUL', '+':'ADD', '>>':'SHL', '<<':'SHR', '|':'OR', '&':'AND'}

REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP'] #, 'RSP'] # RSP is stack pointer?
                  + ['r%d' % i for i in range(8, 16)])
REGISTER_COLORS = ['color="black"', 'color="white",fillcolor="black"', 'color="maroon"', 'color="green"', 'fillcolor="olive"',
                   'color="navy"', 'color="purple"', 'fillcolor="teal"', 'fillcolor="silver"', 'fillcolor="gray"', 'fillcolor="red"',
                   'fillcolor="lime"', 'fillcolor="yellow"', 'fillcolor="blue"', 'fillcolor="fuschia"', 'fillcolor="aqua"']
REGISTER_COLORS = ['fillcolor="%s"' % c for c in 'aliceblue antiquewhite aquamarine azure beige bisque blue blueviolet brown cadetblue chartreuse cyan red gold deeppink darkorange'.split(' ')]
COLOR_FOR_REGISTER = dict(zip(REGISTERS, REGISTER_COLORS))

MAX_INSTRUCTION_WINDOW = 10000

def get_lines(filename):
    with codecs.open(filename, 'r', encoding='utf8') as f:
        lines = f.read().replace('\r\n', '\n')
    return [line.strip() for line in re.findall("%s '.*?[Rr]eturn [^\r\n]*" % LAMBDA, lines, flags=re.DOTALL)[0].split('\n')]

def strip_casts(text):
    return re.sub(r'\(u?int[0-9]*_t\)\s*\(?([^\)]*)\)?', r'\1', text)

def parse_lines(lines):
    lines = list(map(strip_casts, lines))
    assert lines[0][:len(LAMBDA + ' ')] == LAMBDA + ' '
    assert lines[0][-1] == ','
    ret = {}
    ret['vars'] = lines[0][len(LAMBDA + ' '):-1]
    assert lines[-1][-1] == ')'
    ret['return'] = lines[-1][:-1].replace('return ', '').replace('Return ', '')
    ret['lines'] = []
    for line in lines[1:-1]:
        datatype, varname, arg1, op, arg2 = re.findall('^(u?int[0-9]*_t) ([^ ]*) = ([^ ]*) ([^ ]*) ([^ ]*);$', line)[0]
        ret['lines'].append({'type':datatype, 'out':varname, 'op':op, 'args':(arg1, arg2), 'source':line})
    print('Compiling %d lines in groups of %d...' % (len(ret['lines']), min(MAX_INSTRUCTION_WINDOW, len(ret['lines']))))
    ret['lines'] = tuple(ret['lines'])
    split_ret = []
    for start in range(0, len(ret['lines']), MAX_INSTRUCTION_WINDOW):
        cur_ret = dict(ret)
        cur_ret['lines'] = ret['lines'][start:][:MAX_INSTRUCTION_WINDOW]
        split_ret.append(cur_ret)
    return tuple(split_ret)

def get_var_names(input_data):
    return tuple(line['out'] for line in input_data['lines'])

def get_input_var_names(input_data):
    return tuple(i for i in data['vars'].replace('%core', '').replace(',', ' ').replace('(', ' ').replace(')', ' ').replace("'", ' ').split(' ')
                 if i != '')

def get_output_var_names(input_data):
    return tuple(i for i in data['return'].replace(',', ' ').replace('(', ' ').replace(')', ' ').split(' ')
                 if i != '')

def line_of_var(input_data, var):
    retv = [line for line in input_data['lines'] if line['out'] == var]
    if len(retv) > 0: return retv[0]
    return {'out': var, 'args':tuple(), 'op': 'INPUT', 'type':'uint64_t'}

def create_set(name, items):
    ret = ''
    ret += 'set of int: %s = 1..%d;\n' % (name, len(items))
    for i, item in enumerate(items):
        ret += '%s: %s = %d; ' % (name, item, i+1)
    ret += 'array[%s] of string: %s_NAMES = ["' % (name, name)
    ret += '", "'.join(items) + '"];\n'
    ret += '\n'
    return ret

def make_data_dependencies(input_data):
    input_var_names = get_input_var_names(input_data)
    dependencies = dict((var, tuple()) for var in input_var_names)
    for line in input_data['lines']:
        dependencies[line['out']] = tuple(arg for arg in line['args']
                                          if arg[0] not in '0123456789')
    return dependencies
def make_reverse_data_dependencies(dependencies):
    ret = {}
    for k, vs in dependencies.items():
        for v in vs:
            if v not in ret.keys(): ret[v] = []
            ret[v].append(k)
    for k in ret.keys():
        ret[k] = tuple(ret[k])
    return ret

def make_reverse_data_dependencies(dependencies):
    reverse_dependencies = dict((k, []) for k in dependencies.keys())
    for k, v in dependencies.items():
        for arg in v:
            reverse_dependencies[arg].append(k)
    return reverse_dependencies

def backpropogate_one(input_data, dependencies, registers):
    progressed = False
    for var in registers.keys():
        if len(dependencies[var]) == 1:
            dep = dependencies[var][0]
            if dep not in registers.keys():
                line = line_of_var(input_data, dep)
                if line['type'] == 'uint64_t' and ':' not in registers[var]:
                    registers[dep] = registers[var]
                    progressed = True
            elif registers[dep] != registers[var] and registers[var] not in registers[dep].split(':') and len(dependencies[dep]) == 2:
                for dep2, other_dep2 in (tuple(dependencies[dep]), tuple(reversed(dependencies[dep]))):
                    if dep2 in registers.keys(): continue
                    if other_dep2 in registers.keys() and registers[other_dep2] == registers[var]: continue
                    line = line_of_var(input_data, dep2)
                    other_line = line_of_var(input_data, other_dep2)
                    if line['type'] == 'uint64_t' and ':' not in registers[var] and (other_dep2 in registers.keys() or other_line['type'] != 'uint64_t'):
                        registers[dep2] = registers[var]
                        progressed = True
        elif len(dependencies[var]) == 2:
            for dep, other_dep in (tuple(dependencies[var]), tuple(reversed(dependencies[var]))):
                if dep in registers.keys(): continue
                if other_dep in registers.keys() and registers[other_dep] == registers[var]: continue
                line = line_of_var(input_data, dep)
                if line['type'] == 'uint64_t' and ':' not in registers[var] and len(dependencies[dep]) == 1 and dependencies[dep][0] in registers.keys():
                    registers[dep] = registers[var]
                    progressed = True
    return progressed, registers
def backpropogate_one_arbitrary(input_data, dependencies, registers):
    progressed = False
    for var in registers.keys():
        if len(dependencies[var]) == 2:
            for dep, other_dep in (tuple(dependencies[var]), tuple(reversed(dependencies[var]))):
                if dep in registers.keys(): continue
                if other_dep in registers.keys() and (registers[other_dep] == registers[var] or registers[var] in registers[other_dep].split(':')): continue
                line = line_of_var(input_data, dep)
                if line['type'] == 'uint64_t' and ':' not in registers[var]:
                    registers[dep] = registers[var]
                    progressed = True
                elif line['type'] == 'uint128_t' and ':' in registers[var] and other_dep not in registers.keys():
                    registers[dep] = registers[var]
                    progressed = True
    return progressed, registers
def backpropogate_128(input_data, dependencies, reverse_dependencies, registers):
    progressed = False
    for var in registers.keys():
        if len(dependencies[var]) == 1 and len(reverse_dependencies[dependencies[var][0]]) == 2:
            var = dependencies[var][0]
            if var in registers.keys(): continue
            for dep, other_dep in (tuple(reverse_dependencies[var]), tuple(reversed(reverse_dependencies[var]))):
                if dep not in registers.keys() or other_dep not in registers.keys(): continue
                line = line_of_var(input_data, dep)
                other_line = line_of_var(input_data, other_dep)
                var_line = line_of_var(input_data, var)
                if var_line['type'] == 'uint128_t' and line['type'] == 'uint64_t' and other_line['type'] == 'uint64_t' and line['op'] == '>>' and other_line['op'] == '&':
                    registers[var] = registers[dep] + ':' + registers[other_dep]
                    progressed = True
    return progressed, registers
def backpropogate_one128(input_data, dependencies, registers):
    progressed = False
    for var in registers.keys():
        var_line = line_of_var(input_data, var)
        if var_line['type'] != 'uint128_t': continue
        if len(dependencies[var]) == 1:
            dep = dependencies[var][0]
            if dep not in registers.keys():
                line = line_of_var(input_data, dep)
                if line['type'] == 'uint128_t' and ':' in registers[var]:
                    registers[dep] = registers[var]
                    progressed = True
        elif len(dependencies[var]) == 2:
            for dep, other_dep in (tuple(dependencies[var]), tuple(reversed(dependencies[var]))):
                if dep in registers.keys(): continue
                if other_dep in registers.keys() and registers[other_dep] == registers[var]: continue
                line = line_of_var(input_data, dep)
                other_line = line_of_var(input_data, other_dep)
                if line['type'] == 'uint128_t' and other_line['type'] == 'uint64_t' and other_dep not in registers.keys() and ':' in registers[var]:
                    registers[dep] = registers[var]
                    progressed = True
                elif line['type'] == 'uint64_t' and other_line['type'] == 'uint64_t' and other_dep not in registers.keys() and ':' in registers[var] and var_line['op'] == '*':
                    registers[dep], registers[other_dep] = registers[var].split(':')
                    progressed = True
    return progressed, registers
def all_reverse_dependencies(reverse_dependencies, var_set):
    ret = set(var_set)
    for v in var_set:
        ret = ret.union(set(reverse_dependencies[v]))
    if len(ret) == len(set(var_set)): return ret
    return all_reverse_dependencies(reverse_dependencies, ret)
def unassigned_reverse_dependencies(reverse_dependencies, registers, var_set):
    return set(v for v in all_reverse_dependencies(reverse_dependencies, var_set) if v not in registers.keys())
def assign_one_new_reg(input_data, dependencies, reverse_dependencies, registers, new_reg):
    for var in registers.keys():
        var_line = line_of_var(input_data, var)
        for dep in dependencies[var]:
            if len(unassigned_reverse_dependencies(reverse_dependencies, registers, [dep])) == 1 and line_of_var(input_data, dep)['type'] == 'uint64_t':
                registers[dep] = new_reg
                return True, registers
    return False, registers

def assign_registers(input_data, dependencies):
    reverse_dependencies = make_reverse_data_dependencies(dependencies)
    registers = {}
    registers_available = list(REGISTERS)
    out_vars = get_output_var_names(input_data)
    for var in out_vars:
        registers[var] = registers_available.pop()
    progressed = True
    while progressed:
        progressed, registers = backpropogate_one(input_data, dependencies, registers)
    progressed1, progressed2 = True, True
    while progressed1 or progressed2:
        progressed1, registers = backpropogate_one(input_data, dependencies, registers)
        progressed2, registers = backpropogate_one_arbitrary(input_data, dependencies, registers)
    progressed5 = True
    max_count = 7
    c = 0
    while c < max_count and progressed5:
        progressed1, progressed2, did_progress = True, True, True
        while progressed1 or progressed2 or did_progress:
            progressed3, progressed4 = True, True
            while progressed3 or progressed4:
                progressed3, registers = backpropogate_128(input_data, dependencies, reverse_dependencies, registers)
                progressed4, registers = backpropogate_one128(input_data, dependencies, registers)
                did_progress = progressed3 or progressed4
            progressed1, registers = backpropogate_one(input_data, dependencies, registers)
            progressed2, registers = backpropogate_one_arbitrary(input_data, dependencies, registers)
        c += 1
        if c < max_count:
            reg, registers_available = registers_available[-1], registers_available[:-1]
            progressed5, registers = assign_one_new_reg(input_data, dependencies, reverse_dependencies, registers, reg)
    return registers

def print_dependencies(input_data, dependencies):
    in_vars = get_input_var_names(input_data)
    out_vars = get_output_var_names(input_data)
    registers = assign_registers(input_data, dependencies)
    body = (
        ''.join('    %s [label="%s (%s)",%s];\n' % (var, var, reg, COLOR_FOR_REGISTER[reg.split(':')[0]]) for var, reg in registers.items()) +
        ''.join('    in -> %s ;\n' % var for var in in_vars) +
        ''.join('    %s -> out ;\n' % var for var in out_vars) +
        ''.join(''.join('    %s -> %s ;\n' % (out_var, in_var) for out_var in sorted(dependencies[in_var]))
                for in_var in sorted(dependencies.keys()))
            )
    return ('digraph G {\n' + body + '}\n')
def adjust_bits(input_data, graph):
    for line in input_data['lines']:
        if line['type'] == 'uint128_t':
            graph = graph.replace(line['out'], line['out'] + '_128')
    return graph


data_list = parse_lines(get_lines('femulDisplay.log'))
for i, data in enumerate(data_list):
    deps = adjust_bits(data, print_dependencies(data, make_data_dependencies(data)))
    with codecs.open('femulData%d.dot' % i, 'w', encoding='utf8') as f:
        f.write(deps)
    for fmt in ('png', 'svg'):
        subprocess.call(['dot', '-T%s' % fmt, 'femulData%d.dot' % i, '-o', 'femulData%d.%s' % (i, fmt)])
