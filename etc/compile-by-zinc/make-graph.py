#!/usr/bin/env python
from __future__ import with_statement
from memoize import memoize
import codecs, re, sys, os
import subprocess

LAMBDA = u'\u03bb'

OP_NAMES = {'*':'MUL', '+':'ADD', '>>':'SHL', '<<':'SHR', '|':'OR', '&':'AND'}

REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP', 'RSP']
                  + ['r%d' % i for i in range(8, 16)])

MAX_INSTRUCTION_WINDOW = 10000

CORE_DATA = (('ADD_MUL', 2), ('MUL_CORE', 1), ('LEA_BW', 2))
CORES = tuple(name for name, count in CORE_DATA)
CORE_COUNT = dict(CORE_DATA)

BITWISE_CORES = tuple({
    'core' : { 'name' : core_name , 'latency' : 1 },
    'latency' : 1
    } for core_name in ('LEA_BW',))

MODEL = {
    '*': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 3
        }
          for core_name in ('ADD_MUL', 'MUL_CORE')),
    '+': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 1
        }
          for core_name in ('ADD_MUL', 'LEA_BW')),
    '>>': BITWISE_CORES,
    '<<': BITWISE_CORES,
    '|': BITWISE_CORES,
    '&': BITWISE_CORES,
    'LOAD': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 1
        } for core_name in REGISTERS),
    'STORE': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 1
        } for core_name in REGISTERS)
    }

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
    reverse_dependencies = {}
    for k, v in dependencies.items():
        for arg in v:
            if arg not in reverse_dependencies.keys(): reverse_dependencies[arg] = []
            reverse_dependencies[arg].append(k)
    return reverse_dependencies

def print_dependencies(input_data, dependencies):
    in_vars = get_input_var_names(input_data)
    out_vars = get_output_var_names(input_data)
    return ('digraph G {\n' +
            ''.join('    in -> %s ;\n' % var for var in in_vars) +
            ''.join('    %s -> out ;\n' % var for var in out_vars) +
            ''.join(''.join('    %s -> %s ;\n' % (out_var, in_var) for out_var in sorted(dependencies[in_var]))
                    for in_var in sorted(dependencies.keys())) +
            '}\n')
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
