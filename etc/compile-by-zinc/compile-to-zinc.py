#!/usr/bin/env python
from __future__ import with_statement
import codecs, re
import subprocess

LAMBDA = u'\u03bb'

CORES = ('ADD_MUL0', 'ADD_MUL1', 'MUL0', 'LEA_BW0', 'LEA_BW1')

MAX_INSTRUCTION_WINDOW = 4

INSTRUCTIONS_PER_CYCLE = 4

BITWISE_CORES = tuple({
    'core' : { 'name' : core_name , 'latency' : 1 },
    'latency' : 1
    } for core_name in ('LEA_BW0', 'LEA_BW1'))

MODEL = {
    '*': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 3
        }
          for core_name in ('ADD_MUL0', 'ADD_MUL1', 'MUL0')),
    '+': tuple({
        'core' : { 'name' : core_name , 'latency' : 1 },
        'latency' : 1
        }
          for core_name in ('ADD_MUL0', 'ADD_MUL1', 'LEA_BW0', 'LEA_BW1')),
    '>>': BITWISE_CORES,
    '<<': BITWISE_CORES,
    '|': BITWISE_CORES,
    '&': BITWISE_CORES
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
    print('Compiling %d of %d lines...' % (MAX_INSTRUCTION_WINDOW, len(ret['lines'])))
    ret['lines'] = ret['lines'][:MAX_INSTRUCTION_WINDOW]
    return ret

def get_var_names(input_data):
    return tuple(line['out'] for line in input_data['lines'])

def get_input_var_names(input_data):
    return tuple(i for i in data['vars'].replace('%core', '').replace(',', ' ').replace('(', ' ').replace(')', ' ').replace("'", ' ').split(' ')
                 if i != '')


def make_decls(input_data):
    var_names = get_var_names(input_data)
    ret = ''
    ret += 'set of int: CORE = 1..%d;\n' % len(CORES)
    for i, core in enumerate(CORES):
        ret += 'CORE: %s = %d; ' % (core, i+1)
    ret += '\n'
    for var in var_names:
        ret += 'var int: %s_loc;\n' % var
        ret += 'var int: %s_latency;\n' % var
        ret += 'var CORE: %s_core;\n' % var
    ret += 'var int: RET_loc;\n'
    return ret

def make_disjoint(input_data):
    var_names = get_var_names(input_data)
    ret = ''
    for var in var_names:
        ret += 'constraint %s_loc >= 0;\n' % var
        ret += 'constraint %s_latency >= 0;\n' % var
        ret += 'constraint %s_loc + %s_latency <= RET_loc;\n' % (var, var)
    # TODO: Figure out if this next constraint actually helps things....
    MAX_NUMBER_OF_NOPS_PER_INSTRUCTION = 3
    APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
    max_ret_loc = ('constraint RET_loc <= %d;\n'
                   % (len(var_names)
                      * MAX_NUMBER_OF_NOPS_PER_INSTRUCTION
                      + APPROXIMATE_MAX_LATENCY))
    #ret += max_ret_loc
    ret += '\n'
    for var_i in range(len(var_names)):
        for var_j in range(var_i+1, len(var_names)):
            ret += 'constraint %s_loc != %s_loc;\n' % (var_names[var_i], var_names[var_j])
    ret += '\n'
    return ret

def make_dependencies(input_data):
    var_names = get_var_names(input_data)
    ret = ''
    for line in input_data['lines']:
        for arg in line['args']:
            if arg in var_names and arg[0] not in '0123456789':
                ret += ('constraint %s_loc + %s_latency <= %s_loc;\n'
                        % (arg, arg, line['out']))
    ret += '\n'
    return ret

def make_cores(input_data):
    ret = ''
    for line in input_data['lines']:
        ret += 'constraint '
        possible_cores = []
        cores = MODEL[line['op']]
        for core in cores:
            possible_cores.append('(%s_latency == %d /\ %s_core == %s)'
                                  % (line['out'], core['latency'] * INSTRUCTIONS_PER_CYCLE,
                                     line['out'], core['core']['name']))
        ret += ' \/ '.join(possible_cores)
        ret += ';\n'
    return ret

def make_cores_disjoint(input_data):
    var_names = get_var_names(input_data)
    ret = ''
    for core in CORES:
        for var_i in range(len(var_names)):
            for var_j in range(var_i+1, len(var_names)):
                op_i = input_data['lines'][var_i]['op']
                op_j = input_data['lines'][var_j]['op']
                latencies_i = [val['core']['latency'] for val in MODEL[op_i] if val['core']['name'] == core]
                latencies_j = [val['core']['latency'] for val in MODEL[op_j] if val['core']['name'] == core]
                if len(latencies_i) == 0 or len(latencies_j) == 0: continue
                assert len(latencies_i) == 1
                assert len(latencies_j) == 1
                ret += ('constraint (%(vari)s_core != %(core)s \\/ %(varj)s_core != %(core)s) \\/ (%(vari)s_loc + %(latencyi)d <= %(varj)s_loc \\/ %(varj)s_loc + %(latencyj)d <= %(vari)s_loc);\n'
                        % { 'vari':var_names[var_i] , 'varj':var_names[var_j] , 'core':core ,
                            'latencyi':latencies_i[0] * INSTRUCTIONS_PER_CYCLE,
                            'latencyj':latencies_j[0] * INSTRUCTIONS_PER_CYCLE})
    ret += '\n'
    return ret

def make_output(input_data):
    ret = 'solve minimize RET_loc;\n\n'
    ret += 'output [ "{\\n" ++\n'
    for line in input_data['lines']:
        ret += ('         "  \'%(var)s_loc\': " ++ show(%(var)s_loc) ++ ", \'%(var)s_latency\': " ++ show(%(var)s_latency) ++ ", \'%(var)s_core\': " ++ show(%(var)s_core) ++ ",\\n" ++\n         %% %(source)s\n'
                % { 'var':line['out'] , 'source':line['source'] })
    ret += '         "  \'RET_loc\': " ++ show(RET_loc) ++ "\\n" ++\n'
    ret += '         "}" ]\n'
    return ret


data = parse_lines(get_lines('femulDisplay.log'))
with open('femulDisplay.mzn', 'w') as f:
    f.write(make_decls(data))
    f.write(make_disjoint(data))
    f.write(make_dependencies(data))
    f.write(make_cores(data))
    f.write(make_cores_disjoint(data))
    f.write(make_output(data))

p = subprocess.Popen(['/usr/bin/time', '-f', 'real: %e, user: %U, sys: %S, mem: %M ko', 'minizinc', 'femulDisplay.mzn'])
p.communicate()
