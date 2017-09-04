#!/usr/bin/env python
from __future__ import with_statement
import codecs, re

LAMBDA = u'\u03bb'

CORES = ('ADD_MUL0', 'ADD_MUL1', 'MUL0', 'LEA_BW0', 'LEA_BW1', 'NOOP_CORE')

OP_NAMES = {'*':'MUL', '+':'ADD', '>>':'SHL', '<<':'SHR', '|':'OR', '&':'AND'}

MAX_INSTRUCTION_WINDOW = 53

INSTRUCTIONS_PER_CYCLE = 4

REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP', 'RSP']
                  + ['r%d' % i for i in range(8, 16)])

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

########################################################################
########################################################################
####                Assign locations to instructions                  ##
########################################################################
########################################################################
##def make_assign_locations_to_instructions(data):
##    def make_decls(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        ret += create_set('CORE', CORES)
##        for var in var_names:
##            ret += 'var int: %s_loc;\n' % var
##            ret += 'var int: %s_latency;\n' % var
##            ret += 'var CORE: %s_core;\n' % var
##        ret += 'var int: RET_loc;\n'
##        return ret
##
##    def make_disjoint(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        for var in var_names:
##            ret += 'constraint %s_loc >= 0;\n' % var
##            ret += 'constraint %s_latency >= 0;\n' % var
##            ret += 'constraint %s_loc + %s_latency <= RET_loc;\n' % (var, var)
##        # TODO: Figure out if this next constraint actually helps things....
##        MAX_NUMBER_OF_NOPS_PER_INSTRUCTION = 3
##        APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
##        max_ret_loc = ('constraint RET_loc <= %d;\n'
##                       % (len(var_names)
##                          * MAX_NUMBER_OF_NOPS_PER_INSTRUCTION
##                          + APPROXIMATE_MAX_LATENCY))
##        #ret += max_ret_loc
##        ret += '\n'
##        for var_i in range(len(var_names)):
##            for var_j in range(var_i+1, len(var_names)):
##                ret += 'constraint %s_loc != %s_loc;\n' % (var_names[var_i], var_names[var_j])
##        ret += '\n'
##        return ret
##
##    def make_dependencies(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        for line in input_data['lines']:
##            for arg in line['args']:
##                if arg in var_names and arg[0] not in '0123456789':
##                    ret += ('constraint %s_loc + %s_latency <= %s_loc;\n'
##                            % (arg, arg, line['out']))
##        ret += '\n'
##        return ret
##
##    def make_cores(input_data):
##        ret = ''
##        for line in input_data['lines']:
##            ret += 'constraint '
##            possible_cores = []
##            cores = MODEL[line['op']]
##            for core in cores:
##                possible_cores.append('(%s_latency == %d /\ %s_core == %s)'
##                                      % (line['out'], core['latency'] * INSTRUCTIONS_PER_CYCLE,
##                                         line['out'], core['core']['name']))
##            ret += ' \/ '.join(possible_cores)
##            ret += ';\n'
##        return ret
##
##    def make_cores_disjoint(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        for core in CORES:
##            for var_i in range(len(var_names)):
##                for var_j in range(var_i+1, len(var_names)):
##                    op_i = input_data['lines'][var_i]['op']
##                    op_j = input_data['lines'][var_j]['op']
##                    latencies_i = [val['core']['latency'] for val in MODEL[op_i] if val['core']['name'] == core]
##                    latencies_j = [val['core']['latency'] for val in MODEL[op_j] if val['core']['name'] == core]
##                    if len(latencies_i) == 0 or len(latencies_j) == 0: continue
##                    assert len(latencies_i) == 1
##                    assert len(latencies_j) == 1
##                    ret += ('constraint (%(vari)s_core != %(core)s \\/ %(varj)s_core != %(core)s) \\/ (%(vari)s_loc + %(latencyi)d <= %(varj)s_loc \\/ %(varj)s_loc + %(latencyj)d <= %(vari)s_loc);\n'
##                            % { 'vari':var_names[var_i] , 'varj':var_names[var_j] , 'core':core ,
##                                'latencyi':latencies_i[0] * INSTRUCTIONS_PER_CYCLE,
##                                'latencyj':latencies_j[0] * INSTRUCTIONS_PER_CYCLE})
##        ret += '\n'
##        return ret
##
##    def make_output(input_data):
##        ret = 'solve minimize RET_loc;\n\n'
##        ret += 'output [ "{\\n" ++\n'
##        for line in input_data['lines']:
##            ret += ('         "  \'%(var)s_loc\': " ++ show(%(var)s_loc) ++ ", \'%(var)s_latency\': " ++ show(%(var)s_latency) ++ ", \'%(var)s_core\': " ++ show(%(var)s_core) ++ ",\\n" ++\n         %% %(source)s\n'
##                    % { 'var':line['out'] , 'source':line['source'] })
##        ret += '         "  \'RET_loc\': " ++ show(RET_loc) ++ "\\n" ++\n'
##        ret += '         "}" ]\n'
##        return ret
##
##    return '\n'.join([
##        make_decls(data),
##        make_disjoint(data),
##        make_dependencies(data),
##        make_cores(data),
##        make_cores_disjoint(data),
##        make_output(data)
##        ])
##
##
########################################################################
########################################################################
####                Assign instructions to locations                  ##
########################################################################
########################################################################
##
##def make_assign_instructions_to_locations(data):
##    def make_decls(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        ret += 'include "alldifferent.mzn";\n'
##        ret += create_set('CORE', CORES)
##        ret += create_set('INSTRUCTION', ['NOOP'] + list(var_names))
##        MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION = 3
##        APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
##        max_loc = len(var_names) * MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION # + APPROXIMATE_MAX_LATENCY
##        ret += 'int: MAX_LOC = %d;\n\n' % max_loc
##        ret += 'array[1..MAX_LOC] of var INSTRUCTION: output_instructions;\n'
##        ret += 'array[1..MAX_LOC] of var CORE: output_cores;\n'
##        ret += 'array[1..MAX_LOC] of var int: output_core_latency;\n'
##        ret += 'array[1..MAX_LOC] of var int: output_data_latency;\n'
##        ret += 'var int: RET_loc;\n'
##        ret += '\n'
##        ret += 'constraint 1 <= RET_loc /\\ RET_loc <= MAX_LOC;\n'
##        ret += '\n'
##        return ret
##
##    def make_disjoint(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        #ret += 'constraint alldifferent( [ output_instructions[i] | i in 1..MAX_LOC where output_instructions[i] != NOOP ] );\n'
##        ret += 'constraint forall (i,j in 1..MAX_LOC where i < j) (output_instructions[i] == NOOP \\/ output_instructions[i] != output_instructions[j]);\n'
##        ret += 'constraint sum( [ 1 | i in 1..MAX_LOC where output_instructions[i] != NOOP ] ) == length(INSTRUCTION) - 1;\n'
##        ret += 'constraint forall (i in 1..MAX_LOC where RET_loc <= i) (output_instructions[i] == NOOP);\n'
##        ret += 'constraint forall (i,j in 1..MAX_LOC where i < j) ((output_instructions[i] != NOOP /\\ output_instructions[j] != NOOP /\\ output_cores[i] == output_cores[j]) -> i + output_core_latency[i] <= j);\n'
##        ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == NOOP \\/ i + output_data_latency[i] <= RET_loc);\n'
##        ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == NOOP -> (output_core_latency[i] == 0 /\\ output_data_latency[i] == 0 /\\ output_cores[i] == NOOP_CORE));\n'
##        return ret
##
##    def make_dependencies(input_data):
##        var_names = get_var_names(input_data)
##        ret = ''
##        for line in input_data['lines']:
##            for arg in line['args']:
##                if arg in var_names and arg[0] not in '0123456789':
##                    ret += ('constraint forall (i,j in 1..MAX_LOC) ((output_instructions[i] == %s /\\ output_instructions[j] == %s) -> i + output_data_latency[i] <= j);\n'
##                            % (arg, line['out']))
##        ret += '\n'
##        return ret
##
##    def make_cores(input_data):
##        ret = ''
##        for line in input_data['lines']:
##            ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == %s -> (' % line['out']
##            possible_cores = []
##            cores = MODEL[line['op']]
##            for core in cores:
##                possible_cores.append(r'(output_core_latency[i] == %d /\ output_data_latency[i] == %d /\ output_cores[i] == %s)'
##                                      % (core['core']['latency'] * INSTRUCTIONS_PER_CYCLE,
##                                         core['latency'] * INSTRUCTIONS_PER_CYCLE,
##                                         core['core']['name']))
##            ret += ' \/ '.join(possible_cores)
##            ret += '));\n'
##        ret += '\n'
##        return ret
##
##    def make_output(input_data):
##        ret = 'solve minimize RET_loc;\n\n'
##        ret += 'output [ "(" ++ show(INSTRUCTION_NAMES[fix(output_instructions[i])]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_core_latency[i]) ++ ", " ++ show(output_data_latency[i]) ++ ") ,\\n"\n'
##        ret += '       | i in 1..MAX_LOC ];\n'
##        return ret
##
##    return '\n'.join([
##        make_decls(data),
##        make_disjoint(data),
##        make_dependencies(data),
##        make_cores(data),
##        make_output(data)
##        ])

######################################################################
######################################################################
##                Assign locations to instructions cumulatively     ##
######################################################################
######################################################################

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
    '&': BITWISE_CORES
    }


def make_assign_locations_to_instructions_cumulatively(data):
    def make_decls(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        ret += 'include "alldifferent.mzn";\n'
        ret += 'include "cumulative.mzn";\n'
        for line in input_data['lines']:
            ret += '%%%s\n' % line['source']
        ret += create_set('CORE', CORES)
        ret += create_set('INSTRUCTIONS', list(var_names))
        ret += create_set('OPS', list(OP_NAMES.values()))
        MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION = 3
        APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
        max_loc = len(var_names) * MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION + APPROXIMATE_MAX_LATENCY
        ret += 'int: MAX_LOC = %d;\n\n' % max_loc
        ret += 'set of int: LOCATIONS = 1..MAX_LOC;\n'
        ret += 'array[INSTRUCTIONS] of var LOCATIONS: output_locations;\n'
        ret += 'array[INSTRUCTIONS] of var int: output_data_latency;\n'
        ret += 'array[INSTRUCTIONS] of var int: output_core_latency;\n'
        ret += 'array[INSTRUCTIONS] of var CORE: output_cores;\n'
        ret += 'array[INSTRUCTIONS] of OPS: input_ops = [%s];\n' % ', '.join(OP_NAMES[line['op']] for line in input_data['lines'])
        for core in CORES:
            ret += 'array[INSTRUCTIONS] of var int: output_%s_core_latency;\n' % core
            ret += 'array[INSTRUCTIONS] of var 0..1: output_%s_core_use;\n' % core
            ret += 'constraint forall (i in INSTRUCTIONS) (0 <= output_%s_core_latency[i]);\n' % core
            ret += 'constraint forall (i in INSTRUCTIONS) (output_%s_core_use[i] == 1 -> output_core_latency[i] == output_%s_core_latency[i]);\n' % (core, core)
        ret += 'var LOCATIONS: RET_loc;\n'
        ret += '\n'
        return ret

    def make_cores(input_data):
        ret = ''
        for opc, cores in MODEL.items():
            possible_cores = []
            for core in cores:
                conjuncts = (['output_cores[i] == %s' % core['core']['name'],
                              'output_%s_core_use[i] == 1' % core['core']['name'],
                              'output_%s_core_latency[i] == %d' % (core['core']['name'], core['core']['latency'] * INSTRUCTIONS_PER_CYCLE),
                              'output_data_latency[i] == %d' % (core['latency'] * INSTRUCTIONS_PER_CYCLE)] +
                             ['output_%s_core_use[i] == 0 /\ output_%s_core_latency[i] == 0' % (other_core, other_core)
                              for other_core in CORES if other_core != core['core']['name']])
                possible_cores.append('(%s)' % (r' /\ '.join(conjuncts)))
            ret += ('constraint forall (i in INSTRUCTIONS) (input_ops[i] == %s -> (%s));\n'
                    % (OP_NAMES[opc], r' \/ '.join(possible_cores)))
        ret += '\n'
        for core in CORES:
            ret += ('constraint cumulative(output_locations, output_%s_core_latency, output_%s_core_use, %d);\n'
                    % (core, core, CORE_COUNT[core]))
        return ret

    def make_disjoint(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        ret += 'constraint alldifferent(output_locations);\n'
        return ret

    def make_dependencies(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        for line in input_data['lines']:
            for arg in line['args']:
                if arg in var_names and arg[0] not in '0123456789':
                    ret += ('constraint output_locations[%s] + output_data_latency[%s] <= output_locations[%s];\n'
                            % (arg, arg, line['out']))
        ret += '\n'
        ret += 'constraint max([ output_locations[i] + output_data_latency[i] | i in INSTRUCTIONS ]) <= RET_loc;\n'
        ret += '\n'
        return ret

    def make_dependencies_alt(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        dependencies = {}
        for line in input_data['lines']:
            dependencies[line['out']] = tuple(arg for arg in line['args']
                                              if arg in var_names and arg[0] not in '0123456789')
            dependencies_array = [['1' if arg1 in dependencies.get(arg2, tuple()) else '0'
                                   for arg2 in var_names]
                                  for arg1 in var_names]
        ret += 'array[INSTRUCTIONS,INSTRUCTIONS] of 0..1: depends_on =\n'
        ret += '  [|' + ',\n  | '.join(', '.join(row) for row in dependencies_array) + ' |];\n'
        ret += '\n'
        ret += 'constraint forall (i,j in INSTRUCTIONS) (depends_on[i,j] == 1 -> output_locations[i] + output_data_latency[i] <= output_locations[j]);\n'
        ret += '\n'
        ret += 'constraint max([ output_locations[i] + output_data_latency[i] | i in INSTRUCTIONS ]) <= RET_loc;\n'
        ret += '\n'
        return ret
    

    def make_output(input_data):
        ret = 'solve minimize RET_loc;\n\n'
        ret += 'output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(output_data_latency[i]) ++ ", " ++ show(output_core_latency[i]) ++ ") ,\\n"\n'
        ret += '       | i in INSTRUCTIONS ];\n'
        ret += 'output [ "RET_loc: " ++ show(RET_loc) ];\n'
        return ret

    return '\n'.join([
        make_decls(data),
        make_disjoint(data),
        make_dependencies(data),
        make_cores(data),
        make_output(data)
        ])


RESULTS = [
"""("x20", "ADD_MUL", 9, 12, 4) ,
("x21", "ADD_MUL", 21, 12, 4) ,
("x22", "ADD_MUL", 10, 12, 4) ,
("x23", "ADD_MUL", 34, 4, 4) ,
("x24", "ADD_MUL", 47, 12, 4) ,
("x25", "ADD_MUL", 43, 12, 4) ,
("x26", "ADD_MUL", 59, 4, 4) ,
("x27", "ADD_MUL", 51, 12, 4) ,
("x28", "ADD_MUL", 63, 4, 4) ,
("x29", "ADD_MUL", 75, 12, 4) ,
("x30", "ADD_MUL", 71, 12, 4) ,
("x31", "ADD_MUL", 87, 4, 4) ,
("x32", "ADD_MUL", 79, 12, 4) ,
("x33", "ADD_MUL", 91, 4, 4) ,
("x34", "ADD_MUL", 82, 12, 4) ,
("x35", "ADD_MUL", 95, 4, 4) ,
("x36", "ADD_MUL", 58, 12, 4) ,
("x37", "ADD_MUL", 55, 12, 4) ,
("x38", "ADD_MUL", 70, 4, 4) ,
("x39", "ADD_MUL", 62, 12, 4) ,
("x40", "ADD_MUL", 74, 4, 4) ,
("x41", "ADD_MUL", 66, 12, 4) ,
("x42", "ADD_MUL", 78, 4, 4) ,
("x43", "ADD_MUL", 90, 12, 4) ,
("x44", "ADD_MUL", 102, 4, 4) ,
("x45", "ADD_MUL", 1, 12, 4) ,
("x46", "ADD_MUL", 2, 12, 4) ,
("x47", "ADD_MUL", 5, 12, 4) ,
("x48", "ADD_MUL", 6, 12, 4) ,
("x49", "ADD_MUL", 13, 12, 4) ,
("x50", "ADD_MUL", 25, 4, 4) ,
("x51", "ADD_MUL", 14, 12, 4) ,
("x52", "ADD_MUL", 29, 4, 4) ,
("x53", "ADD_MUL", 17, 12, 4) ,
("x54", "ADD_MUL", 33, 4, 4) ,
("x55", "ADD_MUL", 18, 12, 4) ,
("x56", "ADD_MUL", 37, 4, 4) ,
("x57", "ADD_MUL", 22, 12, 4) ,
("x58", "ADD_MUL", 38, 4, 4) ,
("x59", "ADD_MUL", 30, 12, 4) ,
("x60", "ADD_MUL", 42, 4, 4) ,
("x61", "ADD_MUL", 26, 12, 4) ,
("x62", "ADD_MUL", 46, 4, 4) ,
("x63", "ADD_MUL", 54, 12, 4) ,
("x64", "ADD_MUL", 67, 4, 4) ,
("x65", "ADD_MUL", 86, 12, 4) ,
("x66", "ADD_MUL", 98, 4, 4) ,
("x67", "ADD_MUL", 83, 12, 4) ,
("x68", "ADD_MUL", 99, 4, 4) ,
("x69", "LEA_BW", 41, 4, 4) ,
("x70", "LEA_BW", 44, 4, 4) ,
("x71", "ADD_MUL", 50, 4, 4) ,
("x72", "LEA_BW", 56, 4, 4) ,
RET_loc: 106"""
,
"""("x73", "LEA_BW", 2, 4, 4) ,
("x74", "ADD_MUL", 1, 4, 4) ,
("x75", "LEA_BW", 5, 4, 4) ,
("x76", "LEA_BW", 6, 4, 4) ,
("x77", "ADD_MUL", 9, 4, 4) ,
("x78", "LEA_BW", 13, 4, 4) ,
("x79", "LEA_BW", 14, 4, 4) ,
("x80", "ADD_MUL", 17, 4, 4) ,
("x81", "LEA_BW", 21, 4, 4) ,
("x82", "LEA_BW", 22, 4, 4) ,
("x83", "ADD_MUL", 25, 12, 4) ,
("x84", "ADD_MUL", 37, 4, 4) ,
("x85", "LEA_BW", 41, 4, 4) ,
("x86", "LEA_BW", 42, 4, 4) ,
("x87", "ADD_MUL", 45, 4, 4) ,
("x88", "LEA_BW", 49, 4, 4) ,
("x89", "LEA_BW", 50, 4, 4) ,
("x90", "ADD_MUL", 53, 4, 4) ,
RET_loc: 57"""
]

######################################################################
######################################################################
##                     Parsing minizinc output                      ##
######################################################################
######################################################################

def assemble_output_and_register_allocate(data_list, result_list):
    def parse_result(result):
        def parse_val(val):
            val = val.strip()
            if val[0] == '(' and val[-1] == ')':
                return tuple(map(parse_val, val[1:-1].split(',')))
            if val[0] in '"\'' and val[-1] in '"\'':
                return val[1:-1]
            if val.isdigit():
                return int(val)
            print('Unknown value: %s' % val)
            return val
        ret = {'schedule':list(map(str.strip, result.split(',\n')))}
        ret['RET_loc'] = [i[len('RET_loc: '):] for i in ret['schedule'] if i[:len('RET_loc: ')] == 'RET_loc: ']
        assert len(ret['RET_loc']) == 1
        ret['RET_loc'] = int(ret['RET_loc'][0])
        ret['schedule'] = tuple(parse_val(val) for val in ret['schedule'] if val[0] == '(' and val[-1] == ')')
        return ret
        
    def combine_lists(data_list, result_list):
        data = data_list[0]
        data['lines'] = list(data['lines'])
        for cur_data in data_list[1:]:
            data['lines'] += list(cur_data['lines'])
        data['lines'] = tuple(data['lines'])

        basepoint = 0
        results = []
        for result in map(parse_result, result_list):
            results += [(var, core_type, basepoint+loc, data_latency, core_latency)
                        for var, core_type, loc, data_latency, core_latency in result['schedule']]
            basepoint += result['RET_loc']
        return (data, results, basepoint)

    def sort_results(data, results):
        return sorted([(loc, line, var, core_type, data_latency, core_latency)
                       for (line, (var, core_type, loc, data_latency, core_latency))
                       in zip(data['lines'], results)])

    def get_live_ranges(data, results, RET_loc):
        var_names = get_var_names(data)
        input_var_names = get_input_var_names(data)
        output_var_names = get_output_var_names(data)
        ret = dict((var, {'start':0, 'accessed':[]}) for var in input_var_names)
        for (line, (var, core_type, loc, data_latency, core_latency)) in zip(data['lines'], results):
            assert var not in ret.keys()
            ret[var] = {'start':loc, 'accessed':[]}
            for arg in line['args']:
                if arg in var_names + input_var_names:
                    ret[arg]['accessed'].append(loc)
                else:
                    print(arg)
        for var in output_var_names:
            ret[var]['accessed'].append(RET_loc)
        for var in ret.keys():
            ret[var]['end'] = max(ret[var]['accessed'])
        return ret

    def remake_overlaps(live_ranges):
        live_ranges = dict(live_ranges)
        for var in live_ranges.keys():
            live_ranges[var] = dict(live_ranges[var])
            live_ranges[var]['overlaps'] = tuple(sorted(
                other_var
                for other_var in live_ranges.keys()
                if other_var != var and
                (live_ranges[other_var]['start'] <= live_ranges[var]['start'] <= live_ranges[other_var]['end']
                 or live_ranges[var]['start'] <= live_ranges[other_var]['start'] <= live_ranges[var]['end'])
                ))
        return live_ranges

##    def insert_possible_registers(live_ranges):
##        live_ranges = dict(live_ranges)
##        for var in live_ranges.keys():
##            live_ranges[var] = dict(live_ranges[var])
##            live_ranges[var]['possible registers'] = tuple(sorted(
##                other_var
##                for other_var in live_ranges.keys()
##                if other_var != var and
##                (live_ranges[other_var]['start'] <= live_ranges[var]['start'] <= live_ranges[other_var]['end']
##                 or live_ranges[var]['start'] <= live_ranges[other_var]['start'] <= live_ranges[var]['end'])
##                ))
##        return live_ranges

    def register_allocate(live_ranges):
        allocated = {}
        remaining_registers = list(REGISTERS)
        

    def format_results(sorted_results):
        return ['%s // %s, start: %.2f, end: %.2f' % (line['source'], core_type, loc / 4.0, (loc + data_latency) / 4.0)
                for loc, line, var, core_type, data_latency, core_latency in sorted_results]

    data, results, RET_loc = combine_lists(data_list, result_list)
##    live_ranges = remake_overlaps(get_live_ranges(data, results, RET_loc))
##    for i in sorted((len(rangev['overlaps']), var, rangev['accessed'], (rangev['start'], rangev['end']), rangev['overlaps']) for var, rangev in live_ranges.items()):
##        print(i)
    return '\n'.join(format_results(sort_results(data, results)))

data_list = parse_lines(get_lines('femulDisplay.log'))
for i, data in enumerate(data_list):
    with open('femulDisplay_%d.mzn' % i, 'w') as f:
        #f.write(make_assign_locations_to_instructions(data))
        #f.write(make_assign_instructions_to_locations(data))
        f.write(make_assign_locations_to_instructions_cumulatively(data))
            
print(assemble_output_and_register_allocate(data_list, RESULTS))
