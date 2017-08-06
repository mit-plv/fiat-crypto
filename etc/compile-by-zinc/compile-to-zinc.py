#!/usr/bin/env python
from __future__ import with_statement
import codecs, re

LAMBDA = u'\u03bb'

CORES = ('ADD_MUL0', 'ADD_MUL1', 'MUL0', 'LEA_BW0', 'LEA_BW1', 'NOOP_CORE')

OP_NAMES = {'*':'MUL', '+':'ADD', '>>':'SHL', '<<':'SHR', '|':'OR', '&':'AND'}

MAX_INSTRUCTION_WINDOW = 40

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
    print('Compiling %d of %d lines...' % (min(MAX_INSTRUCTION_WINDOW, len(ret['lines'])), len(ret['lines'])))
    ret['lines'] = ret['lines'][:MAX_INSTRUCTION_WINDOW]
    return ret

def get_var_names(input_data):
    return tuple(line['out'] for line in input_data['lines'])

def get_input_var_names(input_data):
    return tuple(i for i in data['vars'].replace('%core', '').replace(',', ' ').replace('(', ' ').replace(')', ' ').replace("'", ' ').split(' ')
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

######################################################################
######################################################################
##                Assign locations to instructions                  ##
######################################################################
######################################################################
def make_assign_locations_to_instructions(data):
    def make_decls(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        ret += create_set('CORE', CORES)
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

    return '\n'.join([
        make_decls(data),
        make_disjoint(data),
        make_dependencies(data),
        make_cores(data),
        make_cores_disjoint(data),
        make_output(data)
        ])


######################################################################
######################################################################
##                Assign instructions to locations                  ##
######################################################################
######################################################################

def make_assign_instructions_to_locations(data):
    def make_decls(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        ret += 'include "alldifferent.mzn";\n'
        ret += create_set('CORE', CORES)
        ret += create_set('INSTRUCTION', ['NOOP'] + list(var_names))
        MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION = 3
        APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
        max_loc = len(var_names) * MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION # + APPROXIMATE_MAX_LATENCY
        ret += 'int: MAX_LOC = %d;\n\n' % max_loc
        ret += 'array[1..MAX_LOC] of var INSTRUCTION: output_instructions;\n'
        ret += 'array[1..MAX_LOC] of var CORE: output_cores;\n'
        ret += 'array[1..MAX_LOC] of var int: output_core_latency;\n'
        ret += 'array[1..MAX_LOC] of var int: output_data_latency;\n'
        ret += 'var int: RET_loc;\n'
        ret += '\n'
        ret += 'constraint 1 <= RET_loc /\\ RET_loc <= MAX_LOC;\n'
        ret += '\n'
        return ret

    def make_disjoint(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        #ret += 'constraint alldifferent( [ output_instructions[i] | i in 1..MAX_LOC where output_instructions[i] != NOOP ] );\n'
        ret += 'constraint forall (i,j in 1..MAX_LOC where i < j) (output_instructions[i] == NOOP \\/ output_instructions[i] != output_instructions[j]);\n'
        ret += 'constraint sum( [ 1 | i in 1..MAX_LOC where output_instructions[i] != NOOP ] ) == length(INSTRUCTION) - 1;\n'
        ret += 'constraint forall (i in 1..MAX_LOC where RET_loc <= i) (output_instructions[i] == NOOP);\n'
        ret += 'constraint forall (i,j in 1..MAX_LOC where i < j) ((output_instructions[i] != NOOP /\\ output_instructions[j] != NOOP /\\ output_cores[i] == output_cores[j]) -> i + output_core_latency[i] <= j);\n'
        ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == NOOP \\/ i + output_data_latency[i] <= RET_loc);\n'
        ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == NOOP -> (output_core_latency[i] == 0 /\\ output_data_latency[i] == 0 /\\ output_cores[i] == NOOP_CORE));\n'
        return ret

    def make_dependencies(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        for line in input_data['lines']:
            for arg in line['args']:
                if arg in var_names and arg[0] not in '0123456789':
                    ret += ('constraint forall (i,j in 1..MAX_LOC) ((output_instructions[i] == %s /\\ output_instructions[j] == %s) -> i + output_data_latency[i] <= j);\n'
                            % (arg, line['out']))
        ret += '\n'
        return ret

    def make_cores(input_data):
        ret = ''
        for line in input_data['lines']:
            ret += 'constraint forall (i in 1..MAX_LOC) (output_instructions[i] == %s -> (' % line['out']
            possible_cores = []
            cores = MODEL[line['op']]
            for core in cores:
                possible_cores.append(r'(output_core_latency[i] == %d /\ output_data_latency[i] == %d /\ output_cores[i] == %s)'
                                      % (core['core']['latency'] * INSTRUCTIONS_PER_CYCLE,
                                         core['latency'] * INSTRUCTIONS_PER_CYCLE,
                                         core['core']['name']))
            ret += ' \/ '.join(possible_cores)
            ret += '));\n'
        ret += '\n'
        return ret

    def make_output(input_data):
        ret = 'solve minimize RET_loc;\n\n'
        ret += 'output [ "(" ++ show(INSTRUCTION_NAMES[fix(output_instructions[i])]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_core_latency[i]) ++ ", " ++ show(output_data_latency[i]) ++ ") ,\\n"\n'
        ret += '       | i in 1..MAX_LOC ];\n'
        return ret

    return '\n'.join([
        make_decls(data),
        make_disjoint(data),
        make_dependencies(data),
        make_cores(data),
        make_output(data)
        ])

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
        ret += 'array[INSTRUCTIONS] of var CORE: output_cores;\n'
        ret += 'array[INSTRUCTIONS] of OPS: input_ops = [%s];\n' % ', '.join(OP_NAMES[line['op']] for line in input_data['lines'])
        for core in CORES:
            ret += 'array[INSTRUCTIONS] of var int: output_%s_core_latency;\n' % core
            ret += 'array[INSTRUCTIONS] of var 0..1: output_%s_core_use;\n' % core
            ret += 'constraint forall (i in INSTRUCTIONS) (0 <= output_%s_core_latency[i]);\n' % core
        ret += 'var LOCATIONS: RET_loc;\n'
        ret += '\n'
        return ret

    def make_cores(input_data):
        ret = ''
        for opc, cores in MODEL.items():
            possible_cores_and = []
            possible_cores_or = []
            for core in cores:
                possible_cores_and.append((r'((output_cores[i] == %s /\ output_%s_core_use[i] == 1 /\ output_%s_core_latency[i] == %d /\ output_data_latency[i] == %d)' +
                                           r' \/ (output_cores[i] != %s /\ output_%s_core_use[i] == 0 /\ output_%s_core_latency[i] == 0))')
                                          % (core['core']['name'],
                                             core['core']['name'],
                                             core['core']['name'],
                                             core['core']['latency'] * INSTRUCTIONS_PER_CYCLE,
                                             core['latency'] * INSTRUCTIONS_PER_CYCLE,
                                             core['core']['name'],
                                             core['core']['name'],
                                             core['core']['name']))
            for core in cores:
                possible_cores_or.append('output_cores[i] == %s' % core['core']['name'])
            ret += ('constraint forall (i in INSTRUCTIONS) (input_ops[i] == %s -> ((%s) /\\ (%s)));\n'
                    % (OP_NAMES[opc], r' /\ '.join(possible_cores_and), r' \/ '.join(possible_cores_or)))
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

    def make_output(input_data):
        ret = 'solve minimize RET_loc;\n\n'
        ret += 'output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(output_data_latency[i]) ++ ") ,\\n"\n'
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



data = parse_lines(get_lines('femulDisplay.txt'))
with open('femulDisplay.mzn', 'w') as f:
    #f.write(make_assign_locations_to_instructions(data))
    #f.write(make_assign_instructions_to_locations(data))
    f.write(make_assign_locations_to_instructions_cumulatively(data))
