#!/usr/bin/env python
from __future__ import with_statement
from memoize import memoize
import codecs, re, sys

LAMBDA = u'\u03bb'

OP_NAMES = {'*':'MUL', '+':'ADD', '>>':'SHL', '<<':'SHR', '|':'OR', '&':'AND'}

MAX_INSTRUCTION_WINDOW = 1000

INSTRUCTIONS_PER_CYCLE = 4

REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP', 'RSP']
                  + ['r%d' % i for i in range(8, 16)])

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

if len(sys.argv) > 1:
    MAX_INSTRUCTION_WINDOW = int(sys.argv[1])

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

def schedule(data, basepoint):
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

    def get_possible_next_statements(remaining_vars, dependencies):
        return [var for var in remaining_vars
                if all(arg not in remaining_vars for arg in dependencies[var])]

    def make_initial_core_state():
        return {'cores':dict((name, [0] * count) for name, count in CORE_DATA),
                'registers':dict((name, None) for name in REGISTERS)}

#    def freeze_core_state(core_state):
#        return (tuple(tuple(core_state['cores'][name]) for name in CORES),
#                tuple(core_state['registers'][name] for name in REGISTERS))
#    def unfreeze_core_state(core_state):
#        return {'cores':dict((name, list(cycles_until_free)) for name, cycles_until_free in zip(CORES, core_state[0])),
#                'registers':dict((name, var) for name, var in zip(REGISTERS, core_state[1]))}

    def get_initial_indices(input_data):
        #if basepoint == 0:
        #    return tuple(list(get_input_var_names(input_data)) + list(get_var_names(input_data)))
        #else:
        return tuple(get_var_names(input_data))



#    def make_source(input_data, var):
#        input_var_names = get_input_var_names(input_data)
#        if var in input_var_names: return 'LOAD %s' % var

#    def freeze_core_state(vars_ready_at, core_remaining_cycle_count,



    dependencies = make_data_dependencies(data)
    reverse_dependencies = make_reverse_data_dependencies(dependencies)

    def make_initial_core_state():
        vars_remaining_cycles = {}
        core_remaining_cycle_count = dict([(core_name, [0] * core_count) for core_name, core_count in CORE_DATA]
                                          + [(core_name, [0]) for core_name in REGISTERS])
        cur_instructions_in_cycle = 0
        return vars_remaining_cycles, core_remaining_cycle_count, cur_instructions_in_cycle

    def freeze_gen(v, rec=(lambda x:x)):
        if isinstance(v, list):
            return ('list', tuple(map(rec, v)))
        if isinstance(v, tuple):
            return ('tuple', tuple(map(rec, v)))
        elif isinstance(v, dict):
            return ('dict', tuple(sorted((k, rec(val)) for k, val in v.items())))
        else:
            return v
    def unfreeze_gen(v, rec=(lambda x:x)):
        if isinstance(v, tuple):
            ty, v = v
            if ty == 'list':
                return list(map(rec, v))
            elif ty == 'tuple':
                return tuple(map(rec, v))
            elif ty == 'dict':
                return dict((k, rec(val)) for k, val in v)
            else:
                print('Freeze error: %s' % repr((ty, v)))
                assert False
        else:
            return v
    def freeze(v):
        return freeze_gen(v, freeze)
    def unfreeze(v):
        return unfreeze_gen(v, unfreeze)

    @memoize
    def update_core_state(var, core, core_state):
        core = unfreeze(core)
        (vars_remaining_cycles, core_remaining_cycle_count, cur_instructions_in_cycle) = unfreeze(core_state)
        cost = 0
        if cur_instructions_in_cycle >= INSTRUCTIONS_PER_CYCLE:
            cost += 1
            cur_instructions_in_cycle = 0
            for c in core_remaining_cycle_count.keys():
                for i in range(len(core_remaining_cycle_count[c])):
                    core_remaining_cycle_count[c][i] = max(0, core_remaining_cycle_count[c][i] - 1)
            vars_remaining_cycles = dict((var, c - 1) for var, c in vars_remaining_cycles.items()
                                         if c > 1)
        cycles_passed = max([min(core_remaining_cycle_count[core['core']['name']])] +
                            [vars_remaining_cycles[v] for v in dependencies[var] if v in vars_remaining_cycles.keys()])
        if cycles_passed != 0:
            cost += cycles_passed
            cur_instructions_in_cycle = 1
            for c in core_remaining_cycle_count.keys():
                for i in range(len(core_remaining_cycle_count[c])):
                    core_remaining_cycle_count[c][i] = max(0, core_remaining_cycle_count[c][i] - cycles_passed)
            vars_remaining_cycles = dict((var, c - cycles_passed) for var, c in vars_remaining_cycles.items()
                                         if c > cycles_passed)
        else:
            cur_instructions_in_cycle += 1
        vars_remaining_cycles[var] = core['latency']
        assert core_remaining_cycle_count[core['core']['name']][0] == 0
        core_remaining_cycle_count[core['core']['name']][0] = core['core']['latency']
        core_remaining_cycle_count[core['core']['name']] = sorted(core_remaining_cycle_count[core['core']['name']])
        return (cost, freeze((vars_remaining_cycles, core_remaining_cycle_count, cur_instructions_in_cycle)))

    @memoize
    def evaluate_cost_memo(arg):
        schedule, core_state = unfreeze_gen(arg)
        schedule = unfreeze(schedule)
        (vars_remaining_cycles, core_remaining_cycle_count, cur_instructions_in_cycle) = unfreeze(core_state)
        if len(schedule) == 0: return max([0] + list(vars_remaining_cycles.values()))
        (var, core), schedule = schedule[0], schedule[1:]
        cost, core_state = update_core_state(var, freeze(core), core_state)
        return cost + evaluate_cost_memo(freeze_gen((freeze(schedule), core_state)))


    def add_cycle_info(schedule):
        vars_remaining_cycles = {}
        core_remaining_cycle_count = dict([(core_name, [0] * core_count) for core_name, core_count in CORE_DATA]
                                          + [(core_name, [0]) for core_name in REGISTERS])
        schedule_with_cycle_info = []
        cur_cycle = 0
        cur_instructions_in_cycle = 0
        for var, core in schedule:
            if cur_instructions_in_cycle >= INSTRUCTIONS_PER_CYCLE:
                cur_cycle += 1
                cur_instructions_in_cycle = 0
                for c in core_remaining_cycle_count.keys():
                    for i in range(len(core_remaining_cycle_count[c])):
                        core_remaining_cycle_count[c][i] = max(0, core_remaining_cycle_count[c][i] - 1)
                vars_remaining_cycles = dict((var, c - 1) for var, c in vars_remaining_cycles.items()
                                             if c > 1)
            cycles_passed = max([min(core_remaining_cycle_count[core['core']['name']])] +
                                [vars_remaining_cycles[v] for v in dependencies[var] if v in vars_remaining_cycles.keys()])
            if cycles_passed != 0:
                cur_cycle += cycles_passed
                cur_instructions_in_cycle = 1
                for c in core_remaining_cycle_count.keys():
                    for i in range(len(core_remaining_cycle_count[c])):
                        core_remaining_cycle_count[c][i] = max(0, core_remaining_cycle_count[c][i] - cycles_passed)
                vars_remaining_cycles = dict((var, c - cycles_passed) for var, c in vars_remaining_cycles.items()
                                             if c > cycles_passed)
            else:
                cur_instructions_in_cycle += 1
            vars_remaining_cycles[var] = core['latency']
            assert core_remaining_cycle_count[core['core']['name']][0] == 0
            core_remaining_cycle_count[core['core']['name']][0] = core['core']['latency']
            core_remaining_cycle_count[core['core']['name']] = sorted(core_remaining_cycle_count[core['core']['name']])
            schedule_with_cycle_info.append((var,
                                             {'start':cur_cycle, 'finish':cur_cycle + core['core']['latency']},
                                             core))
        return schedule_with_cycle_info

    def evaluate_cost(schedule_with_cycle_info):
        return max(cycles['finish'] for var, cycles, core in reversed(schedule_with_cycle_info))


    var_names = get_var_names(data)
    lines = dict((line['out'], line) for line in data['lines'])

    @memoize
    def schedule_remaining(remaining_indices, core_state):
        def make_schedule(var, core):
            cost, new_core_state = update_core_state(var, freeze(core), core_state)
            extra_cost, schedule = schedule_remaining(tuple(i for i in remaining_indices if i != var), new_core_state)
            return cost + extra_cost, ([(var, core)] + schedule)
        next_statements = get_possible_next_statements(remaining_indices, dependencies)
        min_cost, min_schedule = None, None
        for var in next_statements:
            if var in lines.keys():
                for core in MODEL[lines[var]['op']]:
                    cost, schedule = make_schedule(var, core)
                    if min_cost is None or cost < min_cost:
                        min_cost, min_schedule = cost, schedule
#                    return min_cost, min_schedule
            else:
                for core in MODEL['LOAD']:
                    cost, schedule = make_schedule(var, core)
                    if min_cost is None or cost < min_cost:
                        min_cost, min_schedule = cost, schedule
#                    return min_cost, min_schedule
        if min_cost is None:
            min_cost, min_schedule = evaluate_cost_memo(freeze_gen((freeze([]), core_state))), []
        return min_cost, min_schedule

    core_state = freeze(make_initial_core_state())
    cost, schedule = schedule_remaining(get_initial_indices(data), core_state) #, freeze_core_state(make_initial_core_state()))
    schedule_with_cycle_info = add_cycle_info(schedule)
    for var, cycles, core in schedule_with_cycle_info:
        if var in lines.keys():
            print('%s; // %s, start: %s, end: %s' % (lines[var]['source'], core['core']['name'], basepoint + cycles['start'], basepoint + cycles['finish']))
        else:
            print('LOAD %s; // %s, start: %s, end: %s' % (var, core['core']['name'], basepoint + cycles['start'], basepoint + cycles['finish']))
    return basepoint + cost

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



    def make_output(input_data):
        ret = 'solve minimize RET_loc;\n\n'
        ret += 'output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(CORE_NAMES[fix(output_cores[i])]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(output_data_latency[i]) ++ ", " ++ show(output_core_latency[i]) ++ ") ,\\n"\n'
        ret += '       | i in INSTRUCTIONS ];\n'
        ret += 'output [ "RET_loc: " ++ show(RET_loc) ];\n'
        return ret

#    return '\n'.join([
#        make_decls(data),
#        make_disjoint(data),
#        make_dependencies(data),
#        make_cores(data),
#        make_output(data)
#        ])

data_list = parse_lines(get_lines('femulDisplay.log'))
basepoint = 0
for i, data in enumerate(data_list):
    basepoint = schedule(data, basepoint)
    print(basepoint)
    sys.exit(0)

print(basepoint)
