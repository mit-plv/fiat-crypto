#!/usr/bin/env python
from __future__ import with_statement
import codecs, re

LAMBDA = u'\u03bb'

MAX_INSTRUCTION_WINDOW = 30

INSTRUCTIONS_PER_CYCLE = 4

REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP', 'RSP']
                  + ['r%d' % i for i in range(8, 16)])

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

def get_all_var_names(input_data):
    return tuple(list(get_input_var_names(input_data)) + list(get_var_names(input_data)))

def get_output_var_names(input_data):
    return tuple(i for i in data['return'].replace(',', ' ').replace('(', ' ').replace(')', ' ').split(' ')
                 if i != '')


def line_of_var(input_data, var):
    retv = [line for line in input_data['lines'] if line['out'] == var]
    if len(retv) > 0: return retv[0]
    return {'out': var, 'args':tuple(), 'op': 'INPUT', 'type':'uint64_t'}

def reg_count(size):
    return {'uint64_t':1, 'uint128_t': 2}[size]

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
##                Assign locations to instructions cumulatively     ##
######################################################################
######################################################################


def make_assign_locations_to_instructions_cumulatively(data):
    def make_decls(input_data):
        var_names = get_all_var_names(input_data)
        ret = ''
        ret += 'include "alldifferent.mzn";\n'
        ret += 'include "cumulative.mzn";\n'
        for line in input_data['lines']:
            ret += '%%%s\n' % line['source']
        ret += create_set('INSTRUCTIONS', list(var_names))
        MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION = 3
        APPROXIMATE_MAX_LATENCY = 6 * INSTRUCTIONS_PER_CYCLE
        max_loc = len(var_names) * MAX_NUMBER_OF_NOOPS_PER_INSTRUCTION + APPROXIMATE_MAX_LATENCY
        ret += 'int: MAX_LOC = %d;\n\n' % max_loc
        ret += 'set of int: LOCATIONS = 1..MAX_LOC;\n'
        ret += 'array[INSTRUCTIONS] of var LOCATIONS: output_locations;\n'
        ret += 'array[INSTRUCTIONS] of var LOCATIONS: live_duration;\n'
        ret += 'array[INSTRUCTIONS] of int: output_register_count = [%s];\n' % ', '.join(str(reg_count(line_of_var(input_data, var)['type'])) for var in var_names)
        ret += 'var LOCATIONS: RET_loc;\n' 
        ret += 'constraint cumulative(output_locations, live_duration, output_register_count, %d);\n' % len(REGISTERS)
        ret += '\n'
        return ret

    def make_disjoint(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        ret += 'constraint alldifferent(output_locations);\n'
        return ret

    def make_dependencies_use(input_data):
        ret = ''
        reverse_dependencies = {}
        for line in input_data['lines']:
            for arg in line['args']:
                if arg[:2] == '0x': continue
                if arg not in reverse_dependencies.keys(): reverse_dependencies[arg] = []
                reverse_dependencies[arg].append(line['out'])
        for var in reverse_dependencies.keys():
            ret += ('constraint output_locations[%s] + live_duration[%s] == max([%s]);\n'
                    % (var, var, ', '.join('output_locations[%s]' % dep for dep in reverse_dependencies[var])))
        ret += '\n'
        return ret

    def make_dependencies(input_data):
        var_names = get_var_names(input_data)
        ret = ''
        for line in input_data['lines']:
            for arg in line['args']:
                if arg[0] not in '0123456789':
                    ret += ('constraint output_locations[%s] + 1 <= output_locations[%s];\n'
                            % (arg, line['out']))
        ret += '\n'
        ret += 'constraint max([ output_locations[i] + 1 | i in INSTRUCTIONS ]) <= RET_loc;\n'
        ret += '\n'
        return ret

    def make_output(input_data):
        ret = 'solve minimize RET_loc;\n\n'
        ret += 'output [ "(" ++ show(INSTRUCTIONS_NAMES[i]) ++ ", " ++ show(output_locations[i]) ++ ", " ++ show(live_duration[i]) ++ ") ,\\n"\n'
        ret += '       | i in INSTRUCTIONS ];\n'
        ret += 'output [ "RET_loc: " ++ show(RET_loc) ];\n'
        return ret

    return '\n'.join([
        make_decls(data),
        make_disjoint(data),
        make_dependencies_use(data),
        make_dependencies(data),
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
    with open('femulDisplayReg_%d.mzn' % i, 'w') as f:
        #f.write(make_assign_locations_to_instructions(data))
        #f.write(make_assign_instructions_to_locations(data))
        f.write(make_assign_locations_to_instructions_cumulatively(data))
            
#print(assemble_output_and_register_allocate(data_list, RESULTS))
