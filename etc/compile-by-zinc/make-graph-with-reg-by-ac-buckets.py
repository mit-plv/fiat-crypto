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

def make_data_dependencies(input_data):
    input_var_names = get_input_var_names(input_data)
    dependencies = dict((var, tuple()) for var in input_var_names)
    for line in input_data['lines']:
        dependencies[line['out']] = tuple(arg for arg in line['args']
                                          if arg[0] not in '0123456789')
    return dependencies
def make_reverse_data_dependencies(dependencies):
    reverse_dependencies = dict((k, []) for k in dependencies.keys())
    for k, v in dependencies.items():
        for arg in v:
            reverse_dependencies[arg].append(k)
    return reverse_dependencies

def get_low_or_high(obj, low_or_high):
    assert(low_or_high in ('low', 'high'))
    if obj['op'] == 'COMBINE':
        if low_or_high == 'low': return obj['deps'][0]
        if low_or_high == 'high': return obj['deps'][1]
    else:
        return {'out':obj['out'] + '_' + low_or_high, 'style':'', 'deps':(obj,), 'op':'GET_' + low_or_high.upper(), 'type':'uint64_t', 'extra_out':tuple(o + '_' + low_or_high for o in obj['extra_out']), 'rev_deps':tuple()}

def add_combine_low_high(objs):
    for obj in objs:
        if obj['type'] == 'uint128_t':
            obj_low = get_low_or_high(obj, 'low')
            obj_high = get_low_or_high(obj, 'high')
            obj_new = {'out':obj['out'], 'style':'', 'deps':(obj_low, obj_high), 'op':'COMBINE', 'type':'uint128_t', 'extra_out':obj['extra_out'], 'rev_deps':obj['rev_deps']}
            obj['out'] += '_tmp'
            obj['rev_deps'] = (obj_low, obj_high)
            obj_high['rev_deps'] = (obj_new,)
            obj_low['rev_deps'] = (obj_new,)
            for rdep in obj_new['rev_deps']:
                rdep['deps'] = tuple(d if d is not obj else obj_new
                                     for d in rdep['deps'])


def split_graph(objs):
    for obj in objs:
        if obj['op'] == '&' and obj['type'] == 'uint64_t' and len(obj['deps']) == 1 and obj['deps'][0]['type'] == 'uint128_t' and obj['deps'][0]['op'] == 'COMBINE':
            combine_node = obj['deps'][0]
            low = combine_node['deps'][0]
            obj['deps'] = (low,)
            low['rev_deps'] = tuple(list(low['rev_deps']) + [obj])
        if obj['op'] == '+' and obj['type'] == 'uint128_t' and len(obj['rev_deps']) == 2 and obj['rev_deps'][0]['op'] == 'GET_LOW' and obj['rev_deps'][1]['op'] == 'GET_HIGH':
            for tmp in ('_tmp', '_temp'):
                if obj['out'][-len(tmp):] == tmp:
                    obj['out'] = obj['out'][:-len(tmp)]
            obj_low, obj_high = obj['rev_deps']
            obj_carry = {'out':'c' + obj['out'], 'style':'', 'deps':(obj_low,), 'op':'GET_CARRY', 'type':'CARRY', 'extra_out':tuple(), 'rev_deps':(obj_high,)}
            assert(len(obj_low['deps']) == 1)
            assert(len(obj_high['deps']) == 1)
            assert(obj_low['type'] == 'uint64_t')
            assert(obj_high['type'] == 'uint64_t')
            obj_low['deps'], obj_high['deps'] = [], [obj_carry]
            obj_low['op'] = '+'
            obj_high['op'] = '+'
            for dep in obj['deps']:
                if dep['type'] == 'uint64_t':
                    obj_low['deps'].append(dep)
                    dep['rev_deps'] = tuple(d if d is not obj else obj_low
                                            for d in dep['rev_deps'])
                elif dep['type'] == 'uint128_t':
                    dep_low, dep_high = get_low_or_high(dep, 'low'), get_low_or_high(dep, 'high')
                    obj_low['deps'].append(dep_low)
                    obj_high['deps'].append(dep_high)
                    dep_low['rev_deps'] = tuple(list(dep_low['rev_deps']) + [obj_low])
                    dep_high['rev_deps'] = tuple(list(dep_high['rev_deps']) + [obj_high])
                else:
                    assert(False)
            obj_low['deps'], obj_high['deps'] = tuple(obj_low['deps']), tuple(obj_high['deps'])
            obj['deps'] = tuple()
            obj['rev_deps'] = tuple()

def collect_ac_buckets(graph):
    to_process = list(graph['out'].values())
    while len(to_process) > 0:
        line, to_process = to_process[0], to_process[1:]
        if line['op'] == '+':
            args = list(line['deps'])
            new_args = []
            while len(args) > 0:
                arg, args = args[0], args[1:]
                if arg['op'] == '+' and len(arg['rev_deps']) == 1 and line['type'] == 'uint128_t':
                    line['extra_out'] = tuple(sorted(list(line['extra_out']) + [arg['out']] + list(arg['extra_out'])))
                    for arg_arg in arg['deps']:
                        arg_arg['rev_deps'] = (line,)
                        args.append(arg_arg)
                else:
                    new_args.append(arg)
            line['deps'] = tuple(new_args)
        to_process += list(line['deps'])

def prune(out_vars, objs, seen=None):
    if seen is None: seen = set()
    for obj in objs:
        if obj['out'] in seen: continue
        prune(out_vars, obj['rev_deps'], seen=seen)
        if any(len(rdep['deps']) == 0
               or (len(rdep['rev_deps']) == 0 and rdep['out'] not in out_vars)
               for rdep in obj['rev_deps']):
            #print('pruning %s' % obj['out'])
            obj['rev_deps'] = tuple(rdep for rdep in obj['rev_deps']
                                    if len(rdep['deps']) > 0
                                    and (rdep['out'] in out_vars or len(rdep['rev_deps']) > 0))
        seen.add(obj['out'])

def to_graph(input_data):
    objs = dict((var, {'out':var, 'style':''}) for var in list(get_input_var_names(input_data)) + list(get_var_names(input_data)))
    for var in get_input_var_names(input_data):
        objs[var]['deps'] = tuple()
        objs[var]['op'] = 'INPUT'
        objs[var]['type'] = 'uint64_t'
        objs[var]['extra_out'] = tuple()
    for line in input_data['lines']:
        var = line['out']
        objs[var]['extra_out'] = tuple()
        objs[var]['op'] = line['op']
        objs[var]['type'] = line['type']
        objs[var]['deps'] = tuple(objs[arg] for arg in line['args'] if arg in objs.keys())
    for var in objs.keys():
        objs[var]['rev_deps'] = tuple(objs[arg] for arg in sorted(objs.keys())
                                      if any(node['out'] == var for node in objs[arg]['deps']))
    graph = {'out':dict((var, objs[var]) for var in get_output_var_names(input_data)),
             'in':dict((var, objs[var]) for var in get_input_var_names(input_data)) }
    collect_ac_buckets(graph)
    add_combine_low_high(objs.values())
    split_graph(objs.values())
    prune(set(graph['out'].keys()), objs.values())
    #split_graph(objs)
    return graph


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

def fill_node(node, color='red'):
    node['style'] = ', style="filled", fillcolor="%s"' % color

def fill_deps(node, color='red'):
    fill_node(node)
    for dep in node['deps']:
        fill_deps(dep, color=color)

def fill_subgraph(in_node, color='red'):
    #print((in_node['out'], in_node['op'], [d['out'] for d in in_node['rev_deps']]))
    fill_node(in_node, color=color)
    if in_node['op'] != '+':
        fill_deps(in_node, color=color)
        for rdep in in_node['rev_deps']:
            fill_subgraph(rdep, color=color)

def is_temp(node):
    for tmp in ('_tmp', '_temp'):
        if node['out'][-len(tmp):] == tmp:
            return True
    return False

# returns {cur_map with new_name->reg}, still_free_temps, still_free_list, all_temps
def allocate_node(existing, node, *args):
    cur_map, free_temps, free_list, all_temps, freed, new_buckets = args
    free_temps = list(free_temps)
    free_list = list(free_list)
    all_temps = list(all_temps)
    full_map = dict(existing)
    cur_map = dict(cur_map)
    freed = list(freed)
    new_buckets = list(new_buckets)
    full_map.update(cur_map)
    def do_ret():
        return cur_map, tuple(free_temps), tuple(free_list), tuple(all_temps), tuple(freed), tuple(new_buckets)
    def do_free(var):
        for reg in full_map[var].split(':'):
            if reg in all_temps:
                if reg not in free_temps:
                    free_temps.append(reg)
            else:
                if reg not in free_list:
                    free_list.append(reg)
    def do_free_deps(node):
        for dep in node['deps']:
            if dep['out'] in full_map.keys() and all(n['out'] in full_map.keys() or n['out'] in cur_map.keys() for n in dep['rev_deps']):
                if dep['out'] not in freed:
                    do_free(dep['out'])
                    freed.append(dep['out'])
    if node['out'] in full_map.keys():
        do_free_deps(node)
        return do_ret()
    #print('alloc: %s (of %d)' % (node['out'], len(free_list)))
    if node['op'] in ('GET_HIGH', 'GET_LOW') and len(node['deps']) == 1 and len(node['deps'][0]['rev_deps']) <= 2 and all(n['op'] in ('GET_HIGH', 'GET_LOW') for n in node['deps'][0]['rev_deps']) and node['deps'][0]['out'] in full_map.keys():
        reg_idx = {'GET_LOW':0, 'GET_HIGH':1}[node['op']]
        cur_map[node['out']] = full_map[node['deps'][0]['out']].split(':')[reg_idx]
        return do_ret()
    if len(node['deps']) == 1 and len(node['deps'][0]['rev_deps']) == 1 and node['deps'][0]['out'] in full_map.keys() and node['type'] == node['deps'][0]['type']:
        cur_map[node['out']] = full_map[node['deps'][0]['out']]
        return do_ret()
    if len(node['deps']) == 0 and node['op'] == 'INPUT':
        assert(node['type'] == 'uint64_t')
        cur_map[node['out']] = free_list.pop()
        return do_ret()
    if is_temp(node):
        num_reg = {'uint64_t':1, 'uint128_t':2}[node['type']]
        # TODO: make this more efficient by allowing re-use of
        # dependnecies which are no longer needed (which are currently
        # only reaped after this node is assigned)
        while len(free_temps) < num_reg:
            reg = free_list.pop()
            free_temps.append(reg)
            all_temps.append(reg)
        cur_map[node['out']] = ':'.join(free_temps[:num_reg])
        free_temps = free_temps[num_reg:]
        do_free_deps(node)
        return do_ret()
    if node['op'] == '+' and node['type'] == 'uint64_t' and len(node['extra_out']) > 0:
        cur_map[node['out']] = free_list.pop()
        new_buckets.append(node)
        do_free_deps(node)
        return do_ret()
    if node['op'] == '*' and node['type'] == 'uint64_t' and len(node['deps']) == 1:
        dep = node['deps'][0]
        assert(dep['out'] in full_map.keys())
        if all(rdep is node or (rdep['out'] in full_map.keys() and full_map[rdep['out']] != full_map[dep['out']])
               for rdep in dep['rev_deps']):
            cur_map[node['out']] = full_map[dep['out']]
        else:
            cur_map[node['out']] = free_list.pop()
        return do_ret()
    raw_input([node['out'], node['op'], node['type'], len(node['deps'])])
    return do_ret()

def allocate_deps(existing, node, *args):
    for dep in node['deps']:
        args = allocate_deps(existing, dep, *args)
    return allocate_node(existing, node, *args)

def allocate_subgraph(existing, node, *args):
    if node['op'] != '+':
        args = allocate_deps(existing, node, *args)
    else:
        args = allocate_node(existing, node, *args)
    if node['op'] != '+':
        for rdep in node['rev_deps']:
            args = allocate_subgraph(existing, rdep, *args)
    return args

def annotate_with_alloc(objs, mapping):
    for obj in objs:
        if obj['out'] in mapping.keys():
            obj['reg'] = ' (' + mapping[obj['out']] + ')'
        else:
            obj['reg'] = ''

def get_plus_deps(nodes, ops=('+',), types=('uint128_t',), seen=None):
    if seen is None: seen = set()
    for node in nodes:
        for dep in node['deps']:
            if dep['out'] in seen: continue
            seen.add(dep['out'])
            if dep['op'] in ops and dep['type'] in types:
                yield dep
            for dep in get_plus_deps([dep], ops=ops, types=types, seen=seen):
                yield dep

def get_objects(start, ret=None):
    if ret is None: ret = {}
    for node in start:
        if node['out'] in ret.keys(): continue
        ret[node['out']] = node
        get_objects(node['deps'], ret=ret)
    return ret

def print_nodes(objs):
    for var in sorted(objs.keys(), key=(lambda s:(int(s.strip('cx_lowhightmp')), s))):
        yield '    %s [label="%s%s" %s];\n' % (objs[var]['out'], ' + '.join(sorted([objs[var]['out']] + list(objs[var]['extra_out']))), objs[var]['reg'], objs[var]['style'])
def print_deps(objs):
    for var in sorted(objs.keys()):
        for dep in objs[var]['deps']:
            yield '    %s -> %s [ label="%s" ] ;\n' % (dep['out'], objs[var]['out'], objs[var]['op'])

def allocate_one_subtree(possible_nodes, existing, *args):
    cur_map, free_temps, free_list, all_temps, freed, new_buckets = args
    existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets \
        = dict(existing), dict(cur_map), list(free_temps), list(free_list), list(all_temps), tuple(freed), tuple(new_buckets)
    args = (cur_map, free_temps, free_list, all_temps, freed, new_buckets)
    sorted_nodes = []
    for node in possible_nodes:
        try:
            lens = [len([rd for rd in d['rev_deps'] if rd['out'] not in existing.keys()]) for d in node['deps']]
            temp_cur_map, temp_free_temps, temp_free_list, temp_all_temps, temp_freed, temp_new_buckets = allocate_subgraph(existing, node, *args)
            if set(temp_free_temps) != set(temp_all_temps):
                print(('BAD', node['out'], temp_cur_map, temp_free_temps, temp_free_list, temp_all_temps))
            sorted_nodes.append(((len(temp_free_list),
                                  -min(lens),
                                  -max(lens),
                                  -len(temp_new_buckets),
                                  len(temp_free_temps),
                                  -int(node['out'].strip('x_lowhightemp'))),
                                 node))
        except IndexError:
            print('Too many reg: %s' % node['out'])
    sorted_nodes = tuple(reversed(sorted(sorted_nodes, key=(lambda v: v[0]))))
    print([(n[0], n[1]['out']) for n in sorted_nodes])
    node = sorted_nodes[0][1]
    possible_nodes = [n for n in possible_nodes if n is not node]
    print('Allocating for %s' % node['out'])
    args = allocate_subgraph(existing, node, *args)
    fill_subgraph(node)
    cur_map, free_temps, free_list, all_temps, freed, new_buckets = args
    return possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets


def print_graph(graph, allocs):
    objs = get_objects(graph['out'].values())
    annotate_with_alloc(objs.values(), allocs)
    body = ''.join(print_nodes(objs))
    body += ''.join(print_deps(objs))
    body += ''.join('    in -> %s ;\n' % node['out'] for node in graph['in'].values())
    body += ''.join('    %s -> out ;\n' % node['out'] for node in graph['out'].values())
    return ('digraph G {\n' + body + '}\n')

data_list = parse_lines(get_lines('femulDisplay.log'))
for i, data in enumerate(data_list):
    graph = to_graph(data)
    #buckets = tuple(sorted(get_plus_deps(graph['out'].values()),
    #                       key=(lambda n:len(list(get_plus_deps([n]))))))
    possible_nodes = dict((n['out'], n)
                          for in_obj in graph['in'].values()
                          for n in in_obj['rev_deps']
                          if n['op'] == '*')
    for var, node in list(possible_nodes.items()):
        possible_nodes.update(dict((n['out'], n)
                                   for n in node['rev_deps']
                                   if n['op'] == '*'))
    possible_nodes = list(sorted(possible_nodes.items()))
    possible_nodes = [n for v, n in possible_nodes]
    existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets = {}, {}, tuple(), tuple(REGISTERS), tuple(), tuple(), tuple()
    for var in tuple(): #('x20_tmp', 'x49_tmp', 'x51_tmp', 'x55_tmp', 'x53_tmp'):
        print(var)
        cur_possible_nodes = [n for n in possible_nodes if n['out'] == var]
        cur_possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets \
            = allocate_one_subtree(cur_possible_nodes, existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets)
        existing.update(cur_map)
        cur_map = {}
    for count in range(10):
        print(count)
        possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets \
            = allocate_one_subtree(possible_nodes, existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets)
        existing.update(cur_map)
        cur_map = {}
    #my_node = [n for n in possible_nodes if n['out'] == 'x36_tmp'][0]
    #fill_subgraph(my_node)
    #possible_nodes, cur_map, free_temps, free_list, all_temps \
    #        = allocate_one_subtree([my_node], existing, cur_map, free_temps, free_list, all_temps)
    #mul_node = possible_nodes[0]
    #print([n['out'] for n in mul_node['deps']])
    #cur_map, free_temps, free_list, all_temps = allocate_subgraph(existing, mul_node, cur_map, free_temps, free_list, all_temps)
    print((existing, free_temps, free_list, all_temps))
    #fill_deps(buckets[0])
    deps = adjust_bits(data, print_graph(graph, existing))
    with codecs.open('femulData%d.dot' % i, 'w', encoding='utf8') as f:
        f.write(deps)
    for fmt in ('png', 'svg'):
        subprocess.call(['dot', '-T%s' % fmt, 'femulData%d.dot' % i, '-o', 'femulData%d.%s' % (i, fmt)])
