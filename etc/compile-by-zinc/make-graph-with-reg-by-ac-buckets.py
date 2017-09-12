#!/usr/bin/env python
from __future__ import with_statement
from memoize import memoize
import codecs, re, sys, os
import subprocess

LAMBDA = u'\u03bb'

NAMED_REGISTERS = ('RAX', 'RCX', 'RDX', 'RBX', 'RSP', 'RSI', 'RDI')
NAMED_REGISTER_MAPPING = dict(('r%d' % i, reg) for i, reg in enumerate(NAMED_REGISTERS))
REGISTERS = tuple(#['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP'] + #, 'RSP'] # RSP is stack pointer?
    ['reg%d' % i for i in range(13)])
#REAL_REGISTERS = tuple(['RAX', 'RBX', 'RCX', 'RDX', 'RSI', 'RDI', 'RBP'] + #, 'RSP'] # RSP is stack pointer?
#    ['reg%d' % i for i in range(13)])
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
            obj_low['rev_deps'] = list(obj_low['rev_deps']) + [obj_carry]
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

def get_objects(start, ret=None):
    if ret is None: ret = {}
    for node in start:
        if node['out'] in ret.keys(): continue
        ret[node['out']] = node
        get_objects(node['deps'], ret=ret)
    return ret

def prune(start):
    objs = get_objects(start)
    for var in objs.keys():
        objs[var]['rev_deps'] = tuple(objs[arg] for arg in sorted(objs.keys())
                                      if any(node['out'] == var for node in objs[arg]['deps']))

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
    prune(tuple(graph['out'].values()))
    #split_graph(objs)
    return graph


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

def is_allocated_to_reg(full_map, node):
    return node['out'] in full_map.keys() and all(reg in REGISTERS for reg in full_map[node['out']].split(':'))

def deps_allocated(full_map, node):
    if node['op'] == 'INPUT': return True
    if node['out'] not in full_map.keys(): return False
    return all(deps_allocated(full_map, dep) for dep in node['deps'])

# returns {cur_map with new_name->reg}, still_free_temps, still_free_list, all_temps, freed, new_buckets, emit_vars
def allocate_node(existing, node, *args):
    cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars = args
    free_temps = list(free_temps)
    free_list = list(free_list)
    all_temps = list(all_temps)
    full_map = dict(existing)
    cur_map = dict(cur_map)
    freed = list(freed)
    new_buckets = list(new_buckets)
    emit_vars = list(emit_vars)
    full_map.update(cur_map)
    def do_ret():
        return cur_map, tuple(free_temps), tuple(free_list), tuple(all_temps), tuple(freed), tuple(new_buckets), tuple(emit_vars)
    def do_free(var):
        for reg in full_map[var].split(':'):
            if reg in all_temps:
                if reg not in free_temps:
                    free_temps.append(reg)
            elif reg in REGISTERS:
                if reg not in free_list:
                    print('freeing %s from %s' % (reg, var))
                    free_list.append(reg)
    def do_free_deps(node):
        full_map.update(cur_map)
        if node['out'] in full_map.keys():
            for dep in node['deps']:
                if dep['out'] in freed or dep['out'] not in full_map.keys(): continue
                if not is_allocated_to_reg(full_map, dep): continue
                if (all(deps_allocated(full_map, rdep) for rdep in dep['rev_deps']) or
                    all(reg in all_temps for reg in full_map[dep['out']].split(':'))):
                    do_free(dep['out'])
                    freed.append(dep['out'])
    if node['out'] in full_map.keys():
        do_free_deps(node)
        return do_ret()
    #print('alloc: %s (of %d)' % (node['out'], len(free_list)))
    if node['op'] in ('GET_HIGH', 'GET_LOW') and len(node['deps']) == 1 and len(node['deps'][0]['rev_deps']) <= 2 and all(n['op'] in ('GET_HIGH', 'GET_LOW') for n in node['deps'][0]['rev_deps']) and is_allocated_to_reg(full_map, node['deps'][0]):
        reg_idx = {'GET_LOW':0, 'GET_HIGH':1}[node['op']]
        cur_map[node['out']] = full_map[node['deps'][0]['out']].split(':')[reg_idx]
        emit_vars.append(node)
        return do_ret()
    if len(node['deps']) == 1 and len(node['deps'][0]['rev_deps']) == 1 and is_allocated_to_reg(full_map, node['deps'][0]) and node['type'] == node['deps'][0]['type']:
        cur_map[node['out']] = full_map[node['deps'][0]['out']]
        emit_vars.append(node)
        return do_ret()
    if len(node['deps']) == 0 and node['op'] == 'INPUT':
        assert(node['type'] == 'uint64_t')
        cur_map[node['out']] = 'm' + node['out'] # free_list.pop()
        emit_vars.append(node)
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
        emit_vars.append(node)
        do_free_deps(node)
        return do_ret()
    if node['op'] == '+' and node['type'] == 'uint64_t' and len(node['extra_out']) > 0:
        cur_map[node['out']] = free_list.pop()
        emit_vars.append(node)
        new_buckets.append(node)
        do_free_deps(node)
        return do_ret()
    if node['op'] == '*' and node['type'] == 'uint64_t' and len(node['deps']) == 1:
        dep = node['deps'][0]
        assert(dep['out'] in full_map.keys())
        if is_allocated_to_reg(full_map, dep) and \
           all(rdep is node or (is_allocated_to_reg(full_map, rdep) and full_map[rdep['out']] != full_map[dep['out']])
               for rdep in dep['rev_deps']):
            cur_map[node['out']] = full_map[dep['out']]
            freed += [dep['out']]
        else:
            cur_map[node['out']] = free_list.pop()
        emit_vars.append(node)
        return do_ret()
    raw_input([node['out'], node['op'], node['type'], [(dep['out'], full_map.get(dep['out'])) for dep in node['deps']]])
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

def print_nodes(objs):
    for var in sorted(objs.keys(), key=(lambda s:(int(s.strip('cx_lowhightmp')), s))):
        yield '    %s [label="%s%s" %s];\n' % (objs[var]['out'], ' + '.join(sorted([objs[var]['out']] + list(objs[var]['extra_out']))), objs[var]['reg'], objs[var]['style'])
def print_deps(objs):
    for var in sorted(objs.keys()):
        for dep in objs[var]['deps']:
            yield '    %s -> %s [ label="%s" ] ;\n' % (dep['out'], objs[var]['out'], objs[var]['op'])

def push_allocate(existing, nodes, *args, **kwargs):
    if 'seen' not in kwargs.keys(): kwargs['seen'] = set()
    full_map = dict(existing)
    for node in nodes:
        if node['out'] in kwargs['seen']: continue
        cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars = args
        free_temps = list(free_temps)
        free_list = list(free_list)
        all_temps = list(all_temps)
        cur_map = dict(cur_map)
        freed = list(freed)
        new_buckets = list(new_buckets)
        emit_vars = list(emit_vars)
        full_map.update(cur_map)
        if node['out'] in full_map.keys() and node['op'] == '+' and all(d['out'] not in full_map.keys() for d in node['rev_deps']) and set(d['op'] for d in node['rev_deps']) == set(('&', 'COMBINE', 'GET_CARRY')):
            and_node = [d for d in node['rev_deps'] if d['op'] == '&'][0]
            carry_node = [d for d in node['rev_deps'] if d['op'] == 'GET_CARRY'][0]
            combine_node = [d for d in node['rev_deps'] if d['op'] == 'COMBINE'][0]
            high_node = [d for d in combine_node['deps'] if d is not node][0]
            assert(len(combine_node['rev_deps']) == 1)
            shr_node = combine_node['rev_deps'][0]
            assert(shr_node['op'] == '>>')
            assert(shr_node['out'] not in full_map.keys())
            assert(len(combine_node['deps']) == 2)
            assert(all(d['out'] in full_map.keys() for d in combine_node['deps']))
            cur_map[carry_node['out']] = 'c0'
            emit_vars.append(carry_node)
            cur_map[combine_node['out']] = ':'.join(full_map[d['out']] for d in combine_node['deps'])
            emit_vars.append(combine_node)
            assert(high_node['out'] in full_map.keys())
            cur_map[shr_node['out']] = full_map[high_node['out']]
            emit_vars.append(shr_node)
            cur_map[and_node['out']] = full_map[node['out']]
            emit_vars.append(and_node)
            fill_node(combine_node)
            fill_node(carry_node)
            fill_node(shr_node)
            fill_node(and_node)
            freed += [node['out'], carry_node['out'], high_node['out'], combine_node['out']]
        elif node['out'] in full_map.keys() and len(node['rev_deps']) == 1 and all(d['out'] not in full_map.keys() for d in node['rev_deps']) and len(node['rev_deps'][0]['deps']) == 1 and node['type'] == node['rev_deps'][0]['type']:
            next_node = node['rev_deps'][0]
            cur_map[next_node['out']] = full_map[node['out']]
            emit_vars.append(next_node)
            fill_node(next_node)
            full_map.update(cur_map)
            freed += [node['out']]
        elif node['out'] not in full_map.keys() and len(node['rev_deps']) == 2 and len(node['deps']) == 2 and all(d['out'] not in full_map.keys() for d in node['rev_deps']) and all(d['out'] in full_map.keys() for d in node['deps']) and node['type'] == 'uint64_t' and all(d['type'] == 'uint64_t' for d in node['rev_deps']) and all(d['type'] == 'uint64_t' for d in node['deps']):
            from1, from2 = node['deps']
            to1, to2 = node['rev_deps']
            assert(full_map[from1['out']] != full_map[from2['out']])
            cur_map[node['out']] = full_map[from1['out']]
            emit_vars.append(node)
            cur_map[to1['out']] = full_map[from1['out']]
            emit_vars.append(to1)
            cur_map[to2['out']] = full_map[from2['out']]
            emit_vars.append(to2)
            fill_node(node)
            fill_node(to1)
            fill_node(to2)
            full_map.update(cur_map)
            freed += [node['out'], from1['out'], from2['out']]
        elif node['out'] not in full_map.keys() and len(node['rev_deps']) == 0 and len(node['deps']) == 2 and all(d['out'] not in full_map.keys() for d in node['rev_deps']) and all(d['out'] in full_map.keys() for d in node['deps']) and node['type'] == 'uint64_t' and all(d['type'] == 'uint64_t' for d in node['rev_deps']) and all(d['type'] == 'uint64_t' for d in node['deps']):
            from1, from2 = node['deps']
            assert(full_map[from1['out']] != full_map[from2['out']])
            cur_map[node['out']] = full_map[from1['out']]
            emit_vars.append(node)
            fill_node(node)
            full_map.update(cur_map)
            freed += [from1['out'], from2['out']]
        full_map.update(cur_map)
        args = (cur_map, tuple(free_temps), tuple(free_list), tuple(all_temps), tuple(freed), tuple(new_buckets), tuple(emit_vars))
        kwargs['seen'].add(node['out'])
        args = push_allocate(existing, node['rev_deps'], *args, **kwargs)
    return args

def allocate_one_subtree(in_nodes, possible_nodes, existing, *args):
    cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars = args
    existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars \
        = dict(existing), dict(cur_map), list(free_temps), list(free_list), list(all_temps), tuple(freed), tuple(new_buckets), tuple(emit_vars)
    args = (cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars)
    sorted_nodes = []
    for node in possible_nodes:
        try:
            lens = [len([rd for rd in d['rev_deps'] if rd['out'] not in existing.keys()]) for d in node['deps']]
            temp_cur_map, temp_free_temps, temp_free_list, temp_all_temps, temp_freed, temp_new_buckets, temp_emit_vars = allocate_subgraph(existing, node, *args)
            if set(temp_free_temps) != set(temp_all_temps):
                print(('BAD', node['out'], temp_cur_map, temp_free_temps, temp_free_list, temp_all_temps, temp_freed))
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
    args = push_allocate(existing, in_nodes, *args)
    cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars = args
    return possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars


def print_graph(graph, allocs):
    objs = get_objects(graph['out'].values())
    annotate_with_alloc(objs.values(), allocs)
    body = ''.join(print_nodes(objs))
    body += ''.join(print_deps(objs))
    body += ''.join('    in -> %s ;\n' % node['out'] for node in graph['in'].values())
    body += ''.join('    %s -> out ;\n' % node['out'] for node in graph['out'].values())
    return ('digraph G {\n' + body + '}\n')

def fix_emit_vars(emit_vars):
    ret = []
    waiting = []
    seen = set()
    for node in emit_vars:
        waiting.append(node)
        new_waiting = []
        for wnode in waiting:
            if wnode['out'] in seen:
                continue
            elif all(dep['out'] in seen for dep in wnode['deps']):
                ret.append(wnode)
                seen.add(wnode['out'])
            else:
                new_waiting.append(wnode)
        waiting = new_waiting
    while len(waiting) > 0:
        print('Waiting on...')
        print(list(sorted(node['out'] for node in waiting)))
        new_waiting = []
        for wnode in waiting:
            if wnode['out'] in seen:
                continue
            elif all(dep['out'] in seen for dep in wnode['deps']):
                ret.append(wnode)
                seen.add(wnode['out'])
            else:
                new_waiting.append(wnode)
        waiting = new_waiting
    return tuple(ret)

def print_input(reg_out, mem_in):
    #return '%s <- LOAD %s;\n' % (reg_out, mem_in)
    #return '"mov %%[%s], %%[%s]\\n\\t"\n' % (mem_in, reg_out)
    return ""

def print_val(reg):
    if reg.upper() in NAMED_REGISTERS:
        return '%%%s' % reg
    if reg[:2] == '0x':
        return '$%s' % reg
    return '%%[%s]' % reg

def print_load_specific_reg(reg, specific_reg='rdx'):
    ret = ''
    #ret += '"mov %%%s, %%[%s_backup]\\t\\n" // XXX: How do I specify that a particular register should be %s?\n' % (specific_reg, specific_reg, specific_reg)
    if reg != specific_reg:
        ret += '"mov %s, %s\\t\\n"\n' % (print_val(reg), print_val(specific_reg))
    return ret, specific_reg
def print_unload_specific_reg(specific_reg='rdx'):
    ret = ''
    #ret += '"mov %%[%s_backup], %%%s\\t\\n" // XXX: How do I specify that a particular register should be %s?\n' % (specific_reg, specific_reg, specific_reg)
    return ret
#def get_arg_reg(d):
#    return 'arg%d' % d
def print_load(reg, can_clobber=tuple(), dont_clobber=tuple()):
    assert(not isinstance(can_clobber, str))
    assert(not isinstance(dont_clobber, str))
    can_clobber = [i for i in reversed(can_clobber) if i not in dont_clobber]
    if reg in REGISTERS:
        return ('', reg)
    else:
        cur_reg = can_clobber.pop()
        ret = '"mov %s, %s\\t\\n"\n' % (print_val(reg), print_val(cur_reg))
        return (ret, cur_reg)

def print_mulx(reg_out_low, reg_out_high, rx1, rx2, src):
    #return '%s:%s <- MULX %s, %s; // %s\n' % (reg_out_low, reg_out_high, rx1, rx2, src)
    ret = ''
    ret2, actual_rx1 = print_load_specific_reg(rx1, 'rdx')
    assert(rx2 != actual_rx1)
    ret3, actual_rx2 = print_load(rx2, can_clobber=[reg_out_high, reg_out_low], dont_clobber=[actual_rx1])
    ret += ret2 + ret3 + ('"mulx %s, %s, %s\\t\\n" // %s\n' % (print_val(actual_rx2), print_val(reg_out_high), print_val(reg_out_low), src))
    ret += print_unload_specific_reg('rdx')
    return ret

def print_mov_bucket(reg_out, reg_in, bucket):
    #return '%s <- MOV %s; // bucket: %s\n' % (reg_out, reg_in, bucket)
    #ret, reg_in = print_load(reg_in, can_clobber=[reg_out])
    return ('"mov %s, %s\\t\\n" // bucket: %s\n' % (print_val(reg_in), print_val(reg_out), bucket))

def print_mov(reg_out, reg_in):
    #return '%s <- MOV %s;\n' % (reg_out, reg_in)
    #ret, reg_in = print_load(reg_in)
    return ('"mov %s, %s\\t\\n"\n' % (print_val(reg_in), print_val(reg_out)))

def print_load_constant(reg_out, imm):
    assert(imm[:2] == '0x')
    return ('"mov $%s, %s\\t\\n"\n' % (imm, print_val(reg_out)))

LAST_CARRY = None

def print_mul_by_constant(reg_out, reg_in, constant, src):
    #return '%s <- MULX %s, %s; // %s\n' % (ret_out, reg_in, constant, src)
    ret = ''
    if constant == '0x13':
        ret += ('// FIXME: lea for %s\n' % src)
    assert(constant[:2] == '0x')
    return ret + \
        print_load_constant('rdx', constant) + \
        print_mulx(reg_out, 'rdx', 'rdx', reg_in, src)

def print_adx(reg_out, rx1, rx2, bucket):
    #return '%s <- ADX %s, %s; // bucket: %s\n' % (reg_out, rx1, rx2, bucket)
    assert(rx1 == reg_out)
    ret, rx2 = print_load(rx2, dont_clobber=[rx1])
    return ret + ('"adx %%[%s], %%[%s]\\t\\n" // bucket: %s\n' % (rx2, reg_out, bucket))

def print_add(reg_out, cf, rx1, rx2, bucket):
    #return '%s, (%s) <- ADD %s, %s; // bucket: %s\n' % (reg_out, cf, rx1, rx2, bucket)
    global LAST_CARRY
    assert(reg_out == rx1)
    #assert(LAST_CARRY is None or LAST_CARRY == cf)
    LAST_CARRY = cf
    ret, rx2 = print_load(rx2, dont_clobber=[rx1])
    return ret + ('"add %%[%s], %%[%s]\\t\\n" // bucket: %s\n' % (rx2, reg_out, bucket))

def print_adc(reg_out, cf, rx1, rx2, bucket):
    #return '%s, (%s) <- ADC (%s), %s, %s; // bucket: %s\n' % (reg_out, cf, cf, rx1, rx2, bucket)
    assert(reg_out == rx1)
    ret = ''
    global LAST_CARRY
    if LAST_CARRY != cf:
        ret += 'ERRRRRRROR: %s != %s\n' % (LAST_CARRY, cf)
        LAST_CARRY = cf
    ret2, rx2 = print_load(rx2, dont_clobber=[rx1])
    ret += ret2
    return ret + ('"adc %%[%s], %%[%s]\\t\\n" // bucket: %s\n' % (rx2, reg_out, bucket))

def print_adcx(reg_out, cf, bucket):
    #return '%s <- ADCX (%s), %s, 0x0; // bucket: %s\n' % (reg_out, cf, reg_out, bucket)
    assert(LAST_CARRY == cf)
    return ('"adcx $0, %%[%s]\\t\\n" // bucket: %s\n' % (reg_out, bucket))

def print_and(reg_out, rx1, rx2, src):
    #return '%s <- AND %s, %s; // %s\n' % (reg_out, rx1, rx2, src)
    global LAST_CARRY
    LAST_CARRY = None
    if reg_out != rx1:
        return print_mov(reg_out, rx1) + print_and(reg_out, reg_out, rx2, src)
    else:
        if rx2[:2] == '0x':
            return ('"and $%s, %%[%s]\\t\\n" // %s\n' % (rx2, reg_out, src))
        else:
            ret, rx2 = print_load(rx2, can_clobber=[reg_out], dont_clobber=[rx1])
            return ret + ('"and %%[%s], %%[%s]\\t\\n" // %s\n' % (rx2, reg_out, src))

def print_shr(reg_out, rx1, imm, src):
    #return '%s <- SHR %s, %s; // %s\n' % (reg_out, rx1, imm, src)
    global LAST_CARRY
    LAST_CARRY = None
    assert(rx1 == reg_out)
    assert(imm[:2] == '0x')
    return ('"shr $%s, %%[%s]\\t\\n" // %s\n' % (imm, reg_out, src))

def print_shrd(reg_out, rx_low, rx_high, imm, src):
    #return '%s <- SHR %s, %s; // %s\n' % (reg_out, rx1, imm, src)
    global LAST_CARRY
    LAST_CARRY = None
    if rx_low != reg_out and rx_high == reg_out:
        return print_mov('rdx', rx_low) + \
            print_mov(rx_high, rx_low) + \
            print_mov(rx_low, 'rdx') + \
            print_shrd(reg_out, rx_high, rx_low, imm, src)
    assert(rx_low == reg_out)
    assert(imm[:2] == '0x')
    return ('"shrd $%s, %%[%s], %%[%s]\\t\\n" // %s\n' % (imm, rx_low, rx_high, src))


def schedule(input_data, existing, emit_vars):
    ret = ''
    buckets_seen = set()
    buckets_carried = set()
    emit_vars = fix_emit_vars(emit_vars)
    ret += ('// Convention is low_reg:high_reg\n')
    for node in emit_vars:
        if node['op'] == 'INPUT':
            ret += print_input(existing[node['out']], node['out'])
        elif node['op'] == '*' and len(node['deps']) == 2:
            assert(len(existing[node['out']].split(':')) == 2)
            out_low, out_high = existing[node['out']].split(':')
            ret += print_mulx(out_low, out_high,
                              existing[node['deps'][0]['out']],
                              existing[node['deps'][1]['out']],
                              '%s = %s * %s'
                              % (node['out'],
                                 node['deps'][0]['out'],
                                 node['deps'][1]['out']))
        elif node['op'] == '*' and len(node['deps']) == 1:
            extra_arg = [arg for arg in line_of_var(data, node['out'])['args'] if arg[:2] == '0x'][0]
            ret += print_mul_by_constant(existing[node['out']],
                                         existing[node['deps'][0]['out']],
                                         extra_arg,
                                         '%s = %s * %s'
                                         % (node['out'],
                                            node['deps'][0]['out'],
                                            extra_arg))
        elif node['op'] == '&' and len(node['deps']) == 1:
            extra_arg = [arg for arg in line_of_var(data, node['out'])['args'] if arg[:2] == '0x'][0]
            ret += print_and(existing[node['out']],
                             existing[node['deps'][0]['out']],
                             extra_arg,
                             '%s = %s & %s'
                             % (node['out'],
                                node['deps'][0]['out'],
                                extra_arg))
        elif node['op'] == '>>' and len(node['deps']) == 1 and node['deps'][0]['op'] == 'COMBINE':
            extra_arg = [arg for arg in line_of_var(data, node['out'])['args'] if arg[:2] == '0x'][0]
            ret += print_shrd(existing[node['out']],
                              existing[node['deps'][0]['deps'][0]['out']],
                              existing[node['deps'][0]['deps'][1]['out']],
                              extra_arg,
                              '%s = %s:%s >> %s'
                              % (node['out'],
                                 node['deps'][0]['deps'][0]['out'],
                                 node['deps'][0]['deps'][1]['out'],
                                 extra_arg))
        elif node['op'] == '>>' and len(node['deps']) == 1 and node['deps'][0]['type'] == 'uint64_t':
            extra_arg = [arg for arg in line_of_var(data, node['out'])['args'] if arg[:2] == '0x'][0]
            ret += print_shr(existing[node['out']],
                             existing[node['deps'][0]['deps'][0]['out']],
                             extra_arg,
                             '%s = %s >> %s'
                             % (node['out'],
                                node['deps'][0]['deps'][0]['out'],
                                extra_arg))
        elif node['op'] in ('GET_HIGH', 'GET_LOW'):
            if node['rev_deps'][0]['out'] not in buckets_seen:
                ret += print_mov_bucket(existing[node['rev_deps'][0]['out']],
                                        existing[node['out']],
                                        ' + '.join(sorted([node['rev_deps'][0]['out']] + list(node['rev_deps'][0]['extra_out']))))
                buckets_seen.add(node['rev_deps'][0]['out'])
            elif node['op'] == 'GET_HIGH':
                ret += print_adx(existing[node['rev_deps'][0]['out']],
                                 existing[node['rev_deps'][0]['out']],
                                 existing[node['out']],
                                 ' + '.join(sorted([node['rev_deps'][0]['out']] + list(node['rev_deps'][0]['extra_out']))))
            elif node['op'] == 'GET_LOW':
                carry = 'c' + node['rev_deps'][0]['out'][:-len('_low')]
                if node['rev_deps'][0]['out'] not in buckets_carried:
                    ret += print_add(existing[node['rev_deps'][0]['out']],
                                     carry,
                                     existing[node['rev_deps'][0]['out']],
                                     existing[node['out']],
                                     ' + '.join(sorted([node['rev_deps'][0]['out']] + list(node['rev_deps'][0]['extra_out']))))
                    buckets_carried.add(node['rev_deps'][0]['out'])
                else:
                    ret += print_adc(existing[node['rev_deps'][0]['out']],
                                     carry,
                                     existing[node['rev_deps'][0]['out']],
                                     existing[node['out']],
                                     ' + '.join(sorted([node['rev_deps'][0]['out']] + list(node['rev_deps'][0]['extra_out']))))
        elif node['op'] in ('GET_CARRY',):
            carry = 'c' + node['rev_deps'][0]['out'][:-len('_high')]
            ret += print_adcx(existing[node['rev_deps'][0]['out']],
                              carry,
                              ' + '.join(sorted([node['rev_deps'][0]['out']] + list(node['rev_deps'][0]['extra_out']))))
        elif node['op'] == '+' and len(node['extra_out']) > 0:
            pass
        elif node['op'] == '+' and len(node['deps']) == 2 and node['type'] == 'uint64_t':
            ret += print_adx(existing[node['out']],
                             existing[node['deps'][0]['out']],
                             existing[node['deps'][1]['out']],
                             '%s = %s + %s'
                             % (node['out'],
                                node['deps'][0]['out'],
                                node['deps'][1]['out']))
        elif node['op'] in ('COMBINE',):
            pass
        else:
            raw_input((node['out'], node['op']))
        if node['op'] not in ('GET_HIGH', 'GET_LOW', 'COMBINE', 'GET_CARRY'):
            for rdep in node['rev_deps']:
                if len(rdep['extra_out']) > 0 and rdep['op'] == '+':
                    if rdep['out'] not in buckets_seen:
                        ret += print_mov_bucket(existing[rdep['out']],
                                                existing[node['out']],
                                                ' + '.join(sorted([rdep['out']] + list(rdep['extra_out']))))
                        buckets_seen.add(rdep['out'])
                    elif 'high' in rdep['out']:
                        ret += print_adx(existing[rdep['out']],
                                         existing[rdep['out']],
                                         existing[node['out']],
                                         ' + '.join(sorted([rdep['out']] + list(rdep['extra_out']))))
                    elif 'low' in rdep['out']:
                        carry = 'c' + rdep['out'][:-len('_low')]
                        if rdep['out'] not in buckets_carried:
                            ret += print_add(existing[rdep['out']],
                                             carry,
                                             existing[rdep['out']],
                                             existing[node['out']],
                                             ' + '.join(sorted([rdep['out']] + list(rdep['extra_out']))))
                            buckets_carried.add(rdep['out'])
                        else:
                            ret += print_adc(existing[rdep['out']],
                                             carry,
                                             existing[rdep['out']],
                                             existing[node['out']],
                                             ' + '.join(sorted([rdep['out']] + list(rdep['extra_out']))))
                    else:
                        assert(False)
    return ret

def inline_schedule(sched, input_vars, output_vars):
    KNOWN_CONSTRAINTS = dict(('r%sx' % l, l) for l in 'abcd')
    def int_or_zero_key(v):
        orig = v
        v = v.strip('abcdefghijklmnopqrstuvwxyz')
        if v.isdigit(): return (int(v), orig)
        return (0, orig)
    variables = list(sorted(set(list(re.findall('%\[([a-zA-Z0-9_]*)\]', sched)) +
                                list(re.findall('%([a-zA-Z0-9_]+)', sched))),
                            key=int_or_zero_key))
    mems, variables = [i for i in variables if i[:2] == 'mx'], [i for i in variables if i[:2] != 'mx']
    special_reg, variables = [i for i in variables if i.upper() in NAMED_REGISTERS], [i for i in variables if i.upper() not in NAMED_REGISTERS]
    transient_regs, output_regs = [i for i in variables if i not in output_vars.values()], [i for i in variables if i in output_vars.keys()]
    available_registers = ['r%d' % i for i in range(16)
                           if ('r%d' % i) not in NAMED_REGISTER_MAPPING.keys() or NAMED_REGISTER_MAPPING['r%d' % i].lower() not in special_reg]
    for reg in output_regs:
        sched = sched.replace('%%[%s]' % reg, '%%[r%s]' % output_vars[reg])
    renaming = dict((from_reg, to_reg) for from_reg, to_reg in zip(transient_regs, available_registers[-len(transient_regs):]))
    for from_reg, to_reg in renaming.items():
        sched = sched.replace('%%[%s]' % from_reg, '%%%s' % to_reg)
    transient_regs = [renaming[reg] for reg in transient_regs]
    ret = ''
    ret += 'asm (\n'
    ret += sched
    ret += ': ' + ', '.join(['[r%s] "=&r" (%s)' % (output_vars[reg], output_vars[reg]) for reg in output_regs]) + '\n'
    ret += ': ' + ', '.join(['[%s] "m" (%s)' % (reg, input_vars[reg]) for reg in input_vars]) + '\n'
    ret += ': ' + ', '.join(['"cc"'] +
                            ['"%s"' % reg for reg in special_reg] +
                            ['"%s"' % reg for reg in transient_regs]) + '\n'
    ret += ');\n'
    return ret

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
    in_nodes = tuple(graph['in'].values())
    existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars = {}, {}, tuple(), tuple(REGISTERS), tuple(), tuple(), tuple(), tuple()
    objs = get_objects(graph['out'].values())
    def vars_for(var, rec=True):
        pre_ret = [n['out'] for n in objs[var]['rev_deps']]
        ret = [v for v in pre_ret if 'tmp' in v]
        if rec:
            for v in pre_ret:
                if 'tmp' not in v:
                    ret += list(vars_for(v, rec=False))
        return tuple(ret)
    def vars_for_bucket(var):
        if '_' not in var:
            return tuple(list(vars_for_bucket(var + '_low')) + list(vars_for_bucket(var + '_high')))
        ret = []
        for dep in objs[var]['deps']:
            if dep['op'] in ('GET_HIGH', 'GET_LOW'):
                assert(len(dep['deps']) == 1)
                assert('tmp' in dep['deps'][0]['out'])
                ret.append(dep['deps'][0]['out'])
        return tuple(ret)
#    for var in list(vars_for('x10')) + list(vars_for('x11')) + list(vars_for('x9')) + list(vars_for('x7')) + list(vars_for('x5')): # tuple(): #('x20_tmp', 'x49_tmp', 'x51_tmp', 'x55_tmp', 'x53_tmp'):
    for var in list(vars_for_bucket('x56')) + list(vars_for_bucket('x71')) + list(vars_for_bucket('x74')) + list(vars_for_bucket('x77')) + list(vars_for_bucket('x80')): # + list(vars_for('x11')) + list(vars_for('x9')) + list(vars_for('x7')) + list(vars_for('x5')): # tuple(): #('x20_tmp', 'x49_tmp', 'x51_tmp', 'x55_tmp', 'x53_tmp'):
        print(var)
        cur_possible_nodes = [n for n in possible_nodes if n['out'] == var]
        cur_possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars \
            = allocate_one_subtree(in_nodes, cur_possible_nodes, existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars)
        existing.update(cur_map)
        cur_map = {}
    for count in range(0 * 16):
        print(count)
        possible_nodes, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars \
            = allocate_one_subtree(in_nodes, possible_nodes, existing, cur_map, free_temps, free_list, all_temps, freed, new_buckets, emit_vars)
        existing.update(cur_map)
        cur_map = {}
    #my_node = [n for n in possible_nodes if n['out'] == 'x36_tmp'][0]
    #fill_subgraph(my_node)
    #possible_nodes, cur_map, free_temps, free_list, all_temps \
    #        = allocate_one_subtree([my_node], existing, cur_map, free_temps, free_list, all_temps)
    #mul_node = possible_nodes[0]
    #print([n['out'] for n in mul_node['deps']])
    #cur_map, free_temps, free_list, all_temps = allocate_subgraph(existing, mul_node, cur_map, free_temps, free_list, all_temps)
    sched = inline_schedule(schedule(data, existing, emit_vars),
                            dict((existing[n['out']], n['out']) for n in graph['in'].values()),
                            dict((existing[n['out']], n['out']) for n in graph['out'].values()))
    #fill_deps(buckets[0])
    deps = adjust_bits(data, print_graph(graph, existing))
    with codecs.open('femulData%d.dot' % i, 'w', encoding='utf8') as f:
        f.write(deps)
    with codecs.open('femulDisplayScheduled%d.log' % i, 'w', encoding='utf8') as f:
        f.write(sched)
    for fmt in ('png', 'svg'):
        subprocess.call(['dot', '-T%s' % fmt, 'femulData%d.dot' % i, '-o', 'femulData%d.%s' % (i, fmt)])
