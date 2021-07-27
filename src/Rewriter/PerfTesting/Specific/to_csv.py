#!/usr/bin/env python3
import sys, re, csv

SILENCE_MISSING_REAL_USER_WARNING = True

def warn(text):
    sys.stderr.write(text + '\n')

def get_input(fname):
    if fname == '-':
        return sys.stdin.readlines()
    else:
        with open(fname, 'r') as f:
            return f.readlines()

def postformat(lines):
    i = 0
    while i < len(lines):
        if i + 1 < len(lines):
            if lines[i].startswith('Testing ') and lines[i+1].startswith('Tactic call ran for'):
                yield lines[i] + lines[i+1]
                i += 2
                continue
        if lines[i].startswith('Testing '):
            yield lines[i]
            i += 1
        elif lines[i].strip() in ('', 'No such index') or lines[i].startswith('No params'):
            i += 1
        else:
            warn('Could not recognize: %s' % lines[i])
            i += 1

def eval_numexpr(numexpr):
    # copying from https://stackoverflow.com/a/25437733/377022
    numexpr = re.sub(r"\.(?![0-9])", "", numexpr) # purge any instance of '.' not followed by a number
    return eval(numexpr, {'__builtins__':None})

REGS = {'kind': r'(UnsaturatedSolinas|WordByWordMontgomery)',
        'bitwidth': r'bitwidth = ([0-9]+)',
        'prime': r'(?:UnsaturatedSolinas|WordByWordMontgomery)[\s"]*([^" ]+)',
        'method': r'method = ([a-zA-Z0-9_-]+)',
        'descr': r'\|}\s*\)[\s"]*([^:]+)',
        'real': r'(?:ran for |real:\s*)([0-9\.]*) s',
        'user': r'(?:secs \(|user:\s*)([0-9\.]*)(?:u,| s)',
        'index': r'(?:index = ([0-9]+)|WordByWordMontgomery)',
        'nlimbs': r'(?:[ \.]n := ([0-9]+)|WordByWordMontgomery)'}
def get_data(line):
    ret = {}
    bad = False
    for key, reg in REGS.items():
        res = re.search(reg, line)
        if res is None:
            if key in ('real', 'user'):
                if SILENCE_MISSING_REAL_USER_WARNING: return None
                else: bad = True
            warn('Could not find %s (%s) in %s' % (key, reg, line))
        else:
            ret[key] = res.groups()[0]
            if ret[key] is None: ret[key] = ''
            ret[key] = ret[key].replace('"', '').strip()
    if ret['index'] != '': ret['index'] = '(%s)' % ret['index']
    ret['prime_str'] = ret['prime']
    ret['prime'] = eval_numexpr(ret['prime'].replace('^', '**'))
    if ' with ' in ret['descr']:
        ret['descr1'], ret['descr2'] = ret['descr'].split(' with ')
    else:
        ret['descr1'], ret['descr2'] = ret['descr'], ''
    del ret['descr']
    if bad: return None
    return ret

def get_data_for_graph(lines, key_is_good):
    def key_for_sort(key):
        return ('Gallina' in key, 'cbv' in key, 'vm_compute' in key, 'extraction' in key, key)
    data = {}
    for line in map(get_data, lines):
        if line is None: continue
        prime = line['prime']
        if not prime in data.keys(): data[prime] = {}
        key = ('%(kind)s x%(bitwidth)s %(index)s | %(descr1)s with %(descr2)s using %(method)s' % line).strip()
        new_data = {'real': line['real'], 'user': line['user']}
        if key in data[prime]: warn('Overwriting (%s) data[%s][%s] = %s with %s' % (line['prime_str'], prime, key, str(data[prime][key]), str(new_data)))
        data[prime][key] = new_data
    pre_all_keys = list(sorted(set(key for dat in data.values() for key in dat.keys() if key_is_good(key)), key=key_for_sort))
    all_keys = list(sorted(set(key.split(' | ')[1] for key in pre_all_keys), key=key_for_sort))
    extra_key_parts = list(sorted(set(key.split(' | ')[0] for key in pre_all_keys)))
    return data, all_keys, extra_key_parts


POSSIBLE_COLUMNS = ('perf_old_vm_times',
                    'perf_new_vm_times',
                    'perf_new_extraction_times',
                    'perf_old_cbv_times',
	            'perf_new_extraction_over_old_vm',
                    'perf_new_vm_over_old_vm',
                    'perf_old_vm_over_old_vm',
	            'perf_new_extraction_over_new_extraction',
                    'perf_new_vm_over_new_extraction',
                    'perf_old_vm_over_new_extraction')

def lines_to_rows(lines, for_graph=False, real_or_user='real', only=None, **kwargs):
    def key_is_good(key):
        if only is not None and only.replace('-', ' ').replace('_', ' ') not in key: return False
        if 'lazy' in key or '(1)' in key or 'native_compute' in key: return False
        if 'Pipeline' in key and 'NBE' not in key: return False
        if 'Pipeline' in key and 'cbv' in key: return False
        if 'Pipeline' not in key and 'GallinaAxOf' not in key: return False
        return True
    if for_graph:
        data, all_keys, extra_key_parts = get_data_for_graph(lines, key_is_good)
        yield ['prime'] + [key + (' (%s, s)' % real_or_user) for key in all_keys] + ['extra info']
        defaultv = None
        default = {'real':defaultv, 'user':defaultv}
        for prime in sorted(data.keys(), key=int):
            for extra_key in extra_key_parts:
                yield [prime] + [data[prime].get(extra_key + ' | ' + short_key, default)[real_or_user] for short_key in all_keys] + [extra_key]
    elif any(kwargs[col] for col in POSSIBLE_COLUMNS):
        data, all_keys, extra_key_parts = get_data_for_graph(lines, key_is_good)
        defaultv = None
        default = {'real':defaultv, 'user':defaultv}
        def format_prime(p): return p
        def format_time(t): return t
        def format_time_ratio(n, d): return float(n) / float(d)
        def get_div_row(p, n=None, d=None):
            if p is None or n is None or d is None or '' in (p, n, d): return None
            return [format_prime(p), format_time_ratio(n, d)]
        def get_row(p, t=None):
            if p is None or t is None or '' in (p, t): return
            return [format_prime(p), format_time(t)]
        arg_to_key_filter = {
            'perf_old_vm_times': (lambda short_key: 'Pipeline' not in short_key and 'vm_compute' in short_key and 'precomputed_decision_tree' in short_key),
            'perf_new_vm_times': (lambda short_key: 'Pipeline' in short_key and 'vm_compute' in short_key and 'precomputed_decision_tree' in short_key),
            'perf_new_extraction_times': (lambda short_key: 'Pipeline' in short_key and 'extraction' in short_key and 'precomputed_decision_tree' in short_key),
            'perf_old_cbv_times': (lambda short_key: 'Pipeline' not in short_key and 'cbv' in short_key and 'precomputed_decision_tree' in short_key)
        }
        div_arg_to_key_filters = dict(
            (key, (arg_to_key_filter['perf_' + n_key + '_times'], arg_to_key_filter['perf_' + d_key + '_times']))
            for key, (n_key, d_key) in
            [(key, key.replace('perf_', '').split('_over_')) for key in POSSIBLE_COLUMNS if '_over_' in key]
        )

        for prime in sorted(data.keys(), key=int):
            for extra_key in extra_key_parts:
                extra_args = [(short_key, data[prime].get(extra_key + ' | ' + short_key, default)[real_or_user]) for short_key in all_keys]
                for arg, key_filter in arg_to_key_filter.items():
                    if kwargs[arg]:
                        row = get_row(prime, *[v for short_key, v in extra_args if key_filter(short_key)])
                        if row is not None: yield row
                for arg, (n_key_filter, d_key_filter) in div_arg_to_key_filters.items():
                    if kwargs[arg]:
                        row = get_div_row(prime,
                                          *[v for short_key, v in extra_args if n_key_filter(short_key)],
                                          *[v for short_key, v in extra_args if d_key_filter(short_key)])
                        if row is not None: yield row
    else:
        keys = ['prime', 'user', 'real', 'kind', 'bitwidth', 'descr1', 'descr2', 'method', 'index', 'nlimbs', 'prime_str']
        yield list(keys)
        for data in map(get_data, lines):
            if data is None: continue
            yield [data[k] for k in keys]

def writecsv(outfname, lines, **kwargs):
    rows = lines_to_rows(lines, **kwargs)
    def do_write(csvfile):
        writer = csv.writer(csvfile, quoting=csv.QUOTE_MINIMAL, lineterminator='\n')
        writer.writerows(rows)
    if outfname == '-': do_write(sys.stdout)
    else:
        with open(outfnname, 'w', newline='') as csvfile:
            do_write(csvfile)

def writetxt(outfname, lines, **kwargs):
    rows = lines_to_rows(lines, **kwargs)
    def do_write(txtfile):
        txtfile.write('\n'.join(' '.join(map(str, row)) for row in rows))
    if outfname == '-': do_write(sys.stdout)
    else:
        with open(outfnname, 'w', newline='') as txtfile:
            do_write(txtfile)

if __name__ == '__main__':
    fnames = sys.argv[1:]
    outfname = '-'
    if '-o' in fnames:
        i = fnames.index('-o')
        outfname = fnames[i+1]
        del fnames[i+1]
        del fnames[i]
    only = None
    for i, fname in enumerate(fnames):
        if '--only-' in fname and fname.startswith('--'):
            if only is not None:
                raise Exception('Only one argument can start with -- and contain --only-')
            fnames[i], only = fname.split('--only-')
    kwargs = dict([('for_graph', False)] + [(i, False) for i in POSSIBLE_COLUMNS])
    for key in kwargs.keys():
        arg = '--' + key.replace('_', '-')
        if arg in fnames:
            kwargs[key] = True
            del fnames[fnames.index(arg)]
    kwargs['only'] = only
    txt = False
    if '--txt' in fnames:
        txt = True
        del fnames[fnames.index('--txt')]
    while '--file-list' in fnames:
        file_list_file = fnames[fnames.index('--file-list')+1]
        del fnames[fnames.index('--file-list')+1]
        del fnames[fnames.index('--file-list')]
        with open(file_list_file, 'r') as f:
            file_list = [i.strip() for i in f.readlines() if i.strip()]
        fnames.extend(file_list)
    lines = [line
             for fname in fnames
             for line in postformat(get_input(fname))]
    if txt:
        writetxt(outfname, lines, **kwargs)
    else:
        writecsv(outfname, lines, **kwargs)
