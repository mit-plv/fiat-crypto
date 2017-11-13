import sys, collections


results = {}

def do_impl(prime, impl, time):
    if prime not in results.keys():
        results[prime] = {}
    if impl not in results[prime].keys():
        results[prime][impl] = 1e400
    results[prime][impl] = min(results[prime][impl], time)

for line in sys.stdin:
    prime, impl, time = line.split()
    # impl = {'fiat_solinas32':'fiat_solinas',
    #         'fiat_solinas64':'fiat_solinas',
    #         'fiat_montgomery64':'fiat_montgomery',
    #         'fiat_montgomery32':'fiat_montgomery',
    #        }.get(impl, impl)
    time = float(time)
    do_impl(prime, impl, time)
    # do_impl(prime,'xfiat' if 'fiat' in impl else 'xgmp', time)

def format_prime(p):
    return p.replace('x','*').replace('p','+').replace('e','^').replace('m','-')

impls = sorted(set(sum((list(d.keys()) for d in results.values()),[])))
print('\t'.join(['.']+impls))
for p in sorted(list(results.keys())):
    r = results[p].get('xgmp', 1e400) / results[p].get('xfiat', 1e400)
    print('\t'.join([format_prime(p)]+[str(results[p].get(i,'-')) for i in impls]))
