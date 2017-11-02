
'''
EXAMPLES (handwritten):


# p256 - amd128
{
    "modulus"              : "2^256-2^224+2^192+2^96-1",
    "base"                 : "128",
    "sz"                   : "2",
    "bitwidth"             : "128",
    "montgomery"           : "true",
    "operations"           : ["fenz", "feadd", "femul", "feopp", "fesub"],
    "compiler"             : "gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing"
}

# p256 - amd64
{
    "modulus"              : "2^256-2^224+2^192+2^96-1",
    "base"                 : "64",
    "sz"                   : "4",
    "bitwidth"             : "64",
    "montgomery"           : "true",
    "operations"           : ["fenz", "feadd", "femul", "feopp", "fesub"],
    "compiler"             : "gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing"
}


# p448 - c64
{
    "modulus"          : "2^448-2^224-1",
    "base"             : "56",
    "goldilocks"       : "true",
    "sz"               : "8",
    "bitwidth"         : "64",
    "carry_chains"     : [[3, 7],
			  [0, 4, 1, 5, 2, 6, 3, 7],
			  [4, 0]],
    "coef_div_modulus" : "2",
    "operations"       : ["femul"]
}

# curve25519 - c64
{
    "modulus"          : "2^255-19",
    "base"             : "51",
    "sz"               : "5",
    "bitwidth"         : "64",
    "carry_chains"     : "default",
    "coef_div_modulus" : "2",
    "operations"       : ["femul", "fesquare", "freeze"],
    "compiler"         : "gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes",
}

# curve25519 - c32
{
    "modulus"          : "2^255-19",
    "base"             : "25.5",
    "sz"               : "10",
    "bitwidth"         : "32",
    "carry_chains"     : "default",
    "coef_div_modulus" : "2",
    "operations"       : ["femul", "fesquare", "freeze"],
    "compiler"         : "gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes",
}

'''

import math,json,sys,os,traceback,re,textwrap
from fractions import Fraction

# for montgomery
COMPILER_MONT = "gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing"
COMPILERXX_MONT = "g++ -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -fno-strict-aliasing"
# for solinas
COMPILER_SOLI = "gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes"
COMPILERXX_SOLI = "g++ -march=native -mtune=native -std=gnu++11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes"
CUR_PATH = os.path.dirname(os.path.realpath(__file__))
JSON_DIRECTORY = os.path.join(CUR_PATH, "src/Specific/CurveParameters")
REMAKE_CURVES = os.path.join(JSON_DIRECTORY, 'remake_curves.sh')

class LimbPickingException(Exception): pass
class NonBase2Exception(Exception): pass
class UnexpectedPrimeException(Exception): pass

# given a string representing one term or "tap" in a prime, returns a pair of
# integers representing the weight and coefficient of that tap
#    "2 ^ y" -> [1, y]
#    "x * 2 ^ y" -> [x, y]
#    "x * y" -> [x*y,0]
#    "x" -> [x,0]
def parse_term(t) :
    if "*" not in t and "^" not in t:
        return [int(t),0]

    if "*" in t:
        if len(t.split("*")) > 2: # this occurs when e.g. [w - x * y] has been turned into [w + -1 * x * y]
            a1,a2,b = t.split("*")
            a = int(a1) * int(a2)
        else:
            a,b = t.split("*")
        if "^" not in b:
            return [int(a) * int(b),0]
    else:
        a,b = (1,t)

    b,e = b.split("^")
    if int(b) != 2:
        raise NonBase2Exception("Could not parse term, power with base other than 2: %s" %t)
    return [int(a),int(e)]


# expects prime to be a string and expressed as sum/difference of products of
# two with small coefficients (e.g. '2^448 - 2^224 - 1', '2^255 - 19')
def parse_prime(prime):
    prime = prime.replace("-", "+ -").replace(' ', '').replace('+-2^', '+-1*2^')
    terms = prime.split("+")
    return list(map(parse_term, terms))

# check that the parsed prime makes sense
def sanity_check(p):
    if not all([
        # are there at least 2 terms?
        len(p) > 1,
        # do all terms have 2 elements?
        all(map(lambda t:len(t) == 2, p)),
        # are terms are in order (most to least significant)?
        p == list(sorted(p,reverse=True,key=lambda t:t[1])),
        # does the least significant term have weight 2^0=1?
        p[-1][1] == 0,
        # are all the exponents positive and the coefficients nonzero?
        all(map(lambda t:t[0] != 0 and t[1] >= 0, p)),
        # is second-most-significant term negative?
        p[1][0] < 0,
        # are any exponents repeated?
        len(set(map(lambda t:t[1], p))) == len(p)]) :
        raise UnexpectedPrimeException("Parsed prime %s has unexpected format" %p)


def eval_numexpr(numexpr):
  # copying from https://stackoverflow.com/a/25437733/377022
  numexpr = re.sub(r"\.(?![0-9])", "", numexpr) # purge any instance of '.' not followed by a number
  return eval(numexpr, {'__builtins__':None})

def get_extra_compiler_params(q, base, bitwidth, sz):
    def log_wt(i):
        return int(math.ceil(sum(map(Fraction, map(str.strip, str(base).split('+')))) * i))
    q_int = eval_numexpr(q.replace('^', '**'))
    a24 = 12345 # TODO
    modulus_bytes = (q_int.bit_length()+7)//8
    limb_widths = repr('{%s}' % ','.join(str(int(log_wt(i + 1) - log_wt(i))) for i in range(sz)))
    defs = {
        'q_mpz' : repr(re.sub(r'2(\s*)\^(\s*)([0-9]+)', r'(1_mpz\1<<\2\3)', str(q))),
        'modulus_bytes_val' : repr(str(modulus_bytes)),
        'modulus_array' : repr('{%s}' % ','.join(reversed(list('0x%02x' % ((q_int >> 8*i)&0xff) for i in range(modulus_bytes))))),
        'a_minus_two_over_four_array' : repr('{%s}' % ','.join(reversed(list('0x%02x' % ((a24 >> 8*i)&0xff) for i in range(modulus_bytes))))),
        'limb_t' : 'uint%d_t' % bitwidth,
        'modulus_limbs' : repr(str(sz)),
        'limb_weight_gaps_array' : limb_widths
    }
    return ' ' + ' '.join('-D%s=%s' % (k, v) for k, v in defs.items())

def num_bits(p):
    return p[0][1]

def get_params_montgomery(prime, bitwidth):
    p = parse_prime(prime)
    sanity_check(p)
    sz = int(math.ceil(num_bits(p) / float(bitwidth)))
    return {
            "modulus" : prime,
            "base" : str(bitwidth),
            "sz" : str(sz),
            "montgomery" : True,
            "operations" : ["fenz", "feadd", "femul", "feopp", "fesub"],
            "compiler" : COMPILER_MONT + get_extra_compiler_params(prime, bitwidth, bitwidth, sz),
            "compilerxx" : COMPILERXX_MONT + get_extra_compiler_params(prime, bitwidth, bitwidth, sz)
            }

# given a parsed prime, pick a number of (unsaturated) limbs
def get_num_limbs(p, bitwidth):
    # we want to leave enough bits unused to do a full solinas reduction
    # without carrying; the number of bits necessary is the sum of the bits in
    # the negative coefficients of p (other than the most significant digit)
    unused_bits = sum(map(lambda t: math.ceil(math.log(-t[0], 2)) if t[0] < 0 else 0, p[1:]))
    # print(p,unused_bits)
    min_limbs = int(math.ceil(num_bits(p) / (bitwidth - unused_bits)))
    choices = []
    for n in range(min_limbs, 2 * min_limbs): # don't search past 2x as many limbs as saturated representation; that's just wasteful
        # check that the number of 'extra' bits needed fits in this number of limbs
        min_bits = int(num_bits(p) / n)
        extra = num_bits(p) % n
        if (extra == 0 or n % extra == 0) and min_bits + 1 < bitwidth:
            choices.append((n, num_bits(p) / n))
            break
    if len(choices) == 0:
        raise LimbPickingException("Unable to pick a number of limbs for prime %s and bitwidth %s in range %s-%s limbs" %(p,bitwidth,min_limbs,5*min_limbs))
    # print (p,choices,min_limbs)
    return choices[0][0]

def is_goldilocks(p):
    return p[0][1] == 2 * p[1][1]

def format_base(numerator, denominator):
    if numerator % denominator == 0:
        base = int(numerator / denominator)
    else:
        base = Fraction(numerator=numerator, denominator=denominator)
        if base.denominator in (1, 2, 4, 5, 8, 10):
            base = float(base)
        else:
            base_int, base_frac = int(base), base - int(base)
            base = '%d + %s' % (base_int, str(base_frac))
    return base

# removes latest occurences, preserves order
def remove_duplicates(l):
    seen = []
    for x in l:
        if x not in seen:
            seen.append(x)
    return seen

def get_params_solinas(prime, bitwidth):
    p = parse_prime(prime)
    sanity_check(p)
    sz = get_num_limbs(p, bitwidth)
    base = format_base(num_bits(p), sz)

    # Uncomment to pretty-print primes/bases
    # print("  ".join(map(str, [prime, " "*(35-len(prime)), bitwidth, round(base,1), sz])))

    if len(p) > 2:
        # do interleaved carry chains, starting at where the taps are
        starts = [(int(t[1] / (num_bits(p) / sz)) - 1) % sz for t in p[1:]]
        chain2 = []
        for n in range(1,sz):
            for j in starts:
                chain2.append((j + n) % sz)
        chain2 = remove_duplicates(chain2)
        chain3 = list(map(lambda x:(x+1)%sz,starts))
        carry_chains = [starts,chain2,chain3]
    else:
        carry_chains = "default"
    output = {
            "modulus": prime,
            "base" : str(base),
            "sz" : str(sz),
            "bitwidth" : bitwidth,
            "carry_chains" : carry_chains,
            "coef_div_modulus" : str(2),
            "operations"       : ["femul", "feadd", "fesub", "fesquare", "freeze"],
            "compiler"         : COMPILER_SOLI + get_extra_compiler_params(prime, base, bitwidth, sz),
            "compilerxx"       : COMPILERXX_SOLI + get_extra_compiler_params(prime, base, bitwidth, sz)
            }
    if is_goldilocks(p):
        output["goldilocks"] = True
    return output

def write_if_changed(filename, contents):
    if os.path.isfile(filename):
        with open(filename, 'r') as f:
            old = f.read()
        if old == contents: return
    with open(filename, 'w') as f:
        f.write(contents)

def update_remake_curves(filename):
    with open(REMAKE_CURVES, 'r') as f:
        lines = f.readlines()
    new_line = '${MAKE} "$@" %s ../%s/\n' % (filename, filename[:-len('.json')])
    if new_line in lines: return
    if any(filename in line for line in lines):
        lines = [(line if filename not in line else new_line)
                 for line in lines]
    else:
        lines.append(new_line)
    write_if_changed(REMAKE_CURVES, ''.join(lines))

def format_json(params):
    return json.dumps(params, indent=4, separators=(',', ': '), sort_keys=True) + '\n'


def write_output(name, params):
    prime = params["modulus"]
    filename = (name + "_" + prime + ".json").replace("^","e").replace(" ","").replace("-","m").replace("+","p").replace("*","x")

    write_if_changed(os.path.join(JSON_DIRECTORY, filename),
                     format_json(params))
    update_remake_curves(filename)

def try_write_output(name, get_params, prime, bitwidth):
    try:
        write_output(name, get_params(prime, bitwidth))
    except (LimbPickingException, NonBase2Exception, UnexpectedPrimeException) as e:
        print(e)
    except Exception as e:
        traceback.print_exc()

USAGE = "python generate_parameters.py input_file"
if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(USAGE)
        sys.exit()
    f = open(sys.argv[1])
    for line in f:
        # skip comments and empty lines
        if line.strip().startswith("#") or len(line.strip()) == 0:
            continue
        prime = line.strip().split("#")[0] # remove trailing comments and trailing/leading whitespace
        try_write_output("montgomery32", get_params_montgomery, prime, 32)
        try_write_output("montgomery64", get_params_montgomery, prime, 64)
        try_write_output("solinas32", get_params_solinas, prime, 32)
        try_write_output("solinas64", get_params_solinas, prime, 64)
    f.close()
