
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

import math,json,sys

# for montgomery
COMPILER_MONT = "gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing"
# for solinas
COMPILER_SOLI = "gcc -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes"

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
        a,b = t.split("*")
        if "^" not in b:
            return [int(a) * int(b),0]
    else:
        a,b = (1,t)
    
    b,e = b.split("^")
    if int(b) != 2:
        raise Exception("Could not parse term, power with base other than 2: %s" %t)
    return [int(a),int(e)]


# expects prime to be a string and expressed as sum/difference of products of
# two with small coefficients (e.g. '2^448 - 2^224 - 1', '2^255 - 19') 
def parse_prime(prime):
    terms = prime.replace("-", "+ -1 *").split("+")
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
        raise Exception("Parsed prime %s has unexpected format" %p)


def num_bits(p):
    return p[0][1]

def get_params_montgomery(prime, bitwidth):
    p = parse_prime(prime)
    sanity_check(p)
    sz = math.ceil(num_bits(p) / bitwidth)
    return {
            "modulus" : prime,
            "base" : str(bitwidth),
            "sz" : str(sz),
            "montgomery" : True,
            "operations" : ["fenz", "feadd", "femul", "feopp", "fesub"],
            "compiler" : COMPILER_MONT
            }

# given a parsed prime, pick a number of (unsaturated) limbs
def get_num_limbs(p, bitwidth):
    # we want to leave enough bits unused to do a full solinas reduction
    # without carrying; the number of bits necessary is the sum of the bits in
    # the negative coefficients of p (other than the most significant digit)
    unused_bits = sum(map(lambda t: math.ceil(math.log2(-t[0])) if t[0] < 0 else 0, p[1:]))
    # print(p,unused_bits)
    min_limbs = math.ceil(num_bits(p) / (bitwidth - unused_bits)) + 1
    choices = []
    for n in range(min_limbs, 5 * min_limbs): # don't search past 5x as many limbs as saturated representation; that's just wasteful
        # check that the number of 'extra' bits needed fits in this number of limbs
        min_bits = int(num_bits(p) / n)
        extra = num_bits(p) % n
        if extra == 0 or n % extra == 0:
            choices.append((n, num_bits(p) / n))
            break
    if len(choices) == 0:
        raise Exception("Unable to pick a number of limbs for prime %s and bitwidth %s in range %s-%s limbs" %(p,bitwidth,min_limbs,5*min_limbs))
    # print (p,choices)
    return choices[0][0]

def is_goldilocks(p):
    return p[0][1] == 2 * p[1][1]

def get_params_solinas(prime, bitwidth):
    p = parse_prime(prime)
    sanity_check(p)
    sz = get_num_limbs(p, bitwidth)
    base = num_bits(p) / sz
    output = {
            "modulus": prime,
            "base" : str(base),
            "sz" : str(sz),
            "bitwidth" : bitwidth,
            "carry_chains" : "default",
            "coef_div_modulus" : str(2),
            "operations"       : ["femul", "fesquare", "freeze"],
            "compiler"         : COMPILER_SOLI
            }
    if is_goldilocks(p):
        output["goldilocks"] = True
    return output

def write_output(name, params):
    prime = params["modulus"]
    filename = (name + "_" + prime + ".json").replace("^","e").replace(" ","").replace("-","m").replace("+","p").replace("*","x")
    g = open(filename,"w")
    g.write(json.dumps(params))
    g.close()

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
        try:
            write_output("montgomery32", get_params_montgomery(prime, 32))
        except Exception as e:
            print(e)
        try:
            write_output("montgomery64", get_params_montgomery(prime, 64))
        except Exception as e:
            print(e)
        try:
            write_output("solinas32", get_params_solinas(prime, 32))
        except Exception as e:
            print(e)
        try:
            write_output("solinas64", get_params_solinas(prime, 64))
        except Exception as e:
            print(e)

    f.close()
