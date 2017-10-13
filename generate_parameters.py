
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
COMPILER = "gcc -fno-peephole2 `#GCC BUG 81300` -march=native -mtune=native -std=gnu11 -O3 -flto -fomit-frame-pointer -fwrapv -Wno-attributes -Wno-incompatible-pointer-types -fno-strict-aliasing"

# given a string representing one term or "tap" in a prime, returns a pair of
# integers representing the weight and coefficient of that tap
#    "2 ^ y" -> [1, y]
#    "x * 2 ^ y" -> [x, y]
#    "x * y" -> [x*y,0]
#    "x" -> [x,0]
def parse_term(t) :
    if "*" not in t and "^" not in t:
        return [int(t),1]
    
    if "*" in t:
        a,b = t.split("*")
        if "^" not in b:
            return [int(a) * int(b),1]
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
    return all([
        # are there at least 2 terms?
        len(p) > 1,
        # do all terms have 2 elements?
        all(map(lambda t:len(t) == 2, p)),
        # are terms are in order (most to least significant)?
        p == list(sorted(p,reverse=True,key=lambda t:t[1])),
        # are all the exponents positive and the coefficients nonzero?
        all(map(lambda t:t[0] != 0 and t[1] > 0, p)),
        # is second-most-significant term negative?
        p[1][0] < 0,
        # are any exponents repeated?
        len(set(map(lambda t:t[1], p))) == len(p)])


def num_bits(p):
    return p[0][1]

def get_params_montgomery(prime, bitwidth):
    p = parse_prime(prime)
    if not sanity_check(p):
        raise Exception("Parsed prime %s has unexpected format (original input: %s)" %(p,prime))
    sz = num_bits(p) / bitwidth 
    return {
            "modulus" : prime,
            "base" : str(bitwidth),
            "sz" : sz,
            "montgomery" : True,
            "operations" : ["fenz", "feadd", "femul", "feopp", "fesub"],
            "compiler" : COMPILER 
            }
