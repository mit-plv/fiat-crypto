# Generates benchmark graphs in LaTex (following format from the pgfplots
# package)
# 
# This ignores duplicate entries, including different primes with the same
# number of bits.
import sys, math

USAGE = "USAGE: python tolatex.py [input file]"

SETUPS = {
        "fiat_montgomery32": "color=blue,mark=triangle*", 
        "fiat_montgomery64": "color=blue,mark=square*", 
        "fiat_solinas32": "color=blue,mark=triangle", 
        "fiat_solinas64": "color=blue,mark=square", 
        "gmpvar": "color=red,mark=*", 
        "gmpxx": "color=red,mark=o", 
        "gmpsec" : "color=red,mark=x"
        }

LEGEND = {
        "fiat_montgomery32": "ours, Montgomery reduction", 
        "fiat_montgomery64": "ours, Montgomery reduction", 
        "fiat_solinas32": "ours, Solinas reduction", 
        "fiat_solinas64": "ours, Solinas reduction", 
        "gmpvar": "GMP mpn_ API", 
        "gmpxx": "GMP C++ API", 
        "gmpsec" : "GMP mpn_sec API"
        }

EXCLUDE = [
        "fiat_montgomery32",
        "fiat_solinas32"
        ]

class ParseException(Exception): pass

def parse_line(line):
    data = line.strip().split("\t")
    if len(data) != 3 or (data[1] not in SETUPS) or ("2e" not in data[0]) :
        raise ParseException("Could not parse line %s" %line)
    return { 
            "prime" : data[0],
            "setup" : data[1],
            "time" : data[2] }

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

# remove duplicates, reorganize, and parse primes
def clean_data(parsed_lines):
    out = {s:{} for s in SETUPS}
    for ln in parsed_lines:
        prime2 = ln["prime"].replace("e", "^").replace("m", "-").replace("p","+").replace("x","*")
        p = sum([(x * (2**e)) for x,e in parse_prime(prime2)])
        n = math.log2(p)
        # if some measurement is duplicated, ignore the repeats
        if n not in out[ln["setup"]]:
            out[ln["setup"]][n] = ln["time"]
    return out

def makeplot(data):
    out = """
 \\begin{figure*}
 \\begin{tikzpicture}
 \t\\begin{axis}[
 \t\theight=9cm,
 \t\twidth=\\textwidth,
 \t\tlegend pos= north west,
 \t\txtick distance=100,
 \t\textra x ticks={127,256,448,480},
 \t\textra x tick style={grid=major, tick label style={rotate=45,anchor=east}},
 \t\tymin=0,
 \t\txlabel=log2(prime),
 \t\tylabel=Time (seconds)]"""
    for s in SETUPS:
        if s in EXCLUDE:
            continue
        out +="\t\t\\addplot[%s] coordinates {\n" %SETUPS[s]
        for n in data[s]:
            out += "\t\t\t(%s, %s) \n" %(n, data[s][n])
        out += "\t\t};\n"
        out += "\t\t\\addlegendentry{%s}\n\n" %LEGEND[s].replace("_", "\_")
    out += "\t\end{axis}\n\\end{tikzpicture}\n\\end{figure*}"
    return out

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(USAGE)
        sys.exit()
    f = open(sys.argv[1])
    parsed_lines = []
    for line in f:
        try:
            parsed_lines.append(parse_line(line))
        except ParseException:
            print("WARNING: Could not parse line %s, skipping" %line)
    f.close()
    print(makeplot(clean_data(parsed_lines)))

