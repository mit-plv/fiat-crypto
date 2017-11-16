# Generates benchmark graphs in LaTex (following format from the pgfplots
# package)
import sys, math, re

USAGE = "USAGE: python tolatex.py [input file] {plot32, plot64, table32, table64}"

SETUPS = {
        "gmpvar32": "color=red,mark=o", 
        "gmpxx32": "color=red,mark=x", 
        "gmpsec32" : "color=red,mark=*",
        "gmpvar64": "color=red,mark=o", 
        "gmpxx64": "color=red,mark=x", 
        "gmpsec64" : "color=red,mark=*",
        "fiat_montgomery32": "color=blue,mark=triangle*", 
        "fiat_montgomery64": "color=blue,mark=triangle*", 
        "fiat_solinas32": "color=blue,mark=triangle", 
        "fiat_solinas64": "color=blue,mark=triangle"
        }

# setups to combine and functions to combine them
COMBINE = [
        ("fiat_montgomery32", "fiat_solinas32", min),
        ("fiat_montgomery64", "fiat_solinas64", min)
        ]

# setups to exclude
EXCLUDE_32 = [
        "fiat_montgomery64",
        "fiat_solinas64",
        "gmpvar64",
        "gmpsec64",
        "gmpxx64",
        "gmpxx32"
        ]
EXCLUDE_64 = [
        "fiat_montgomery32",
        "fiat_solinas32",
        "gmpvar32",
        "gmpsec32",
        "gmpxx64",
        "gmpxx32"
        ]

LEGEND = {
        "fiat_montgomery32": "this paper", 
        "fiat_montgomery64": "this paper", 
        "fiat_solinas32": "this paper", 
        "fiat_solinas64": "this paper", 
        "gmpvar32": "GMP mpn API", 
        "gmpxx32": "GMP C++ API", 
        "gmpsec32" : "GMP mpn_sec API",
        "gmpvar64": "GMP mpn API",
        "gmpxx64": "GMP C++ API", 
        "gmpsec64" : "GMP mpn_sec API"
        }

class ParseException(Exception): pass
class MissingDataException(Exception): pass

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
        raise ParseException("Could not parse term, power with base other than 2: %s" %t)
    return [int(a),int(e)]

# expects prime to be a string and expressed as sum/difference of products of
# two with small coefficients (e.g. '2^448 - 2^224 - 1', '2^255 - 19')
# returns tuple (string representation, numeric value)
def parse_prime(prime):
    rep = prime.replace("e", "^").replace("m", "-").replace("p","+").replace("x","*")
    terms = rep.replace("-", "+ -").replace(' ', '').replace('+-2^', '+-1*2^').split("+")
    value = sum([(x * (2**e)) for x,e in map(parse_term, terms)])
    return (rep, value)

def parse_line(line):
    data = line.strip().split("\t")
    if len(data) != 3 or (data[1] not in SETUPS) or ("2e" not in data[0]) :
        raise ParseException("Could not parse line %s" %line.strip())
    return { 
            "prime" : data[0],
            "setup" : data[1],
            "time" : data[2] }

def final_lines(bits):
    out = []
    for s in SETUPS:
        if (bits == 32 and s in EXCLUDE_32) or (bits == 64 and s in EXCLUDE_64):
            continue
        if any([x[1]==s for x in COMBINE]):
            continue # in this case, the setup has been combined into some other one
        out.append(s)
    return out 

# check for missing data points
def check_missing(data, bits):
    all_primes = set()
    for s in final_lines(bits):
        all_primes = all_primes | set(data[s].keys())
    missing = []
    for s in final_lines(bits):
        x = all_primes ^ set(data[s].keys())
        if len(x) != 0:
            missing.append((s, x))
    if len(missing) > 0:
        message = "\n".join(["missing datapoints in %s: primes are %s" %(LEGEND[s],list(map(lambda t:t[0], x))) for s,x in missing])
        print("WARNING: %s" %message)
        #raise MissingDataException(message) 

# remove duplicates, reorganize, and parse primes
def clean_plot_data(parsed_lines, bits):
    out = {s:{} for s in SETUPS}
    for ln in parsed_lines:
        p = parse_prime(ln["prime"])
        # if some measurement is duplicated, ignore the repeats
        if p not in out[ln["setup"]]:
            out[ln["setup"]][p] = ln["time"]
    # combine setups according to COMBINE list
    for s1, s2, f in COMBINE:
        all_primes = list(out[s1].keys())
        all_primes.extend(out[s2].keys())
        for p in set(all_primes):
            if p in out[s1] and p in out[s2]:
                out[s1][p] = f(out[s1][p], out[s2][p])
            elif p in out[s2]:
                out[s1][p] = out[s2][p]
    check_missing(out, bits)
    return out

# remove duplicates, reorganize, and parse primes
def clean_table_data(parsed_lines):
    all_primes = set([ln["prime"] for ln in parsed_lines])
    out = {p:{} for p in all_primes}
    for ln in parsed_lines:
        # ignore duplicates
        if ln["setup"] not in out[ln["prime"]]:
            out[ln["prime"]][ln["setup"]] = ln["time"]
    return out

def maketable(data, bits):
    if bits == 64:
        out="""\\tablehead{%
  \\hline
  & \\multicolumn{2}{c|}{\\textbf{Our Code}} & \\multicolumn{3}{c|}{\\textbf{GMP Code}} & \\\\
  \\cline{2-6}
  \\textbf{Prime} & \\textbf{Sol.} & \\textbf{Mont.} & \\textbf{const time} & \\textbf{var time} & \\textbf{C++} & \\textbf{Speedup} \\\\ \\hline}
\\footnotesize
\\begin{xtabular}{|l|p{0.6cm}|p{0.6cm}|p{0.6cm}|p{0.6cm}|p{0.6cm}|p{0.6cm}|}\n"""
    else:
        out="""\\tablehead{%
  \\hline
  & \\textbf{Our Code} & \\multicolumn{2}{c|}{\\textbf{GMP Code}} & \\\\
  \\cline{2-5}
  \\textbf{Prime} & \\textbf{Solinas} & \\textbf{const time} & \\textbf{var time} & \\textbf{Speedup} \\\\ \\hline}
\\footnotesize
\\begin{xtabular}{|l|p{0.8cm}|p{0.8cm}|p{0.8cm}|p{0.9cm}|}\n"""

    cols_64 = ["fiat_solinas64", "fiat_montgomery64", "gmpsec64", "gmpvar64", "gmpxx64"]
    cols_32 = ["fiat_solinas32", "gmpsec32", "gmpvar32"]
    cols = cols_64 if bits == 64 else cols_32

    for p in sorted(data.keys()):
        prime_latex= re.sub("2\^[0-9]+", lambda matchobj : "2^{%s}" %matchobj.group(0)[2:], parse_prime(p)[0])
        prime_latex= re.sub("[0-9]\*[0-9]", lambda matchobj : "%s\cdot %s" %(matchobj.group(0)[0], matchobj.group(0)[2]), prime_latex)
        row = ["$" + prime_latex + "$"]
        our_best = None
        gmp_best = None
        for s in cols: 
            if s in data[p]:
                row.append(data[p][s])
                if "fiat" in s and (our_best == None or float(data[p][s]) < our_best):
                    our_best = float(data[p][s])
                if "gmp" in s and (gmp_best == None or float(data[p][s]) < gmp_best):
                    gmp_best = float(data[p][s])
            else:
                row.append("-")
        if our_best != None and gmp_best != None:
            row.append(str(round(1 - our_best/gmp_best, 2)))
        else:
            row.append("-")
        out += ("\t" + " & ".join(row) + " \\\\ \n")

    out +="""\\hline\n\\end{xtabular}""" 
    return out

def makeplot(data, bits):
    out = """
 \\begin{figure*}
 \\begin{tikzpicture}
 \t\\begin{axis}[
 \t\theight=3.4cm,
 \t\ttitle style={font=\small},
 \t\ttitle=%s-Bit Field Arithmetic Benchmarks,
 \t\twidth=\\textwidth,
 \t\tlegend pos= north west,
 \t\txtick distance=64,
 \t\tlegend style={font=\\tiny},
 \t\tlabel style={font=\\footnotesize},
 \t\txlabel style={at={(0.5,0.1)}, anchor=north},
 \t\tlegend columns=2,
 \t\ttick label style={font=\\footnotesize},
 \t\tgrid=major,
 \t\tymin=0,
 \t\txlabel=log2(prime),
 \t\tylabel=Time (seconds)]\n""" %bits
    for s in final_lines(bits):
        out +="\t\t\\addplot[%s,mark size=2pt] coordinates {\n" %SETUPS[s]
        for p,t in sorted(data[s].items()):
            out += "\t\t\t(%s, %s) \n" %(math.log2(p[1]), t)
        out += "\t\t};\n"
        out += "\t\t\\addlegendentry{%s}\n\n" %LEGEND[s].replace("_", "\_")
    out += "\t\end{axis}\n\\end{tikzpicture}\n\\end{figure*}"
    return out

if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[2] not in ["plot32", "plot64", "table32", "table64"]:
        print(USAGE)
        sys.exit()
    f = open(sys.argv[1])
    parsed_lines = []
    for line in f:
        try:
            parsed_lines.append(parse_line(line))
        except ParseException:
            print("WARNING: Could not parse line %s, skipping" %line.strip().split("\t"))
    f.close()

    if sys.argv[2] == "table32":
        print(maketable(clean_table_data(parsed_lines), 32))
    if sys.argv[2] == "table64":
        print(maketable(clean_table_data(parsed_lines), 64))
    elif sys.argv[2] == "plot32":
        print(makeplot(clean_plot_data(parsed_lines, 32), 32))
    elif sys.argv[2] == "plot64":
        print(makeplot(clean_plot_data(parsed_lines, 64), 64))

