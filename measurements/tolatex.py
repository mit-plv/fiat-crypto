# Generates benchmark graphs in LaTex (following format from the pgfplots
# package)
# 
# This ignores duplicate entries, including different primes with the same
# number of bits.
import sys

USAGE = "USAGE: python tolatex.py [input file]"

SETUPS = {
        "fiat_montgomery32": "color=blue,mark=triangle*", 
        "fiat_montgomery64": "color=blue,mark=square*", 
        "fiat_solinas32": "color=blue,mark=triangle", 
        "fiat_solinas64": "color=blue,mark=square", 
        "gmpvar": "color=red,mark=ball*", 
        "gmpxx": "color=red,mark=o", 
        "gmpsec" : "color=red,mark=*"
        }

class ParseException(Exception): pass

def parse_line(line):
    data = line.strip().split("\t")
    if len(data) != 3 or (data[1] not in SETUPS) or ("2e" not in data[0]) :
        raise ParseException("Could not parse line %s" %line)
    return { 
            "prime" : data[0],
            "setup" : data[1],
            "time" : data[2] }

# remove duplicates, reorganize, and parse number of bits from primes
def clean_data(parsed_lines):
    out = {s:{} for s in SETUPS}
    for ln in parsed_lines:
        nbits = ln["prime"].split("2e")[1].split("m")[0].split("p")[0]
        # if some measurement is duplicated, ignore the repeats
        if nbits not in out[ln["setup"]]:
            out[ln["setup"]][nbits] = ln["time"]
    return out

def makeplot(data):
    out = """
    \\begin{figure*}
    \\begin{tikzpicture}
    \t\\begin{axis}[
    \t\theight=11cm,
    \t\twidth=\\textwidth,
    \t\tgrid=major,
    \t\tlegend pos= north west,
    \t\txlabel=Prime Size (bits),
    \t\tylabel=Time (seconds)]
    """
    for s in SETUPS:
        out +="\t\t\\addplot[%s] coordinates {\n" %SETUPS[s]
        for nbits in data[s]:
            out += "\t\t\t(%s, %s) \n" %(nbits, data[s][nbits])
        out += "\t\t};\n"
        out += "\t\t\\addlegendentry{%s}\n\n" %s.replace("_", "\_")
    out += """
    \t\end{axis}
    \\end{tikzpicture}
    \\end{figure*}
    """
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

