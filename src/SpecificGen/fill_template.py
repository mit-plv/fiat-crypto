import os, sys, json

enum = lambda n, s : "(" + ", ".join([s + str(x) for x in range(n)]) + ")"

params = open(sys.argv[1])
replacements = json.load(params)
params.close()
replacements["kmodw"] = replacements["k"] % replacements["w"]
replacements["kdivw"] = int(replacements["k"] / replacements["w"])
replacements["enum f"] = enum(replacements["n"], "f")
replacements["enum g"] = enum(replacements["n"], "g")
replacements["enumw f"] = enum(replacements["kdivw"] + 1, "f")
replacements = {k : str(v) for k,v in replacements.items()}

OUT = "GF" + replacements["k"] + replacements["c"] + "_" + replacements["w"] + ".v"

if len(sys.argv) > 2:
    OUT = sys.argv[2]

if int(replacements["c"]) % 8 == 1:
    TEMPLATE = "GFtemplate3mod4"
else:
    TEMPLATE = "GFtemplate5mod8"

BEGIN_FIELD = "{{{"
END_FIELD = "}}}"
field = lambda s : BEGIN_FIELD + s + END_FIELD

inp = open(TEMPLATE)
out = open(OUT, "w+")

for line in inp:
    new_line = line
    for w in replacements:
        new_line = new_line.replace(field(w), replacements[w])
    out.write(new_line)

inp.close()
out.close()
