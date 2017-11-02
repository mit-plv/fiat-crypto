#!/usr/bin/env python3
import re, sys

def translate_typename(t):
    return {
            'word8':'uint8_t',
            'word16':'uint16_t',
            'word32':'uint32_t',
            'word64':'uint64_t',
            'word128':'uint128_t',
            'word 8':'uint8_t',
            'word 16':'uint16_t',
            'word 32':'uint32_t',
            'word 64':'uint64_t',
            'word 128':'uint128_t'
            }.get(t,t)

def cleanup_type(t):
    t = t.strip()
    if t.startswith('ReturnType (') and t.endswith(')'):
        t = t[len('ReturnType ('):-len(')')]
    return t

def translate_type(t):
    t = cleanup_type(t)
    fieldtypes = [s.strip() for s in t.split('*')]
    assert len(set(fieldtypes)) == 1
    return translate_typename(fieldtypes[0]), len(fieldtypes)


funcname = sys.argv[1]
_, _, _, binderline, *bodylines, returnline, _, typeline = sys.stdin.read().strip('\n').split('\n')

*arguments, (returntype, returnlength) = [translate_type(s) for s in typeline.lstrip(": ").split('→')]

binders = binderline.replace('λ','').replace('\'', '').replace('(','').replace(')','').replace('%core','').split(',')
binders = [b.strip() for b in binders if b.strip()]

returnline = returnline.strip()
assert returnline.endswith(')') # I don't know why there is an extra paren on that line
returnline = returnline[:-len(')')].strip()
if returnline.startswith('return'):
    returnline = returnline[len('return'):].strip()
if returnline.startswith('(') and returnline.endswith(')'): # but only once... idk why
    returnline = returnline[1:-1].strip()
returneds = returnline.replace('Return','').split(',')
returneds = [r.strip() for r in returneds if r.strip()]

assert (len(binders) == sum(l for (_, l) in arguments))

indent = '  '

outparam = [(returntype, "out", returnlength)]
inparams = [("const "+t, "in%d"%(i+1), l) for (i,(t,l)) in enumerate(arguments)]
print ("static void "+funcname+"(" + ", ".join("%s %s[%d]"%x for x in (outparam+inparams))  + ") {")

braces = 0
for (b, (i, (t, a))) in (list(zip(binders,sum((list(reversed(list(enumerate(l*[(t,n)])))) for (t, n, l) in inparams), [])))):
    print (indent+ "{ %s %s = %s[%d];"%(t, b, a, i))
    braces += 1

mulx_re = re.compile(r'^([^,]*),(\s*)([^ ]*) ([^ ]*)(.*)(mulx.*)\)([; ]*)$'); mulx_sub = r' \3 \4;\2\1\5_\6, &\4)\7'
adc_re = re.compile(r'^([^,]*) ([^, ]*)(\s*),(.*)(addcarryx.*)\)([; ]*)$'); adc_sub = r'\1 \2\3;\4_\5, &\2)\6'
sbb_re = re.compile(r'^([^,]*) ([^, ]*)(\s*),(.*)(subborrow.*)\)([; ]*)$'); sbb_sub = r'\1 \2\3;\4_\5, &\2)\6'
for s in bodylines:
    s = re.sub(mulx_re, mulx_sub, s)
    s = re.sub(adc_re, adc_sub, s)
    s = re.sub(sbb_re, sbb_sub, s)
    print (indent+ "{"+s)
    braces += 1

for (i,r) in enumerate(reversed(returneds)):
    print (indent+ "out[%d] = %s;"%(i, r))

print (indent+'}'*braces)

print ('}')
