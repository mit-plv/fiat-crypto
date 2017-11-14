#!/usr/bin/python3

curves = {}

try:
    while True:
        line = input()
        curve, variant, time = line.split()
        if curve not in curves:
            curves[curve] = {}
        curves[curve][variant] = time
except EOFError:
    pass

for curve, variants in curves.items():
    if 'fiat_solinas64' in variants and 'gmpvar64' in variants:
        print(curve, float(variants['gmpvar64']) / float(variants['fiat_solinas64']))
    if 'fiat_solinas32' in variants and 'gmpvar32' in variants:
        print(curve, float(variants['gmpvar32']) / float(variants['fiat_solinas32']))
