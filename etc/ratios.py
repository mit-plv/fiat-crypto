#!/usr/bin/python3

curves = {}

try:
    while True:
        line = input()
        curve, variant, time = line.split()
        if curve not in curves:
            curves[curve] = {}
        curves[curve][variant] = float(time)
except EOFError:
    pass

for curve, variants in curves.items():
    def compare(fiat, other):
        if fiat in variants and other in variants:
            print(curve, variants[other] / variants[fiat])

    compare('fiat_solinas64', 'gmpvar64')
    compare('fiat_solinas32', 'gmpvar32')
    compare('fiat_montgomery64', 'gmpvar64')
    compare('fiat_montgomery32', 'gmpvar32')
