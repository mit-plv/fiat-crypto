#!/usr/bin/python3
# The purpose of this file is to assist with reverse-engineering addition
# chains from imperative code. One would find an implementation with a good
# addition chain, translate the code to python (vim macros are your friends),
# and replace the middle section of this file with the addition chain. This
# script prints back-indices in the format that AdditionChainExponentiation.v
# accepts.

values = [1]
chain = []

def mul(x,y):
    i = values.index(x)
    j = values.index(y)
    assert values[i] + values[j] == x+y
    chain.insert(0, (i, j))
    values.insert(0, x+y)
    return x+y

def sqr(x):
    return mul(x,x)

### ==== cut here ==== ###

z = 1
z2 = sqr(z)                   # 2
t1 = sqr(z2)                  # 4
t0 = sqr(t1)                  # 8
z9 = mul(t0, z)               # 9
z11 = mul(z9, z2)             # 11
t0 = sqr(z11)                 # 22
z2_5_0 = mul(t0, z9)          # 2^5 - 2^0 = 31 = 22 + 9

t0 = sqr(z2_5_0)              # 2^6 - 2^1
t1 = sqr(t0)                  # 2^7 - 2^2
t0 = sqr(t1)                  # 2^8 - 2^3
t1 = sqr(t0)                  # 2^9 - 2^4
t0 = sqr(t1)                  # 2^10 - 2^5
z2_10_0 = mul(t0, z2_5_0)     # 2^10 - 2^0

t0 = sqr(z2_10_0)             # 2^11 - 2^1
t1 = sqr(t0)                  # 2^12 - 2^2
for i in range(2, 10, 2):       # 2^20 - 2^10
    t0 = sqr(t1)
    t1 = sqr(t0)
z2_20_0 = mul(t1, z2_10_0)    # 2^20 - 2^0

t0 = sqr(z2_20_0)             # 2^21 - 2^1
t1 = sqr(t0)                  # 2^22 - 2^1
for i in range(2, 20, 2):       # 2^40 - 2^20
    t0 = sqr(t1)
    t1 = sqr(t0)
z2_40_0 = mul(t1, z2_20_0)    # 2^40 - 2^0

t0 = sqr(z2_40_0)             # 2^41 - 2^1
t1 = sqr(t0)                  # 2^42 - 2^2
for i in range(2, 10, 2):       # 2^50 - 2^10
    t0 = sqr(t1)
    t1 = sqr(t0)
z2_50_0 = mul(t1, z2_10_0)    # 2^50 - 2^0

t0 = sqr(z2_50_0)             # 2^51 - 2^1
t1 = sqr(t0)                  # 2^52 - 2^2
for i in range(2, 50, 2):       # 2^100 - 2^50
    t0 = sqr(t1)
    t1 = sqr(t0)
z2_100_0 = mul(t1, z2_50_0)   # 2^100 - 2^0

t0 = sqr(z2_100_0)            # 2^101 - 2^1
t1 = sqr(t0)                  # 2^102 - 2^2
for i in range(2, 100, 2):      # 2^200 - 2^100
    t0 = sqr(t1)
    t1 = sqr(t0)
z2_200_0 = mul(t1, z2_100_0)  # 2^200 - 2^0

t0 = sqr(z2_200_0)            # 2^201 - 2^1
t1 = sqr(t0)                  # 2^202 - 2^2
for i in range(2, 50, 2):       # 2^250 - 2^50
    t0 = sqr(t1)
    t1 = sqr(t0)
t0 = mul(t1, z2_50_0)         # 2^250 - 2^0

t1 = sqr(t0)                  # 2^251 - 2^1
t0 = sqr(t1)                  # 2^252 - 2^2
t1 = sqr(t0)                  # 2^253 - 2^3
t0 = sqr(t1)                  # 2^254 - 2^4
t1 = sqr(t0)                  # 2^255 - 2^5
t0 = mul(t1, z11)             # 2^255 - 21

### ==== cut here ==== ###

print (list(reversed(chain)))
