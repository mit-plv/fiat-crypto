p256 = 2^256 - 2^224 + 2^192 + 2^96 - 1
F = GF(p256)
a = F(-3)
b = F(41058363725152142129326129780047268409114441015993725554835256314039467401291)
E = EllipticCurve([a, b])
B = E(0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296, 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5)

def orzero(x):
    if not x:
        return "0"
    return x

def hex4(x):
    x = int(x)
    M = int(2^64-1)
    return hex((x>>(3*64))&M) +', '+ hex((x>>(2*64))&M) +', '+ hex((x>>64)&M) +', '+ hex(x&M)

R = 2^256
testcount = [0]
def print_test(J, Z1, A):
    Z1 = F(Z1)
    print ("{")
    print ("uint64_t out[12] = {0};")

    if not J.is_zero():
        X1, Y1 = J.xy()
        X1 = X1 * Z1^2
        Y1 = Y1 * Z1^3
    else:
        X1 = F(32421522)
        Y1 = F(-451234651326)
        Z1 = 0

    if not A.is_zero():
        X2, Y2 = A.xy()
    else:
        X2 = 0
        Y2 = 0

    print ("uint64_t J[12] = {" + hex4(R*X1) +", " + hex4(R*Y1) + ", " + hex4(R*Z1) + "};")
    print ("uint64_t A[8] = {" + hex4(R*X2) +", " + hex4(R*Y2) + "};")
    P = J+A
    if not P.is_zero():
        X3, Y3 = P.xy()
        if not J.is_zero() and not A.is_zero():
            print ("// both nz")
            Z3 = Z1 * (Z1^2*X2 - X1)
        elif not J.is_zero():
            print ("// J nz")
            Z3 = Z1
        else:
            print ("// maybe A nz, maybe neither")
            Z3 = F(1)
        X3 = X3 * Z3^2
        Y3 = Y3 * Z3^3
    else:
        X3 = X1
        Y3 = Y1
        Z3 = 0
    print ("p256_jacobian_add_affine(out, J, A);")
    print ("uint64_t ref[12] = {" + hex4(R*X3) +", " + hex4(R*Y3) + ", " + hex4(R*Z3) + "};")
    testcount[0] = testcount[0] + 1
    print ("if (memcmp(out, ref, sizeof(uint64_t)*12)) return %d;"%testcount[0])
    print ("}")

P = E(0, sqrt(b))

print ("""
#include <string.h>
#include <stdint.h>
#include "p256.h"

int main() {
""")
print_test(B,1, P)
print_test(B,1, -P)
print_test(B,2, P)
print_test(B,2, -P)
print_test(P,2, P)
print_test(P,-1, P)
print_test(-P,1, B)
print_test(-P,-1, B)
print_test(B-B,0, B)
print_test(P,1, B-B)
print_test(P,-1, B-B)
print_test(B,1, B-B)
import random
random.seed(314)
for i in range(200):
    print_test(random.randint(0,100)*B,random.randint(1,100)^random.randint(0,10), random.randint(0,100)*P)
print("""
return 0;
}""")
