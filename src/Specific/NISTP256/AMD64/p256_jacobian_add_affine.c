#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"
#include "p256.h"
#include "feadd.h"
#include "fesub.h"
#include "feopp.h"
#include "femul.h"
#include "fenz.h"

#undef force_inline
#define force_inline __attribute__((always_inline))

static inline void force_inline fesquare(uint64_t o[4], uint64_t a, uint64_t b, uint64_t c, uint64_t d) {
  femul(o,
        a, b, c, d,
        a, b, c, d);
}

static uint64_t Rmodm[4] = {0xfffffffe, 0xffffffffffffffff, 0xffffffff00000000, 0x0000000000000001};

void p256_jacobian_add_affine(
    uint64_t P3[12],
    uint64_t P1[12],
    uint64_t P2[8]
) {
    uint64_t* X1 = P1;
    uint64_t* Y1 = P1+4;
    uint64_t* Z1 = P1+8;
    uint64_t* X2 = P2;
    uint64_t* Y2 = P2+4;
    uint64_t* X3 = P3;
    uint64_t* Y3 = P3+4;
    uint64_t* Z3 = P3+8;
    uint64_t ZZ[4] = {0};  fesquare(ZZ, Z1[0], Z1[1], Z1[2], Z1[3]);
    uint64_t P1nz = 0;  fenz(&P1nz, Z1[0], Z1[1], Z1[2], Z1[3]);
    uint64_t U2[4] = {0};  femul(U2, ZZ[0], ZZ[1], ZZ[2], ZZ[3], X2[0], X2[1], X2[2], X2[3]);
    uint64_t X2nz = 0;  fenz(&X2nz, X2[0], X2[1], X2[2], X2[3]);
    uint64_t ZZZ[4] = {0};  femul(ZZZ, ZZ[0], ZZ[1], ZZ[2], ZZ[3], Z1[0], Z1[1], Z1[2], Z1[3]);
    uint64_t H[4] = {0};  fesub(H, U2[0], U2[1], U2[2], U2[3], X1[0], X1[1], X1[2], X1[3]);
                           femul(Z3, Z1[0], Z1[1], Z1[2], Z1[3], H[0], H[1], H[2], H[3]);
    uint64_t Y2nz = 0;  fenz(&Y2nz, Y2[0], Y2[1], Y2[2], Y2[3]);
    uint64_t P2nz = X2nz | Y2nz;
    uint64_t S2[4] = {0};  femul(S2, ZZZ[0], ZZZ[1], ZZZ[2], ZZZ[3], Y2[0], Y2[1], Y2[2], Y2[3]);
    uint64_t R[4] = {0};  fesub(R, S2[0], S2[1], S2[2], S2[3], Y1[0], Y1[1], Y1[2], Y1[3]);
    uint64_t HH[4] = {0};  fesquare(HH, H[0], H[1], H[2], H[3]);
    uint64_t RR[4] = {0};  fesquare(RR, R[0], R[1], R[2], R[3]);
    uint64_t HHH[4] = {0};  femul(HHH, HH[0], HH[1], HH[2], HH[3], H[0], H[1], H[2], H[3]);
    Z3[3] = cmovznz(P1nz,  Rmodm[3],  Z3[3]);
    Z3[2] = cmovznz(P1nz,  Rmodm[2],  Z3[2]);
    Z3[1] = cmovznz(P1nz,  Rmodm[1],  Z3[1]);
    Z3[0] = cmovznz(P1nz,  Rmodm[0],  Z3[0]);
    Z3[3] = cmovznz(P2nz,  Z1[3],  Z3[3]);
    Z3[2] = cmovznz(P2nz,  Z1[2],  Z3[2]);
    Z3[1] = cmovznz(P2nz,  Z1[1],  Z3[1]);
    Z3[0] = cmovznz(P2nz,  Z1[0],  Z3[0]);
    uint64_t HHX[4] = {0};  femul(HHX, HH[0], HH[1], HH[2], HH[3], X1[0], X1[1], X1[2], X1[3]);
    uint64_t T10[4] = {0};  feadd(T10, HHX[0], HHX[1], HHX[2], HHX[3], HHX[0], HHX[1], HHX[2], HHX[3]);
    uint64_t E4[4] = {0};  fesub(E4, RR[0], RR[1], RR[2], RR[3], T10[0], T10[1], T10[2], T10[3]);
                           fesub(X3, E4[0], E4[1], E4[2], E4[3], HHH[0], HHH[1], HHH[2], HHH[3]);
    X3[3] = cmovznz(P1nz,  X2[3],  X3[3]);
    X3[2] = cmovznz(P1nz,  X2[2],  X3[2]);
    X3[1] = cmovznz(P1nz,  X2[1],  X3[1]);
    X3[0] = cmovznz(P1nz,  X2[0],  X3[0]);
    X3[3] = cmovznz(P2nz,  X1[3],  X3[3]);
    X3[2] = cmovznz(P2nz,  X1[2],  X3[2]);
    X3[1] = cmovznz(P2nz,  X1[1],  X3[1]);
    X3[0] = cmovznz(P2nz,  X1[0],  X3[0]);
    uint64_t T13[4] = {0}; femul(T13, HHH[0], HHH[1], HHH[2], HHH[3], Y1[0], Y1[1], Y1[2], Y1[3]);
    uint64_t T11[4] = {0}; fesub(T11, HHX[0], HHX[1], HHX[2], HHX[3], X3[0], X3[1], X3[2], X3[3]);
    uint64_t T12[4] = {0}; femul(T12, T11[0], T11[1], T11[2], T11[3], R[0], R[1], R[2], R[3]);
                           fesub(Y3, T12[0], T12[1], T12[2], T12[3], T13[0], T13[1], T13[2], T13[3]);
    Y3[3] = cmovznz(P1nz,  Y2[3],  Y3[3]);
    Y3[2] = cmovznz(P1nz,  Y2[2],  Y3[2]);
    Y3[1] = cmovznz(P1nz,  Y2[1],  Y3[1]);
    Y3[0] = cmovznz(P1nz,  Y2[0],  Y3[0]);
    Y3[3] = cmovznz(P2nz,  Y1[3],  Y3[3]);
    Y3[2] = cmovznz(P2nz,  Y1[2],  Y3[2]);
    Y3[1] = cmovznz(P2nz,  Y1[1],  Y3[1]);
    Y3[0] = cmovznz(P2nz,  Y1[0],  Y3[0]);
}
