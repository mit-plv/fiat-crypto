#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

/* Scalar baselines (compiled from GCC -O2, saved as scalar_baselines.s) */
extern void scalar_add4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void scalar_sub4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void scalar_opp4(uint64_t out[20], const uint64_t a[20]);
extern void scalar_carry4(uint64_t out[20], const uint64_t a[20]);
extern void scalar_carry_add4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void scalar_carry_sub4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void scalar_carry_opp4(uint64_t out[20], const uint64_t a[20]);

/* Limb-parallel XMM asm */
extern void fiat_25519_add_lp(uint64_t out[5], const uint64_t a[5], const uint64_t b[5]);
extern void fiat_25519_sub_lp(uint64_t out[5], const uint64_t a[5], const uint64_t b[5]);

/* Batch AVX2 asm */
extern void fiat_25519_batch_add(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void fiat_25519_batch_sub(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void fiat_25519_batch_opp(uint64_t out[20], const uint64_t a[20]);
extern void fiat_25519_batch_carry(uint64_t out[20], const uint64_t a[20]);
extern void fiat_25519_batch_carry_add(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void fiat_25519_batch_carry_sub(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]);
extern void fiat_25519_batch_carry_opp(uint64_t out[20], const uint64_t a[20]);

#define ITERS 10000000
#define RUNS 10

static inline double now_sec(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec*1e-9; }
static void escape(void *p) { __asm__ volatile("" : : "g"(p) : "memory"); }

/* Wrappers for limb-parallel (call 4 times for 4 elements) */
__attribute__((noinline)) void lp_add4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    fiat_25519_add_lp(out+0,a+0,b+0); fiat_25519_add_lp(out+5,a+5,b+5);
    fiat_25519_add_lp(out+10,a+10,b+10); fiat_25519_add_lp(out+15,a+15,b+15);
}
__attribute__((noinline)) void lp_sub4(uint64_t out[20], const uint64_t a[20], const uint64_t b[20]) {
    fiat_25519_sub_lp(out+0,a+0,b+0); fiat_25519_sub_lp(out+5,a+5,b+5);
    fiat_25519_sub_lp(out+10,a+10,b+10); fiat_25519_sub_lp(out+15,a+15,b+15);
}

typedef struct { double mean; double std; } stats_t;

static stats_t compute_stats(double *samples, int n) {
    double sum = 0;
    for (int i = 0; i < n; i++) sum += samples[i];
    double mean = sum / n;
    double var = 0;
    for (int i = 0; i < n; i++) var += (samples[i] - mean) * (samples[i] - mean);
    var /= n;
    return (stats_t){mean, sqrt(var)};
}

#define MEASURE(samples, call) do { \
    for (int _r = 0; _r < RUNS; _r++) { \
        double _t0 = now_sec(); \
        for (long _i = 0; _i < ITERS; _i++) { call; escape(out); } \
        double _t1 = now_sec(); \
        samples[_r] = (_t1 - _t0) / ITERS * 1e9; \
    } \
} while(0)

int main(void) {
    uint64_t a[20] __attribute__((aligned(32)));
    uint64_t b[20] __attribute__((aligned(32)));
    uint64_t out[20] __attribute__((aligned(32)));
    srand(42);
    for (int i = 0; i < 20; i++) { a[i] = rand() & 0x7ffffffffffffULL; b[i] = rand() & 0x7ffffffffffffULL; }

    double samples[RUNS];
    stats_t s, ref_s;

    printf("=== Native AVX2 Runtime Benchmark ===\n");
    printf("CPU: AMD EPYC 7502P, %d iterations x %d runs\n", ITERS, RUNS);
    printf("Scalar baselines: GCC -O2 assembly (scalar_baselines.s)\n");
    printf("AVX2 programs: hand-written NASM assembly\n\n");
    printf("%-45s %9s %9s %9s\n", "Operation", "mean(ns)", "std(ns)", "speedup");
    printf("--------------------------------------------------------------------------\n");

#define PRINT_REF(label, call) \
    MEASURE(samples, call); \
    ref_s = compute_stats(samples, RUNS); \
    printf("%-45s %8.2f %8.2f\n", label, ref_s.mean, ref_s.std);

#define PRINT_CMP(label, call) \
    MEASURE(samples, call); \
    s = compute_stats(samples, RUNS); \
    printf("%-45s %8.2f %8.2f %8.2fx\n", label, s.mean, s.std, ref_s.mean / s.mean);

    PRINT_REF("add: scalar x86-64 (GCC -O2)", scalar_add4(out,a,b));
    PRINT_CMP("add: limb-parallel XMM (4 calls)", lp_add4(out,a,b));
    PRINT_CMP("add: batch AVX2 YMM (SoA)", fiat_25519_batch_add(out,a,b));
    printf("\n");

    PRINT_REF("sub: scalar x86-64 (GCC -O2)", scalar_sub4(out,a,b));
    PRINT_CMP("sub: limb-parallel XMM (4 calls)", lp_sub4(out,a,b));
    PRINT_CMP("sub: batch AVX2 YMM (AoS contiguous)", fiat_25519_batch_sub(out,a,b));
    printf("\n");

    PRINT_REF("opp: scalar x86-64 (GCC -O2)", scalar_opp4(out,a));
    PRINT_CMP("opp: batch AVX2 YMM (AoS contiguous)", fiat_25519_batch_opp(out,a));
    printf("\n");

    PRINT_REF("carry: scalar x86-64 (GCC -O2)", scalar_carry4(out,a));
    PRINT_CMP("carry: batch AVX2 (AoS gather/scatter)", fiat_25519_batch_carry(out,a));
    printf("\n");

    PRINT_REF("carry_add: scalar x86-64 (GCC -O2)", scalar_carry_add4(out,a,b));
    PRINT_CMP("carry_add: batch AVX2 (AoS gather/scatter)", fiat_25519_batch_carry_add(out,a,b));
    printf("\n");

    PRINT_REF("carry_sub: scalar x86-64 (GCC -O2)", scalar_carry_sub4(out,a,b));
    PRINT_CMP("carry_sub: batch AVX2 (AoS gather/scatter)", fiat_25519_batch_carry_sub(out,a,b));
    printf("\n");

    PRINT_REF("carry_opp: scalar x86-64 (GCC -O2)", scalar_carry_opp4(out,a));
    PRINT_CMP("carry_opp: batch AVX2 (AoS gather/scatter)", fiat_25519_batch_carry_opp(out,a));

    return 0;
}
