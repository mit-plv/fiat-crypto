/*
 * Native AVX2 benchmark harness for curve25519 batched operations.
 * Links against assembled .asm files and compares to scalar C baselines.
 *
 * Build:
 *   nasm -f elf64 -o batch_avx_add.o batch_avx_add.asm
 *   nasm -f elf64 -o batch_avx_carry.o batch_avx_carry.asm
 *   nasm -f elf64 -o batch_avx_sub.o batch_avx_sub.asm
 *   nasm -f elf64 -o batch_avx_opp.o batch_avx_opp.asm
 *   gcc -O2 -mavx2 -o bench_avx bench_avx_harness.c batch_avx_add.o batch_avx_carry.o batch_avx_sub.o batch_avx_opp.o
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "gen_scalar_add.c"
#include "gen_scalar_carry.c"
#include "gen_batch_add.c"
#include "gen_batch_carry.c"

/* External: AVX2 assembly functions */
extern void fiat_25519_batch_add(uint64_t out1[20], const uint64_t arg1[20], const uint64_t arg2[20]);
extern void fiat_25519_batch_carry(uint64_t out1[20], const uint64_t arg1[20]);

/* Rename to avoid collision with C versions */
extern void fiat_25519_batch_add(uint64_t*, const uint64_t*, const uint64_t*)
    __asm__("fiat_25519_batch_add");
extern void fiat_25519_batch_carry(uint64_t*, const uint64_t*)
    __asm__("fiat_25519_batch_carry");

/* We call the C versions with _c suffix */
#define batch_add_c fiat_25519_batch_add_c
#define batch_carry_c fiat_25519_batch_carry_c

static inline void batch_add_c(uint64_t out1[20], const uint64_t arg1[20], const uint64_t arg2[20]) {
    fiat_25519_add(out1 + 0,  arg1 + 0,  arg2 + 0);
    fiat_25519_add(out1 + 5,  arg1 + 5,  arg2 + 5);
    fiat_25519_add(out1 + 10, arg1 + 10, arg2 + 10);
    fiat_25519_add(out1 + 15, arg1 + 15, arg2 + 15);
}

static inline void batch_carry_c(uint64_t out1[20], const uint64_t arg1[20]) {
    fiat_25519_carry(out1 + 0,  arg1 + 0);
    fiat_25519_carry(out1 + 5,  arg1 + 5);
    fiat_25519_carry(out1 + 10, arg1 + 10);
    fiat_25519_carry(out1 + 15, arg1 + 15);
}

#define ITERS 50000000

static inline double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void escape(void *p) { __asm__ volatile("" : : "g"(p) : "memory"); }

/* Correctness check: compare AVX output to scalar output */
static int verify_add(const uint64_t a[20], const uint64_t b[20]) {
    uint64_t scalar_out[20], avx_out[20];
    batch_add_c(scalar_out, a, b);
    fiat_25519_batch_add(avx_out, a, b);
    return memcmp(scalar_out, avx_out, sizeof(scalar_out)) == 0;
}

static int verify_carry(const uint64_t a[20]) {
    uint64_t scalar_out[20], avx_out[20];
    batch_carry_c(scalar_out, a);
    fiat_25519_batch_carry(avx_out, a);
    return memcmp(scalar_out, avx_out, sizeof(scalar_out)) == 0;
}

int main(void) {
    uint64_t a[20] __attribute__((aligned(32)));
    uint64_t b[20] __attribute__((aligned(32)));
    uint64_t out[20] __attribute__((aligned(32)));

    srand(42);
    for (int i = 0; i < 20; i++) {
        a[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);
        b[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);
    }

    printf("=== Native AVX2 Benchmark (AMD EPYC) ===\n");
    printf("Iterations: %d\n\n", ITERS);

    /* Correctness checks */
    printf("Correctness: batch_add %s, batch_carry %s\n\n",
           verify_add(a, b) ? "OK" : "MISMATCH",
           verify_carry(a) ? "OK" : "MISMATCH");

    printf("%-30s %10s %10s %10s\n", "Operation", "Time (s)", "ns/call", "Speedup");
    printf("%-30s %10s %10s %10s\n", "---------", "--------", "-------", "-------");

    double t0, t1;

    /* --- ADD --- */
    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        batch_add_c(out, a, b);
        escape(out);
    }
    t1 = now_sec();
    double add_scalar = t1 - t0;
    printf("%-30s %10.3f %10.1f\n", "add (4x scalar C)", add_scalar, add_scalar / ITERS * 1e9);

    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_batch_add(out, a, b);
        escape(out);
    }
    t1 = now_sec();
    double add_avx = t1 - t0;
    printf("%-30s %10.3f %10.1f %9.2fx\n", "batch_add (AVX2 YMM)", add_avx, add_avx / ITERS * 1e9, add_scalar / add_avx);

    /* --- CARRY --- */
    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        batch_carry_c(out, a);
        escape(out);
    }
    t1 = now_sec();
    double carry_scalar = t1 - t0;
    printf("%-30s %10.3f %10.1f\n", "carry (4x scalar C)", carry_scalar, carry_scalar / ITERS * 1e9);

    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_batch_carry(out, a);
        escape(out);
    }
    t1 = now_sec();
    double carry_avx = t1 - t0;
    printf("%-30s %10.3f %10.1f %9.2fx\n", "batch_carry (AVX2 YMM)", carry_avx, carry_avx / ITERS * 1e9, carry_scalar / carry_avx);

    return 0;
}
