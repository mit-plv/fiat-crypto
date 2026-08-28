/*
 * Runtime benchmark: scalar (called 4x) vs batched C code for curve25519 ops.
 *
 * This benchmarks the *C-level* batched code (not the AVX assembly) to show
 * the baseline overhead of batching at the algorithmic level. The AVX assembly
 * would be faster still due to SIMD parallelism on the actual hardware.
 *
 * Build:
 *   # First generate the C files (from repo root):
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' add -o test-avx/gen_scalar_add.c
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' carry --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 \
 *     -o test-avx/gen_scalar_carry.c
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' carry_mul --no-wide-int --shiftr-avoid-uint1 \
 *     --tight-bounds-mul-by 1.000001 -o test-avx/gen_scalar_carry_mul.c
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' batch_add -o test-avx/gen_batch_add.c
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' batch_carry --shiftr-avoid-uint1 \
 *     --tight-bounds-mul-by 1.000001 -o test-avx/gen_batch_carry.c
 *   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
 *     25519 64 '(auto)' '2^255 - 19' batch_carry_mul --no-wide-int --shiftr-avoid-uint1 \
 *     --tight-bounds-mul-by 1.000001 -o test-avx/gen_batch_carry_mul.c
 *
 *   # Then compile:
 *   cc -O2 -o test-avx/bench_runtime test-avx/bench_runtime.c
 */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Pull in generated code */
#include "gen_scalar_add.c"
#include "gen_scalar_carry.c"
#include "gen_scalar_carry_mul.c"
#include "gen_batch_add.c"
#include "gen_batch_carry.c"

/* batch_carry_mul shares helper functions with scalar_carry_mul; rename them */
#define fiat_25519_addcarryx_u64 batch_fiat_25519_addcarryx_u64
#define fiat_25519_subborrowx_u64 batch_fiat_25519_subborrowx_u64
#define fiat_25519_mulx_u64 batch_fiat_25519_mulx_u64
#define fiat_25519_uint1 batch_fiat_25519_uint1
#define fiat_25519_int1 batch_fiat_25519_int1
#include "gen_batch_carry_mul.c"
#undef fiat_25519_addcarryx_u64
#undef fiat_25519_subborrowx_u64
#undef fiat_25519_mulx_u64
#undef fiat_25519_uint1
#undef fiat_25519_int1

#define BATCH_SIZE 4
#define LIMBS 5
#define ITERS 10000000

static inline double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Prevent the compiler from optimizing away results */
static void escape(void *p) {
    __asm__ volatile("" : : "g"(p) : "memory");
}

int main(void) {
    /* Initialize inputs with pseudo-random data in tight bounds */
    uint64_t a[20], b[20], out[20];
    srand(42);
    for (int i = 0; i < 20; i++) {
        a[i] = ((uint64_t)rand() & 0x7ffffffffffffULL); /* 51-bit values */
        b[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);
    }

    double t0, t1;
    long iters = ITERS;

    printf("Benchmark: curve25519 operations, %ld iterations\n", iters);
    printf("Each 'batch' processes %d independent field elements\n\n", BATCH_SIZE);
    printf("%-30s %12s %12s %10s\n", "Operation", "Time (s)", "ns/call", "Speedup");
    printf("%-30s %12s %12s %10s\n", "---------", "--------", "-------", "-------");

    /* --- ADD --- */
    /* Scalar: call add 4 times */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_add((uint64_t*)out + 0,  (uint64_t*)a + 0,  (uint64_t*)b + 0);
        fiat_25519_add((uint64_t*)out + 5,  (uint64_t*)a + 5,  (uint64_t*)b + 5);
        fiat_25519_add((uint64_t*)out + 10, (uint64_t*)a + 10, (uint64_t*)b + 10);
        fiat_25519_add((uint64_t*)out + 15, (uint64_t*)a + 15, (uint64_t*)b + 15);
        escape(out);
    }
    t1 = now_sec();
    double add_scalar = t1 - t0;
    printf("%-30s %12.3f %12.1f\n", "add (4x scalar)", add_scalar, add_scalar / iters * 1e9);

    /* Batch add */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_batch_add(out, a, b);
        escape(out);
    }
    t1 = now_sec();
    double add_batch = t1 - t0;
    printf("%-30s %12.3f %12.1f %9.2fx\n", "batch_add", add_batch, add_batch / iters * 1e9, add_scalar / add_batch);

    /* --- CARRY --- */
    /* Scalar carry 4x */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_carry((uint64_t*)out + 0,  (uint64_t*)a + 0);
        fiat_25519_carry((uint64_t*)out + 5,  (uint64_t*)a + 5);
        fiat_25519_carry((uint64_t*)out + 10, (uint64_t*)a + 10);
        fiat_25519_carry((uint64_t*)out + 15, (uint64_t*)a + 15);
        escape(out);
    }
    t1 = now_sec();
    double carry_scalar = t1 - t0;
    printf("%-30s %12.3f %12.1f\n", "carry (4x scalar)", carry_scalar, carry_scalar / iters * 1e9);

    /* Batch carry */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_batch_carry(out, a);
        escape(out);
    }
    t1 = now_sec();
    double carry_batch = t1 - t0;
    printf("%-30s %12.3f %12.1f %9.2fx\n", "batch_carry", carry_batch, carry_batch / iters * 1e9, carry_scalar / carry_batch);

    /* --- CARRY_MUL --- */
    /* Scalar carry_mul 4x */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_carry_mul((uint64_t*)out + 0,  (uint64_t*)a + 0,  (uint64_t*)b + 0);
        fiat_25519_carry_mul((uint64_t*)out + 5,  (uint64_t*)a + 5,  (uint64_t*)b + 5);
        fiat_25519_carry_mul((uint64_t*)out + 10, (uint64_t*)a + 10, (uint64_t*)b + 10);
        fiat_25519_carry_mul((uint64_t*)out + 15, (uint64_t*)a + 15, (uint64_t*)b + 15);
        escape(out);
    }
    t1 = now_sec();
    double mul_scalar = t1 - t0;
    printf("%-30s %12.3f %12.1f\n", "carry_mul (4x scalar)", mul_scalar, mul_scalar / iters * 1e9);

    /* Batch carry_mul */
    t0 = now_sec();
    for (long i = 0; i < iters; i++) {
        fiat_25519_batch_carry_mul(out, a, b);
        escape(out);
    }
    t1 = now_sec();
    double mul_batch = t1 - t0;
    printf("%-30s %12.3f %12.1f %9.2fx\n", "batch_carry_mul", mul_batch, mul_batch / iters * 1e9, mul_scalar / mul_batch);

    return 0;
}
