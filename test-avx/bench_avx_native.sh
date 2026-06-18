#!/bin/bash
# Native AVX2 runtime benchmark (requires x86-64 Linux with AVX2 support)
# Assembles and benchmarks the vectorized .asm files against scalar C baselines.
#
# Usage: ./test-avx/bench_avx_native.sh
# Prerequisites: nasm, gcc, an x86-64 CPU with AVX2

set -e

if [ "$(uname -m)" != "x86_64" ]; then
    echo "ERROR: This benchmark requires x86-64 hardware (you have $(uname -m))" >&2
    exit 1
fi

if ! command -v nasm >/dev/null; then
    echo "ERROR: nasm not found" >&2
    exit 1
fi

TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

ITERS=10000000

echo "=== Native AVX2 Benchmark ==="
echo "Iterations: $ITERS"
echo ""

# --- Benchmark batch_add: AVX YMM vs scalar 4x ---

# Assemble the AVX batch_add
nasm -f elf64 -o "$TMPDIR/batch_avx_add.o" test-avx/batch_avx_add.asm

# Generate scalar add C code
src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' add \
    -o "$TMPDIR/scalar_add.c" 2>/dev/null

# Write the benchmark harness
cat > "$TMPDIR/bench_add.c" << 'HARNESS'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

#include "scalar_add.c"

/* External: the AVX batch_add function */
extern void fiat_25519_batch_add(uint64_t out1[20], const uint64_t arg1[20], const uint64_t arg2[20]);

#define ITERS 10000000

static inline double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void escape(void *p) { __asm__ volatile("" : : "g"(p) : "memory"); }

int main(void) {
    uint64_t a[20], b[20], out[20];
    srand(42);
    for (int i = 0; i < 20; i++) {
        a[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);
        b[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);
    }

    double t0, t1;

    /* Scalar: 4x add */
    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_add(out + 0, a + 0, b + 0);
        fiat_25519_add(out + 5, a + 5, b + 5);
        fiat_25519_add(out + 10, a + 10, b + 10);
        fiat_25519_add(out + 15, a + 15, b + 15);
        escape(out);
    }
    t1 = now_sec();
    double scalar = t1 - t0;
    printf("4x scalar add:     %.3fs (%.1f ns/call)\n", scalar, scalar / ITERS * 1e9);

    /* AVX batch_add */
    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_batch_add(out, a, b);
        escape(out);
    }
    t1 = now_sec();
    double avx = t1 - t0;
    printf("AVX batch_add:     %.3fs (%.1f ns/call)\n", avx, avx / ITERS * 1e9);
    printf("Speedup:           %.2fx\n", scalar / avx);

    return 0;
}
HARNESS

gcc -O2 -mavx2 -o "$TMPDIR/bench_add" "$TMPDIR/bench_add.c" "$TMPDIR/batch_avx_add.o" -I"$TMPDIR"
echo "--- batch_add (AVX YMM vs 4x scalar) ---"
"$TMPDIR/bench_add"
echo ""

# --- Benchmark batch_carry: AVX gather/SIMD-carry vs scalar 4x ---

nasm -f elf64 -o "$TMPDIR/batch_avx_carry.o" test-avx/batch_avx_carry.asm

src/ExtractionOCaml/unsaturated_solinas --inline --static 25519 64 '(auto)' '2^255 - 19' carry \
    --shiftr-avoid-uint1 --tight-bounds-mul-by 1.000001 \
    -o "$TMPDIR/scalar_carry.c" 2>/dev/null

cat > "$TMPDIR/bench_carry.c" << 'HARNESS'
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>

#include "scalar_carry.c"

extern void fiat_25519_batch_carry(uint64_t out1[20], const uint64_t arg1[20]);

#define ITERS 10000000

static inline double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void escape(void *p) { __asm__ volatile("" : : "g"(p) : "memory"); }

int main(void) {
    uint64_t a[20], out[20];
    srand(42);
    for (int i = 0; i < 20; i++)
        a[i] = ((uint64_t)rand() & 0x7ffffffffffffULL);

    double t0, t1;

    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_carry(out + 0, a + 0);
        fiat_25519_carry(out + 5, a + 5);
        fiat_25519_carry(out + 10, a + 10);
        fiat_25519_carry(out + 15, a + 15);
        escape(out);
    }
    t1 = now_sec();
    double scalar = t1 - t0;
    printf("4x scalar carry:   %.3fs (%.1f ns/call)\n", scalar, scalar / ITERS * 1e9);

    t0 = now_sec();
    for (long i = 0; i < ITERS; i++) {
        fiat_25519_batch_carry(out, a);
        escape(out);
    }
    t1 = now_sec();
    double avx = t1 - t0;
    printf("AVX batch_carry:   %.3fs (%.1f ns/call)\n", avx, avx / ITERS * 1e9);
    printf("Speedup:           %.2fx\n", scalar / avx);

    return 0;
}
HARNESS

gcc -O2 -mavx2 -o "$TMPDIR/bench_carry" "$TMPDIR/bench_carry.c" "$TMPDIR/batch_avx_carry.o" -I"$TMPDIR"
echo "--- batch_carry (AVX gather+SIMD vs 4x scalar) ---"
"$TMPDIR/bench_carry"
echo ""

echo "=== Done ==="
