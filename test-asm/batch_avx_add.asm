; Batched AVX2 field addition for curve25519 (4 independent adds in parallel).
;
; Spec: fiat_25519_batch_add from src/PushButtonSynthesis/SIMDUnsaturatedSolinas.v
; (batched_addmod), exposed via the synthesis CLI as the operation `batch_add`.
;
; The spec takes two flat 20-element arrays (4 field elements x 5 limbs) and
; returns a 20-element result. For unsaturated solinas at this point in the
; pipeline `add` is just elementwise, so the spec reduces to 20 independent
; uint64 adds with no cross-position interaction. This means the equivalence
; checker is layout-agnostic for `batch_add`: any memory layout where the
; same index `i` on each side maps to the same Z value works.
;
; Layout used here is structure-of-arrays so each YMM holds the same limb
; position across all 4 elements, giving contiguous loads/stores:
;
;   Memory (20 uint64s):
;     [limb0_e0, limb0_e1, limb0_e2, limb0_e3,   <- ymm0 loads this (offset 0)
;      limb1_e0, limb1_e1, limb1_e2, limb1_e3,   <- ymm1 loads this (offset 32)
;      limb2_e0, limb2_e1, limb2_e2, limb2_e3,   <- ymm2 loads this (offset 64)
;      limb3_e0, limb3_e1, limb3_e2, limb3_e3,   <- ymm3 loads this (offset 96)
;      limb4_e0, limb4_e1, limb4_e2, limb4_e3]   <- ymm4 loads this (offset 128)
;
; Each of the 5 iterations does: load arg1 group, add arg2 group, store result.
;
; Calling convention (System V AMD64): rdi=out, rsi=arg1, rdx=arg2.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 5 '2^255 - 19' batch_add \
;     --hints-file test-asm/batch_avx_add.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_batch_add

fiat_25519_batch_add:
	; group 0: limb 0 of all 4 elements
	vmovdqu ymm0, [rsi]		; ymm0 = arg1[0..3]
	vpaddq ymm0, ymm0, [rdx]	; ymm0 += arg2[0..3]
	vmovdqu [rdi], ymm0		; out[0..3] = ymm0

	; group 1: limb 1 of all 4 elements
	vmovdqu ymm1, [rsi + 32]
	vpaddq ymm1, ymm1, [rdx + 32]
	vmovdqu [rdi + 32], ymm1

	; group 2: limb 2 of all 4 elements
	vmovdqu ymm2, [rsi + 64]
	vpaddq ymm2, ymm2, [rdx + 64]
	vmovdqu [rdi + 64], ymm2

	; group 3: limb 3 of all 4 elements
	vmovdqu ymm3, [rsi + 96]
	vpaddq ymm3, ymm3, [rdx + 96]
	vmovdqu [rdi + 96], ymm3

	; group 4: limb 4 of all 4 elements
	vmovdqu ymm4, [rsi + 128]
	vpaddq ymm4, ymm4, [rdx + 128]
	vmovdqu [rdi + 128], ymm4

	vzeroupper			; clear upper YMM bits (AVX/SSE transition penalty)
	ret
