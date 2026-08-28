; AVX vectorized field addition for curve25519 (unsaturated solinas, 5 limbs x 64-bit).
; Equivalent to the scalar fiat_25519_add: adds 5 pairs of 64-bit limbs.
; Uses XMM registers to add 2 limbs at a time via vpaddq, plus one
; remaining limb via vmovq.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' add \
;     --hints-file test-avx/simple_avx_add.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	; limbs 0-1: load 128 bits (two 64-bit limbs) from each input, add, store
	vmovdqu	xmm0, [rsi]
	vmovdqu	xmm1, [rdx]
	vpaddq	xmm0, xmm0, xmm1
	vmovdqu	[rdi], xmm0
	; limbs 2-3: same pattern at offset +16
	vmovdqu	xmm0, [rsi + 16]
	vmovdqu	xmm1, [rdx + 16]
	vpaddq	xmm0, xmm0, xmm1
	vmovdqu	[rdi + 16], xmm0
	; limb 4: single 64-bit limb via vmovq
	vmovq	xmm0, [rsi + 32]
	vmovq	xmm1, [rdx + 32]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	[rdi + 32], xmm0
	ret
