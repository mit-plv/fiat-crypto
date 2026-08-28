; AVX2 vectorized field addition for curve25519 (unsaturated solinas, 5 limbs x 64-bit).
; Equivalent to the scalar fiat_25519_add: adds 5 pairs of 64-bit limbs.
; Uses a single YMM register to add limbs 0-3 (256 bits) via vpaddq ymm,
; then a scalar mov/add/mov for limb 4.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' add \
;     --hints-file test-avx/simple_avx_add_ymm.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_add

fiat_25519_add:
	; limbs 0-3: load 256 bits (four 64-bit limbs) from each input, add, store
	vmovdqu	ymm0, [rsi]
	vmovdqu	ymm1, [rdx]
	vpaddq	ymm0, ymm0, ymm1
	vmovdqu	[rdi], ymm0
	; limb 4: scalar 64-bit add
	mov	rax, [rsi + 32]
	add	rax, [rdx + 32]
	mov	[rdi + 32], rax
	vzeroupper
	ret
