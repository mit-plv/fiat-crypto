; AVX2 vectorized field subtraction for curve25519 (unsaturated solinas, 5 limbs x 64-bit).
; Equivalent to scalar fiat_25519_sub: out[i] = balance[i] + arg1[i] - arg2[i]
; where balance = [0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]
;
; Uses a single YMM register to process limbs 0-3 (256 bits) via vpaddq/vpsubq ymm,
; then scalar arithmetic for limb 4.
;
; The balance constants are loaded into ymm2 by building them in a GPR and broadcasting
; via vmovq + vpbroadcastq, then patching lane 0 which has a different value.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' sub \
;     --hints-file test-asm/simple_avx_sub_ymm.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_sub

fiat_25519_sub:
	; build balance vector in ymm2:
	;   lane 0 = 0xfffffffffffda, lanes 1-3 = 0xffffffffffffe
	mov	rax, 0xffffffffffffe
	vmovq	xmm2, rax
	vpbroadcastq	ymm2, xmm2		; ymm2 = [0xffe, 0xffe, 0xffe, 0xffe]
	mov	rax, 0xfffffffffffda
	vmovq	xmm3, rax
	vpblendd	ymm2, ymm2, ymm3, 0x03	; replace lane 0 (low 2 dwords) with 0xfda

	; limbs 0-3: balance + arg1 - arg2
	vmovdqu	ymm0, [rsi]
	vmovdqu	ymm1, [rdx]
	vpaddq	ymm2, ymm2, ymm0		; balance + arg1
	vpsubq	ymm2, ymm2, ymm1		; (balance + arg1) - arg2
	vmovdqu	[rdi], ymm2

	; limb 4: scalar balance + arg1 - arg2
	mov	rax, 0xffffffffffffe
	add	rax, [rsi + 32]
	sub	rax, [rdx + 32]
	mov	[rdi + 32], rax

	vzeroupper
	ret
