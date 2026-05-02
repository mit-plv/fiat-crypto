; Batched AVX2 field negation for curve25519 (4 independent opps in parallel).
;
; Spec: batch_opp from SIMDUnsaturatedSolinas.v (batched_oppmod).
; opp(arg1) = balance - arg1, elementwise per limb.
;
; Memory layout: AoS, 4 elements x 5 limbs = 20 uint64s.
; Processed in groups of 4 consecutive uint64s per YMM.
;
; Balance constants (same as sub/opp):
;   limb 0: 0xfffffffffffda, limbs 1-4: 0xffffffffffffe
; In AoS layout, the 0xfda constant rotates through YMM lanes:
;   group 0 (limbs 0-3):   [0xfda, 0xffe, 0xffe, 0xffe]
;   group 1 (limbs 4-7):   [0xffe, 0xfda, 0xffe, 0xffe]
;   group 2 (limbs 8-11):  [0xffe, 0xffe, 0xfda, 0xffe]
;   group 3 (limbs 12-15): [0xffe, 0xffe, 0xffe, 0xfda]
;   group 4 (limbs 16-19): [0xffe, 0xffe, 0xffe, 0xffe]
;
; Calling convention (System V AMD64): rdi=out1, rsi=arg1.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' batch_opp \
;     --hints-file test-asm/batch_avx_opp.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_batch_opp

fiat_25519_batch_opp:
	; build base constant vector ymm14 = [0xffe, 0xffe, 0xffe, 0xffe]
	mov	rax, 0xffffffffffffe
	vmovq	xmm14, rax
	vpbroadcastq	ymm14, xmm14

	; build patch value ymm15 = [0xfda, 0xfda, 0xfda, 0xfda]
	mov	rax, 0xfffffffffffda
	vmovq	xmm15, rax
	vpbroadcastq	ymm15, xmm15

	; group 0 (limbs 0-3): balance = [0xfda, 0xffe, 0xffe, 0xffe]
	vpblendd	ymm5, ymm14, ymm15, 0x03
	vpsubq	ymm0, ymm5, [rsi]
	vmovdqu	[rdi], ymm0

	; group 1 (limbs 4-7): balance = [0xffe, 0xfda, 0xffe, 0xffe]
	vpblendd	ymm6, ymm14, ymm15, 0x0C
	vpsubq	ymm1, ymm6, [rsi + 32]
	vmovdqu	[rdi + 32], ymm1

	; group 2 (limbs 8-11): balance = [0xffe, 0xffe, 0xfda, 0xffe]
	vpblendd	ymm7, ymm14, ymm15, 0x30
	vpsubq	ymm2, ymm7, [rsi + 64]
	vmovdqu	[rdi + 64], ymm2

	; group 3 (limbs 12-15): balance = [0xffe, 0xffe, 0xffe, 0xfda]
	vpblendd	ymm8, ymm14, ymm15, 0xC0
	vpsubq	ymm3, ymm8, [rsi + 96]
	vmovdqu	[rdi + 96], ymm3

	; group 4 (limbs 16-19): balance = [0xffe, 0xffe, 0xffe, 0xffe]
	vpsubq	ymm4, ymm14, [rsi + 128]
	vmovdqu	[rdi + 128], ymm4

	vzeroupper
	ret
