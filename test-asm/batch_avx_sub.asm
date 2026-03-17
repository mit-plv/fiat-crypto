; Batched AVX2 field subtraction for curve25519 (4 independent subs in parallel).
; Uses the proper batched spec (batch_sub), NOT the n=20 trick.
;
; Memory layout is AoS (array-of-structures): 4 complete 5-limb field elements
; concatenated: [e0_l0..e0_l4, e1_l0..e1_l4, e2_l0..e2_l4, e3_l0..e3_l4].
; Each YMM processes 4 consecutive uint64s from this flat array.
;
; Balance constants (same as scalar 5-limb sub, repeating for each element):
;   limb 0: 0xfffffffffffda, limbs 1-4: 0xffffffffffffe
; In the AoS layout, the 0xfda constant rotates through YMM lanes:
;   group 0 (limbs 0-3):   [0xfda, 0xffe, 0xffe, 0xffe]
;   group 1 (limbs 4-7):   [0xffe, 0xfda, 0xffe, 0xffe]
;   group 2 (limbs 8-11):  [0xffe, 0xffe, 0xfda, 0xffe]
;   group 3 (limbs 12-15): [0xffe, 0xffe, 0xffe, 0xfda]
;   group 4 (limbs 16-19): [0xffe, 0xffe, 0xffe, 0xffe]
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' batch_sub \
;     --hints-file test-asm/batch_avx_sub.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_batch_sub

fiat_25519_batch_sub:
	; build base constant vector ymm14 = [0xffe, 0xffe, 0xffe, 0xffe]
	mov	rax, 0xffffffffffffe
	vmovq	xmm14, rax
	vpbroadcastq	ymm14, xmm14

	; build patch value ymm15 = [0xfda, 0xfda, 0xfda, 0xfda]
	mov	rax, 0xfffffffffffda
	vmovq	xmm15, rax
	vpbroadcastq	ymm15, xmm15

	; group 0 (limbs 0-3): balance = [0xfda, 0xffe, 0xffe, 0xffe]
	vpblendd	ymm5, ymm14, ymm15, 0x03	; patch lane 0
	vmovdqu	ymm0, [rsi]
	vpaddq	ymm0, ymm0, ymm5
	vpsubq	ymm0, ymm0, [rdx]
	vmovdqu	[rdi], ymm0

	; group 1 (limbs 4-7): balance = [0xffe, 0xfda, 0xffe, 0xffe]
	vpblendd	ymm6, ymm14, ymm15, 0x0C	; patch lane 1
	vmovdqu	ymm1, [rsi + 32]
	vpaddq	ymm1, ymm1, ymm6
	vpsubq	ymm1, ymm1, [rdx + 32]
	vmovdqu	[rdi + 32], ymm1

	; group 2 (limbs 8-11): balance = [0xffe, 0xffe, 0xfda, 0xffe]
	vpblendd	ymm7, ymm14, ymm15, 0x30	; patch lane 2
	vmovdqu	ymm2, [rsi + 64]
	vpaddq	ymm2, ymm2, ymm7
	vpsubq	ymm2, ymm2, [rdx + 64]
	vmovdqu	[rdi + 64], ymm2

	; group 3 (limbs 12-15): balance = [0xffe, 0xffe, 0xffe, 0xfda]
	vpblendd	ymm8, ymm14, ymm15, 0xC0	; patch lane 3
	vmovdqu	ymm3, [rsi + 96]
	vpaddq	ymm3, ymm3, ymm8
	vpsubq	ymm3, ymm3, [rdx + 96]
	vmovdqu	[rdi + 96], ymm3

	; group 4 (limbs 16-19): balance = [0xffe, 0xffe, 0xffe, 0xffe]
	vmovdqu	ymm4, [rsi + 128]
	vpaddq	ymm4, ymm4, ymm14
	vpsubq	ymm4, ymm4, [rdx + 128]
	vmovdqu	[rdi + 128], ymm4

	vzeroupper
	ret
