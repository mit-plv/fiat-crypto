; AVX vectorized field subtraction for curve25519 (unsaturated solinas, 5 limbs x 64-bit).
; Equivalent to scalar fiat_25519_sub: out[i] = balance[i] + arg1[i] - arg2[i]
; where balance = [0xfffffffffffda, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe, 0xffffffffffffe]
;
; Uses vmovq to load each limb individually, vpaddq/vpsubq for arithmetic.
; Tests constant handling and vpsubq through the equivalence checker.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' sub \
;     --hints-file test-avx/simple_avx_sub.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_sub

fiat_25519_sub:
	; limb 0: balance = 0xfffffffffffda
	mov	rax, 0xfffffffffffda
	vmovq	xmm0, rax
	vmovq	xmm1, [rsi]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	xmm1, [rdx]
	vpsubq	xmm0, xmm0, xmm1
	vmovq	[rdi], xmm0

	; limb 1: balance = 0xffffffffffffe
	mov	rax, 0xffffffffffffe
	vmovq	xmm0, rax
	vmovq	xmm1, [rsi + 8]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	xmm1, [rdx + 8]
	vpsubq	xmm0, xmm0, xmm1
	vmovq	[rdi + 8], xmm0

	; limb 2: balance = 0xffffffffffffe
	vmovq	xmm0, rax
	vmovq	xmm1, [rsi + 16]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	xmm1, [rdx + 16]
	vpsubq	xmm0, xmm0, xmm1
	vmovq	[rdi + 16], xmm0

	; limb 3: balance = 0xffffffffffffe
	vmovq	xmm0, rax
	vmovq	xmm1, [rsi + 24]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	xmm1, [rdx + 24]
	vpsubq	xmm0, xmm0, xmm1
	vmovq	[rdi + 24], xmm0

	; limb 4: balance = 0xffffffffffffe
	vmovq	xmm0, rax
	vmovq	xmm1, [rsi + 32]
	vpaddq	xmm0, xmm0, xmm1
	vmovq	xmm1, [rdx + 32]
	vpsubq	xmm0, xmm0, xmm1
	vmovq	[rdi + 32], xmm0

	ret
