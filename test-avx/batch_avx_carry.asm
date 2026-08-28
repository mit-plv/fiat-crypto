SECTION .text
	GLOBAL fiat_25519_batch_carry

; Batched carry reduction for curve25519: 4 independent elements in parallel
; Calling convention: rdi = out1, rsi = arg1
; Memory layout (AoS): arg1[0..4] = elem0, arg1[5..9] = elem1, etc.
;
; Register plan:
;   ymm0-ymm4  = limbs 0-4 (each YMM holds one limb from all 4 elements)
;   ymm5        = mask51 (0x7ffffffffffff in all lanes)
;   ymm6        = constant 19 in all lanes
;   ymm7-ymm8   = scratch (carries)
;   xmm9-xmm10  = scratch (gather/scatter)
;   rax, rcx     = scratch

fiat_25519_batch_carry:

; ============================================================
; Phase 0: Load constants
; ============================================================

	; mask51 = 0x7ffffffffffff = (1 << 51) - 1
	mov rax, 0x7ffffffffffff
	vmovq xmm5, rax
	vpbroadcastq ymm5, xmm5

	; constant 19
	mov rax, 19
	vmovq xmm6, rax
	vpbroadcastq ymm6, xmm6

; ============================================================
; Phase 1: Gather — transpose AoS to lane-parallel YMMs
; ============================================================
; For limb i, load arg1[i], arg1[5+i], arg1[10+i], arg1[15+i]

	; --- ymm0: limb 0 ---
	mov rax, [rsi + 0]
	vmovq xmm0, rax
	mov rax, [rsi + 40]
	vmovq xmm9, rax
	vpunpcklqdq xmm0, xmm0, xmm9
	mov rax, [rsi + 80]
	vmovq xmm9, rax
	mov rax, [rsi + 120]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm0, ymm0, xmm9, 1

	; --- ymm1: limb 1 ---
	mov rax, [rsi + 8]
	vmovq xmm1, rax
	mov rax, [rsi + 48]
	vmovq xmm9, rax
	vpunpcklqdq xmm1, xmm1, xmm9
	mov rax, [rsi + 88]
	vmovq xmm9, rax
	mov rax, [rsi + 128]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm1, ymm1, xmm9, 1

	; --- ymm2: limb 2 ---
	mov rax, [rsi + 16]
	vmovq xmm2, rax
	mov rax, [rsi + 56]
	vmovq xmm9, rax
	vpunpcklqdq xmm2, xmm2, xmm9
	mov rax, [rsi + 96]
	vmovq xmm9, rax
	mov rax, [rsi + 136]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm2, ymm2, xmm9, 1

	; --- ymm3: limb 3 ---
	mov rax, [rsi + 24]
	vmovq xmm3, rax
	mov rax, [rsi + 64]
	vmovq xmm9, rax
	vpunpcklqdq xmm3, xmm3, xmm9
	mov rax, [rsi + 104]
	vmovq xmm9, rax
	mov rax, [rsi + 144]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm3, ymm3, xmm9, 1

	; --- ymm4: limb 4 ---
	mov rax, [rsi + 32]
	vmovq xmm4, rax
	mov rax, [rsi + 72]
	vmovq xmm9, rax
	vpunpcklqdq xmm4, xmm4, xmm9
	mov rax, [rsi + 112]
	vmovq xmm9, rax
	mov rax, [rsi + 152]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm4, ymm4, xmm9, 1

; ============================================================
; Phase 2: Carry chain (all 4 elements in parallel)
; ============================================================
; Matches fiat_25519_batch_carry from curve25519_64.c:
;   x2 = (x1 >> 51) + arg1[1]
;   x3 = (x2 >> 51) + arg1[2]
;   x4 = (x3 >> 51) + arg1[3]
;   x5 = (x4 >> 51) + arg1[4]
;   x6 = (x1 & mask) + (x5 >> 51) * 19
;   x7 = (x6 >> 51) + (x2 & mask)
;   x8 = x6 & mask
;   x9 = x7 & mask
;   x10 = (x7 >> 51) + (x3 & mask)
;   x11 = x4 & mask
;   x12 = x5 & mask

	; First pass: carry propagation 0 -> 1 -> 2 -> 3 -> 4
	vpsrlq ymm7, ymm0, 51       ; carry0 = ymm0 >> 51
	vpaddq ymm1, ymm1, ymm7     ; x2 = carry0 + limb1

	vpsrlq ymm7, ymm1, 51       ; carry1 = x2 >> 51
	vpaddq ymm2, ymm2, ymm7     ; x3 = carry1 + limb2

	vpsrlq ymm7, ymm2, 51       ; carry2 = x3 >> 51
	vpaddq ymm3, ymm3, ymm7     ; x4 = carry2 + limb3

	vpsrlq ymm7, ymm3, 51       ; carry3 = x4 >> 51
	vpaddq ymm4, ymm4, ymm7     ; x5 = carry3 + limb4

	; Wrap-around: carry from limb 4 * 19 back to limb 0
	vpsrlq ymm7, ymm4, 51       ; carry4 = x5 >> 51
	vpmuludq ymm7, ymm7, ymm6   ; carry4 * 19
	vpandq ymm0, ymm0, ymm5     ; x1 & mask
	vpaddq ymm0, ymm0, ymm7     ; x6 = (x1 & mask) + carry4 * 19

	; Mask limbs 1-4 from first pass
	vpandq ymm1, ymm1, ymm5     ; x2 & mask
	vpandq ymm2, ymm2, ymm5     ; x3 & mask
	vpandq ymm3, ymm3, ymm5     ; x4 & mask  (= x11)
	vpandq ymm4, ymm4, ymm5     ; x5 & mask  (= x12)

	; Second pass: carry from limb 0 -> 1 -> 2
	vpsrlq ymm7, ymm0, 51       ; carry0b = x6 >> 51
	vpandq ymm0, ymm0, ymm5     ; x8 = x6 & mask
	vpaddq ymm1, ymm1, ymm7     ; x7 = carry0b + (x2 & mask)

	vpsrlq ymm7, ymm1, 51       ; carry1b = x7 >> 51
	vpandq ymm1, ymm1, ymm5     ; x9 = x7 & mask
	vpaddq ymm2, ymm2, ymm7     ; x10 = carry1b + (x3 & mask)

; ============================================================
; Phase 3: Scatter — store YMM lanes back to AoS memory
; ============================================================
; For limb i, store to out1[i], out1[5+i], out1[10+i], out1[15+i]

	; --- ymm0: limb 0 ---
	vmovq rax, xmm0
	mov [rdi + 0], rax
	vpextrq rax, xmm0, 1
	mov [rdi + 40], rax
	vextracti128 xmm9, ymm0, 1
	vmovq rax, xmm9
	mov [rdi + 80], rax
	vpextrq rax, xmm9, 1
	mov [rdi + 120], rax

	; --- ymm1: limb 1 ---
	vmovq rax, xmm1
	mov [rdi + 8], rax
	vpextrq rax, xmm1, 1
	mov [rdi + 48], rax
	vextracti128 xmm9, ymm1, 1
	vmovq rax, xmm9
	mov [rdi + 88], rax
	vpextrq rax, xmm9, 1
	mov [rdi + 128], rax

	; --- ymm2: limb 2 ---
	vmovq rax, xmm2
	mov [rdi + 16], rax
	vpextrq rax, xmm2, 1
	mov [rdi + 56], rax
	vextracti128 xmm9, ymm2, 1
	vmovq rax, xmm9
	mov [rdi + 96], rax
	vpextrq rax, xmm9, 1
	mov [rdi + 136], rax

	; --- ymm3: limb 3 ---
	vmovq rax, xmm3
	mov [rdi + 24], rax
	vpextrq rax, xmm3, 1
	mov [rdi + 64], rax
	vextracti128 xmm9, ymm3, 1
	vmovq rax, xmm9
	mov [rdi + 104], rax
	vpextrq rax, xmm9, 1
	mov [rdi + 144], rax

	; --- ymm4: limb 4 ---
	vmovq rax, xmm4
	mov [rdi + 32], rax
	vpextrq rax, xmm4, 1
	mov [rdi + 72], rax
	vextracti128 xmm9, ymm4, 1
	vmovq rax, xmm9
	mov [rdi + 112], rax
	vpextrq rax, xmm9, 1
	mov [rdi + 152], rax

	vzeroupper
	ret
