SECTION .text
	GLOBAL fiat_25519_batch_carry_add

; Batched carry_add for curve25519: 4 independent (add + carry) in parallel.
; carry_add(arg1, arg2) = carry(arg1 + arg2), per element.
; Calling convention: rdi = out1, rsi = arg1, rdx = arg2.
; Memory layout (AoS): 4 elements x 5 limbs = 20 uint64s.
;   Each element occupies 40 bytes (5 * 8).
;
; Strategy: gather same-limb values from all 4 elements into YMM lanes,
; add the two inputs, run the carry chain in parallel, then scatter back.
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' batch_carry_add \
;     --hints-file test-avx/batch_avx_carry_add.asm -o /dev/null --output-asm /dev/null

fiat_25519_batch_carry_add:

; ============================================================
; Phase 0: Load constants
; ============================================================

	; mask51 = 0x7ffffffffffff
	mov rax, 0x7ffffffffffff
	vmovq xmm5, rax
	vpbroadcastq ymm5, xmm5

	; constant 19
	mov rax, 19
	vmovq xmm6, rax
	vpbroadcastq ymm6, xmm6

; ============================================================
; Phase 1: Gather + Add
; ============================================================
; For limb i, gather arg1[i], arg1[5+i], arg1[10+i], arg1[15+i] into ymm,
; gather arg2 same positions into scratch, add them.

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

	mov rax, [rdx + 0]
	vmovq xmm7, rax
	mov rax, [rdx + 40]
	vmovq xmm9, rax
	vpunpcklqdq xmm7, xmm7, xmm9
	mov rax, [rdx + 80]
	vmovq xmm9, rax
	mov rax, [rdx + 120]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm7, ymm7, xmm9, 1

	vpaddq ymm0, ymm0, ymm7

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

	mov rax, [rdx + 8]
	vmovq xmm7, rax
	mov rax, [rdx + 48]
	vmovq xmm9, rax
	vpunpcklqdq xmm7, xmm7, xmm9
	mov rax, [rdx + 88]
	vmovq xmm9, rax
	mov rax, [rdx + 128]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm7, ymm7, xmm9, 1

	vpaddq ymm1, ymm1, ymm7

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

	mov rax, [rdx + 16]
	vmovq xmm7, rax
	mov rax, [rdx + 56]
	vmovq xmm9, rax
	vpunpcklqdq xmm7, xmm7, xmm9
	mov rax, [rdx + 96]
	vmovq xmm9, rax
	mov rax, [rdx + 136]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm7, ymm7, xmm9, 1

	vpaddq ymm2, ymm2, ymm7

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

	mov rax, [rdx + 24]
	vmovq xmm7, rax
	mov rax, [rdx + 64]
	vmovq xmm9, rax
	vpunpcklqdq xmm7, xmm7, xmm9
	mov rax, [rdx + 104]
	vmovq xmm9, rax
	mov rax, [rdx + 144]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm7, ymm7, xmm9, 1

	vpaddq ymm3, ymm3, ymm7

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

	mov rax, [rdx + 32]
	vmovq xmm7, rax
	mov rax, [rdx + 72]
	vmovq xmm9, rax
	vpunpcklqdq xmm7, xmm7, xmm9
	mov rax, [rdx + 112]
	vmovq xmm9, rax
	mov rax, [rdx + 152]
	vmovq xmm10, rax
	vpunpcklqdq xmm9, xmm9, xmm10
	vinserti128 ymm7, ymm7, xmm9, 1

	vpaddq ymm4, ymm4, ymm7

; ============================================================
; Phase 2: Carry chain (identical to batch_avx_carry)
; ============================================================

	; First pass: carry propagation 0 -> 1 -> 2 -> 3 -> 4
	vpsrlq ymm7, ymm0, 51
	vpaddq ymm1, ymm1, ymm7

	vpsrlq ymm7, ymm1, 51
	vpaddq ymm2, ymm2, ymm7

	vpsrlq ymm7, ymm2, 51
	vpaddq ymm3, ymm3, ymm7

	vpsrlq ymm7, ymm3, 51
	vpaddq ymm4, ymm4, ymm7

	; Wrap-around: carry from limb 4 * 19 back to limb 0
	vpsrlq ymm7, ymm4, 51
	vpmuludq ymm7, ymm7, ymm6
	vpandq ymm0, ymm0, ymm5
	vpaddq ymm0, ymm0, ymm7

	; Mask limbs 1-4
	vpandq ymm1, ymm1, ymm5
	vpandq ymm2, ymm2, ymm5
	vpandq ymm3, ymm3, ymm5
	vpandq ymm4, ymm4, ymm5

	; Second pass: carry from limb 0 -> 1 -> 2
	vpsrlq ymm7, ymm0, 51
	vpandq ymm0, ymm0, ymm5
	vpaddq ymm1, ymm1, ymm7

	vpsrlq ymm7, ymm1, 51
	vpandq ymm1, ymm1, ymm5
	vpaddq ymm2, ymm2, ymm7

; ============================================================
; Phase 3: Scatter — store YMM lanes back to AoS memory
; ============================================================

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
