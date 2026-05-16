SECTION .text
	GLOBAL fiat_25519_batch_carry

fiat_25519_batch_carry:
	;; Batch carry reduction for 4 independent curve25519 field elements
	;; AoS layout: arg1[0..4], arg1[5..9], arg1[10..14], arg1[15..19]
	;; PHOAS order: element 3, 2, 1, 0
	;; rdi = out1, rsi = arg1

	push rbx
	push r12
	push r13
	push r14
	push r15

	mov r15, 0x7ffffffffffff       ; mask = 2^51 - 1

	;; ===== Element 3: arg1[15..19] -> out1[15..19] =====
	;; x1 = arg1[15]
	mov rax, [rsi + 120]
	;; x2 = (x1 >> 51) + arg1[16]
	mov rbx, rax
	shr rbx, 51
	add rbx, [rsi + 128]
	;; x3 = (x2 >> 51) + arg1[17]
	mov rcx, rbx
	shr rcx, 51
	add rcx, [rsi + 136]
	;; x4 = (x3 >> 51) + arg1[18]
	mov rdx, rcx
	shr rdx, 51
	add rdx, [rsi + 144]
	;; x5 = (x4 >> 51) + arg1[19]
	mov r8, rdx
	shr r8, 51
	add r8, [rsi + 152]
	;; x6 = (x1 & mask) + (x5 >> 51) * 19
	mov r9, r8
	shr r9, 51
	imul r9, r9, 19
	and rax, r15
	add rax, r9
	;; x7 = (uint1)(x6 >> 51) + (x2 & mask)
	mov r9, rax
	shr r9, 51
	and rbx, r15
	add r9, rbx
	;; Store element 3 outputs
	;; out1[15] = x6 & mask
	mov r10, rax
	and r10, r15
	mov [rdi + 120], r10
	;; out1[16] = x7 & mask
	mov r10, r9
	and r10, r15
	mov [rdi + 128], r10
	;; out1[17] = (uint1)(x7 >> 51) + (x3 & mask)
	mov r10, r9
	shr r10, 51
	and rcx, r15
	add r10, rcx
	mov [rdi + 136], r10
	;; out1[18] = x4 & mask
	and rdx, r15
	mov [rdi + 144], rdx
	;; out1[19] = x5 & mask
	and r8, r15
	mov [rdi + 152], r8

	;; ===== Element 2: arg1[10..14] -> out1[10..14] =====
	;; x8 = arg1[10]
	mov rax, [rsi + 80]
	;; x9 = (x8 >> 51) + arg1[11]
	mov rbx, rax
	shr rbx, 51
	add rbx, [rsi + 88]
	;; x10 = (x9 >> 51) + arg1[12]
	mov rcx, rbx
	shr rcx, 51
	add rcx, [rsi + 96]
	;; x11 = (x10 >> 51) + arg1[13]
	mov rdx, rcx
	shr rdx, 51
	add rdx, [rsi + 104]
	;; x12 = (x11 >> 51) + arg1[14]
	mov r8, rdx
	shr r8, 51
	add r8, [rsi + 112]
	;; x13 = (x8 & mask) + (x12 >> 51) * 19
	mov r9, r8
	shr r9, 51
	imul r9, r9, 19
	and rax, r15
	add rax, r9
	;; x14 = (uint1)(x13 >> 51) + (x9 & mask)
	mov r9, rax
	shr r9, 51
	and rbx, r15
	add r9, rbx
	;; Store element 2 outputs
	;; out1[10] = x13 & mask
	mov r10, rax
	and r10, r15
	mov [rdi + 80], r10
	;; out1[11] = x14 & mask
	mov r10, r9
	and r10, r15
	mov [rdi + 88], r10
	;; out1[12] = (uint1)(x14 >> 51) + (x10 & mask)
	mov r10, r9
	shr r10, 51
	and rcx, r15
	add r10, rcx
	mov [rdi + 96], r10
	;; out1[13] = x11 & mask
	and rdx, r15
	mov [rdi + 104], rdx
	;; out1[14] = x12 & mask
	and r8, r15
	mov [rdi + 112], r8

	;; ===== Element 1: arg1[5..9] -> out1[5..9] =====
	;; x15 = arg1[5]
	mov rax, [rsi + 40]
	;; x16 = (x15 >> 51) + arg1[6]
	mov rbx, rax
	shr rbx, 51
	add rbx, [rsi + 48]
	;; x17 = (x16 >> 51) + arg1[7]
	mov rcx, rbx
	shr rcx, 51
	add rcx, [rsi + 56]
	;; x18 = (x17 >> 51) + arg1[8]
	mov rdx, rcx
	shr rdx, 51
	add rdx, [rsi + 64]
	;; x19 = (x18 >> 51) + arg1[9]
	mov r8, rdx
	shr r8, 51
	add r8, [rsi + 72]
	;; x20 = (x15 & mask) + (x19 >> 51) * 19
	mov r9, r8
	shr r9, 51
	imul r9, r9, 19
	and rax, r15
	add rax, r9
	;; x21 = (uint1)(x20 >> 51) + (x16 & mask)
	mov r9, rax
	shr r9, 51
	and rbx, r15
	add r9, rbx
	;; Store element 1 outputs
	;; out1[5] = x20 & mask
	mov r10, rax
	and r10, r15
	mov [rdi + 40], r10
	;; out1[6] = x21 & mask
	mov r10, r9
	and r10, r15
	mov [rdi + 48], r10
	;; out1[7] = (uint1)(x21 >> 51) + (x17 & mask)
	mov r10, r9
	shr r10, 51
	and rcx, r15
	add r10, rcx
	mov [rdi + 56], r10
	;; out1[8] = x18 & mask
	and rdx, r15
	mov [rdi + 64], rdx
	;; out1[9] = x19 & mask
	and r8, r15
	mov [rdi + 72], r8

	;; ===== Element 0: arg1[0..4] -> out1[0..4] =====
	;; x22 = arg1[0]
	mov rax, [rsi]
	;; x23 = (x22 >> 51) + arg1[1]
	mov rbx, rax
	shr rbx, 51
	add rbx, [rsi + 8]
	;; x24 = (x23 >> 51) + arg1[2]
	mov rcx, rbx
	shr rcx, 51
	add rcx, [rsi + 16]
	;; x25 = (x24 >> 51) + arg1[3]
	mov rdx, rcx
	shr rdx, 51
	add rdx, [rsi + 24]
	;; x26 = (x25 >> 51) + arg1[4]
	mov r8, rdx
	shr r8, 51
	add r8, [rsi + 32]
	;; x27 = (x22 & mask) + (x26 >> 51) * 19
	mov r9, r8
	shr r9, 51
	imul r9, r9, 19
	and rax, r15
	add rax, r9
	;; x28 = (uint1)(x27 >> 51) + (x23 & mask)
	mov r9, rax
	shr r9, 51
	and rbx, r15
	add r9, rbx
	;; Store element 0 outputs
	;; out1[0] = x27 & mask
	mov r10, rax
	and r10, r15
	mov [rdi], r10
	;; out1[1] = x28 & mask
	mov r10, r9
	and r10, r15
	mov [rdi + 8], r10
	;; out1[2] = (uint1)(x28 >> 51) + (x24 & mask)
	mov r10, r9
	shr r10, 51
	and rcx, r15
	add r10, rcx
	mov [rdi + 16], r10
	;; out1[3] = x25 & mask
	and rdx, r15
	mov [rdi + 24], rdx
	;; out1[4] = x26 & mask
	and r8, r15
	mov [rdi + 32], r8

	pop r15
	pop r14
	pop r13
	pop r12
	pop rbx
	ret
