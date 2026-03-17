; Batched field multiplication for curve25519 (4 independent carry_muls).
; Uses the proper batched spec (batch_carry_mul), AoS layout.
;
; Memory layout: 4 complete 5-limb field elements concatenated.
;   arg1/arg2/out: 20 uint64s = [e0_l0..e0_l4, e1_l0..e1_l4, e2_l0..e2_l4, e3_l0..e3_l4]
;   Each element occupies 40 bytes (5 * 8).
;
; Strategy: inline 4 copies of the scalar carry_mul body with pointer offsets.
;   sub rsp, 24 allocates space at [rsp+0..16] to save base pointers.
;   Scalar body uses [rsp-8]..[rsp-128] (red zone) — no overlap.
;
; Scalar body derived from fiat-amd64/fiat_curve25519_carry_mul/seed0000000059842304_ratio12536.asm
;
; Check with:
;   src/ExtractionOCaml/unsaturated_solinas --inline --static --use-value-barrier \
;     25519 64 '(auto)' '2^255 - 19' batch_carry_mul \
;     --hints-file test-asm/batch_avx_carry_mul.asm -o /dev/null --output-asm /dev/null

SECTION .text
	GLOBAL fiat_25519_batch_carry_mul

fiat_25519_batch_carry_mul:
	sub rsp, 24
	mov [ rsp + 0 ], rdi
	mov [ rsp + 8 ], rsi
	mov [ rsp + 16 ], rdx

	; === element 0 (offset 0) ===
	imul rax, [ rdx + 0x10 ], 0x13
	mov r10, rdx
	mov rdx, [ rdx + 0x10 ]
	mulx rcx, r11, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r9, r8, [ r10 + 0x0 ]
	imul rdx, [ r10 + 0x20 ], 0x13
	mov [ rsp - 0x80 ], rbx
	mov [ rsp - 0x78 ], rbp
	mulx rbp, rbx, [ rsi + 0x20 ]
	mov [ rsp - 0x70 ], r12
	imul r12, [ r10 + 0x8 ], 0x13
	test al, al
	adox rbx, r8
	adox r9, rbp
	mov r8, rdx
	mov rdx, [ rsi + 0x20 ]
	mov [ rsp - 0x68 ], r13
	mulx r13, rbp, r12
	mov rdx, r8
	mulx r12, r8, [ rsi + 0x10 ]
	mov [ rsp - 0x60 ], r14
	mov [ rsp - 0x58 ], r15
	mulx r15, r14, [ rsi + 0x8 ]
	mov [ rsp - 0x50 ], rdi
	mov [ rsp - 0x48 ], rcx
	mulx rcx, rdi, [ rsi + 0x18 ]
	mov rdx, [ rsi + 0x18 ]
	mov [ rsp - 0x40 ], r11
	mov [ rsp - 0x38 ], rcx
	mulx rcx, r11, rax
	adcx rbp, r11
	adcx rcx, r13
	mov rdx, [ r10 + 0x18 ]
	lea r13, [rdx + 8 * rdx]
	lea r11, [rdx + 2 * r13]
	mov rdx, r11
	mulx r13, r11, [ rsi + 0x10 ]
	mov [ rsp - 0x30 ], rdi
	mov rdi, rdx
	mov rdx, [ r10 + 0x8 ]
	mov [ rsp - 0x28 ], r12
	mov [ rsp - 0x20 ], r8
	mulx r8, r12, [ rsi + 0x10 ]
	add rbx, r12
	adcx r8, r9
	mov rdx, rax
	mulx r9, rax, [ rsi + 0x20 ]
	mov rdx, rdi
	mulx r12, rdi, [ rsi + 0x20 ]
	mov [ rsp - 0x18 ], r8
	xor r8, r8
	adox rbp, r11
	adox r13, rcx
	adcx rbp, r14
	adcx r15, r13
	mov r14, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r11, rcx, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r8, r13, r14
	xor rdx, rdx
	adox rax, r13
	adox r8, r9
	adcx rbp, rcx
	adcx r11, r15
	mov r14, rbp
	shrd r14, r11, 51
	xor r9, r9
	adox rax, [ rsp - 0x20 ]
	adox r8, [ rsp - 0x28 ]
	mov rdx, [ r10 + 0x8 ]
	mulx rcx, r15, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r11, r13, [ r10 + 0x0 ]
	mov rdx, [ r10 + 0x0 ]
	mov [ rsp - 0x10 ], rbx
	mulx rbx, r9, [ rsi + 0x10 ]
	adcx rax, r13
	adcx r11, r8
	xor rdx, rdx
	adox rax, r15
	adox rcx, r11
	adcx rax, r14
	adc rcx, 0x0
	xor r14, r14
	adox rdi, [ rsp - 0x30 ]
	adox r12, [ rsp - 0x38 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r15, r8, [ r10 + 0x8 ]
	mov rdx, rax
	shrd rdx, rcx, 51
	xor r13, r13
	adox rdi, r9
	adox rbx, r12
	adcx rdi, r8
	adcx r15, rbx
	add rdi, [ rsp - 0x40 ]
	adcx r15, [ rsp - 0x48 ]
	xor r14, r14
	adox rdi, rdx
	adox r15, r14
	mov rdx, [ rsi + 0x0 ]
	mulx r9, r13, [ r10 + 0x18 ]
	mov rdx, 0x33
	bzhi r11, rdi, rdx
	mov rdx, [ rsi + 0x18 ]
	mulx r12, rcx, [ r10 + 0x8 ]
	mov rdx, [ r10 + 0x10 ]
	mulx rbx, r8, [ rsi + 0x8 ]
	mov rdx, [ rsi + 0x10 ]
	mov [ rsp - 0x8 ], r11
	mulx r11, r14, [ r10 + 0x10 ]
	shrd rdi, r15, 51
	mov rdx, r8
	xor r15, r15
	adox rdx, [ rsp - 0x10 ]
	adox rbx, [ rsp - 0x18 ]
	adcx rdx, r13
	adcx r9, rbx
	add rdx, rdi
	adc r9, 0x0
	mov r13, 0x33
	bzhi r8, rdx, r13
	shrd rdx, r9, 51
	mov rdi, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r9, rbx, [ rsi + 0x20 ]
	test al, al
	adox rbx, rcx
	adox r12, r9
	adcx rbx, r14
	adcx r11, r12
	mov rdx, [ rsi + 0x8 ]
	mulx r14, rcx, [ r10 + 0x18 ]
	mov rdx, [ r10 + 0x20 ]
	mulx r12, r9, [ rsi + 0x0 ]
	xor rdx, rdx
	adox rbx, rcx
	adox r14, r11
	bzhi r15, rbp, r13
	adox rbx, r9
	adox r12, r14
	add rbx, rdi
	adc r12, 0x0
	mov rbp, rbx
	shrd rbp, r12, 51
	imul rdi, rbp, 0x13
	bzhi r11, rbx, r13
	lea r15, [ r15 + rdi ]
	bzhi rcx, r15, r13
	mov r9, [ rsp - 0x50 ]
	mov [ r9 + 0x20 ], r11
	bzhi r14, rax, r13
	shr r15, 51
	lea r15, [ r15 + r14 ]
	mov rax, r15
	shr rax, 51
	add rax, [ rsp - 0x8 ]
	bzhi rbx, r15, r13
	mov [ r9 + 0x10 ], rax
	mov [ r9 + 0x0 ], rcx
	mov [ r9 + 0x8 ], rbx
	mov [ r9 + 0x18 ], r8
	mov rbx, [ rsp - 0x80 ]
	mov rbp, [ rsp - 0x78 ]
	mov r12, [ rsp - 0x70 ]
	mov r13, [ rsp - 0x68 ]
	mov r14, [ rsp - 0x60 ]
	mov r15, [ rsp - 0x58 ]

	; === element 1 (offset 0x28 = 40) ===
	mov rdi, [ rsp + 0 ]
	add rdi, 0x28
	mov rsi, [ rsp + 8 ]
	add rsi, 0x28
	mov rdx, [ rsp + 16 ]
	add rdx, 0x28
	imul rax, [ rdx + 0x10 ], 0x13
	mov r10, rdx
	mov rdx, [ rdx + 0x10 ]
	mulx rcx, r11, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r9, r8, [ r10 + 0x0 ]
	imul rdx, [ r10 + 0x20 ], 0x13
	mov [ rsp - 0x80 ], rbx
	mov [ rsp - 0x78 ], rbp
	mulx rbp, rbx, [ rsi + 0x20 ]
	mov [ rsp - 0x70 ], r12
	imul r12, [ r10 + 0x8 ], 0x13
	test al, al
	adox rbx, r8
	adox r9, rbp
	mov r8, rdx
	mov rdx, [ rsi + 0x20 ]
	mov [ rsp - 0x68 ], r13
	mulx r13, rbp, r12
	mov rdx, r8
	mulx r12, r8, [ rsi + 0x10 ]
	mov [ rsp - 0x60 ], r14
	mov [ rsp - 0x58 ], r15
	mulx r15, r14, [ rsi + 0x8 ]
	mov [ rsp - 0x50 ], rdi
	mov [ rsp - 0x48 ], rcx
	mulx rcx, rdi, [ rsi + 0x18 ]
	mov rdx, [ rsi + 0x18 ]
	mov [ rsp - 0x40 ], r11
	mov [ rsp - 0x38 ], rcx
	mulx rcx, r11, rax
	adcx rbp, r11
	adcx rcx, r13
	mov rdx, [ r10 + 0x18 ]
	lea r13, [rdx + 8 * rdx]
	lea r11, [rdx + 2 * r13]
	mov rdx, r11
	mulx r13, r11, [ rsi + 0x10 ]
	mov [ rsp - 0x30 ], rdi
	mov rdi, rdx
	mov rdx, [ r10 + 0x8 ]
	mov [ rsp - 0x28 ], r12
	mov [ rsp - 0x20 ], r8
	mulx r8, r12, [ rsi + 0x10 ]
	add rbx, r12
	adcx r8, r9
	mov rdx, rax
	mulx r9, rax, [ rsi + 0x20 ]
	mov rdx, rdi
	mulx r12, rdi, [ rsi + 0x20 ]
	mov [ rsp - 0x18 ], r8
	xor r8, r8
	adox rbp, r11
	adox r13, rcx
	adcx rbp, r14
	adcx r15, r13
	mov r14, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r11, rcx, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r8, r13, r14
	xor rdx, rdx
	adox rax, r13
	adox r8, r9
	adcx rbp, rcx
	adcx r11, r15
	mov r14, rbp
	shrd r14, r11, 51
	xor r9, r9
	adox rax, [ rsp - 0x20 ]
	adox r8, [ rsp - 0x28 ]
	mov rdx, [ r10 + 0x8 ]
	mulx rcx, r15, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r11, r13, [ r10 + 0x0 ]
	mov rdx, [ r10 + 0x0 ]
	mov [ rsp - 0x10 ], rbx
	mulx rbx, r9, [ rsi + 0x10 ]
	adcx rax, r13
	adcx r11, r8
	xor rdx, rdx
	adox rax, r15
	adox rcx, r11
	adcx rax, r14
	adc rcx, 0x0
	xor r14, r14
	adox rdi, [ rsp - 0x30 ]
	adox r12, [ rsp - 0x38 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r15, r8, [ r10 + 0x8 ]
	mov rdx, rax
	shrd rdx, rcx, 51
	xor r13, r13
	adox rdi, r9
	adox rbx, r12
	adcx rdi, r8
	adcx r15, rbx
	add rdi, [ rsp - 0x40 ]
	adcx r15, [ rsp - 0x48 ]
	xor r14, r14
	adox rdi, rdx
	adox r15, r14
	mov rdx, [ rsi + 0x0 ]
	mulx r9, r13, [ r10 + 0x18 ]
	mov rdx, 0x33
	bzhi r11, rdi, rdx
	mov rdx, [ rsi + 0x18 ]
	mulx r12, rcx, [ r10 + 0x8 ]
	mov rdx, [ r10 + 0x10 ]
	mulx rbx, r8, [ rsi + 0x8 ]
	mov rdx, [ rsi + 0x10 ]
	mov [ rsp - 0x8 ], r11
	mulx r11, r14, [ r10 + 0x10 ]
	shrd rdi, r15, 51
	mov rdx, r8
	xor r15, r15
	adox rdx, [ rsp - 0x10 ]
	adox rbx, [ rsp - 0x18 ]
	adcx rdx, r13
	adcx r9, rbx
	add rdx, rdi
	adc r9, 0x0
	mov r13, 0x33
	bzhi r8, rdx, r13
	shrd rdx, r9, 51
	mov rdi, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r9, rbx, [ rsi + 0x20 ]
	test al, al
	adox rbx, rcx
	adox r12, r9
	adcx rbx, r14
	adcx r11, r12
	mov rdx, [ rsi + 0x8 ]
	mulx r14, rcx, [ r10 + 0x18 ]
	mov rdx, [ r10 + 0x20 ]
	mulx r12, r9, [ rsi + 0x0 ]
	xor rdx, rdx
	adox rbx, rcx
	adox r14, r11
	bzhi r15, rbp, r13
	adox rbx, r9
	adox r12, r14
	add rbx, rdi
	adc r12, 0x0
	mov rbp, rbx
	shrd rbp, r12, 51
	imul rdi, rbp, 0x13
	bzhi r11, rbx, r13
	lea r15, [ r15 + rdi ]
	bzhi rcx, r15, r13
	mov r9, [ rsp - 0x50 ]
	mov [ r9 + 0x20 ], r11
	bzhi r14, rax, r13
	shr r15, 51
	lea r15, [ r15 + r14 ]
	mov rax, r15
	shr rax, 51
	add rax, [ rsp - 0x8 ]
	bzhi rbx, r15, r13
	mov [ r9 + 0x10 ], rax
	mov [ r9 + 0x0 ], rcx
	mov [ r9 + 0x8 ], rbx
	mov [ r9 + 0x18 ], r8
	mov rbx, [ rsp - 0x80 ]
	mov rbp, [ rsp - 0x78 ]
	mov r12, [ rsp - 0x70 ]
	mov r13, [ rsp - 0x68 ]
	mov r14, [ rsp - 0x60 ]
	mov r15, [ rsp - 0x58 ]

	; === element 2 (offset 0x50 = 80) ===
	mov rdi, [ rsp + 0 ]
	add rdi, 0x50
	mov rsi, [ rsp + 8 ]
	add rsi, 0x50
	mov rdx, [ rsp + 16 ]
	add rdx, 0x50
	imul rax, [ rdx + 0x10 ], 0x13
	mov r10, rdx
	mov rdx, [ rdx + 0x10 ]
	mulx rcx, r11, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r9, r8, [ r10 + 0x0 ]
	imul rdx, [ r10 + 0x20 ], 0x13
	mov [ rsp - 0x80 ], rbx
	mov [ rsp - 0x78 ], rbp
	mulx rbp, rbx, [ rsi + 0x20 ]
	mov [ rsp - 0x70 ], r12
	imul r12, [ r10 + 0x8 ], 0x13
	test al, al
	adox rbx, r8
	adox r9, rbp
	mov r8, rdx
	mov rdx, [ rsi + 0x20 ]
	mov [ rsp - 0x68 ], r13
	mulx r13, rbp, r12
	mov rdx, r8
	mulx r12, r8, [ rsi + 0x10 ]
	mov [ rsp - 0x60 ], r14
	mov [ rsp - 0x58 ], r15
	mulx r15, r14, [ rsi + 0x8 ]
	mov [ rsp - 0x50 ], rdi
	mov [ rsp - 0x48 ], rcx
	mulx rcx, rdi, [ rsi + 0x18 ]
	mov rdx, [ rsi + 0x18 ]
	mov [ rsp - 0x40 ], r11
	mov [ rsp - 0x38 ], rcx
	mulx rcx, r11, rax
	adcx rbp, r11
	adcx rcx, r13
	mov rdx, [ r10 + 0x18 ]
	lea r13, [rdx + 8 * rdx]
	lea r11, [rdx + 2 * r13]
	mov rdx, r11
	mulx r13, r11, [ rsi + 0x10 ]
	mov [ rsp - 0x30 ], rdi
	mov rdi, rdx
	mov rdx, [ r10 + 0x8 ]
	mov [ rsp - 0x28 ], r12
	mov [ rsp - 0x20 ], r8
	mulx r8, r12, [ rsi + 0x10 ]
	add rbx, r12
	adcx r8, r9
	mov rdx, rax
	mulx r9, rax, [ rsi + 0x20 ]
	mov rdx, rdi
	mulx r12, rdi, [ rsi + 0x20 ]
	mov [ rsp - 0x18 ], r8
	xor r8, r8
	adox rbp, r11
	adox r13, rcx
	adcx rbp, r14
	adcx r15, r13
	mov r14, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r11, rcx, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r8, r13, r14
	xor rdx, rdx
	adox rax, r13
	adox r8, r9
	adcx rbp, rcx
	adcx r11, r15
	mov r14, rbp
	shrd r14, r11, 51
	xor r9, r9
	adox rax, [ rsp - 0x20 ]
	adox r8, [ rsp - 0x28 ]
	mov rdx, [ r10 + 0x8 ]
	mulx rcx, r15, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r11, r13, [ r10 + 0x0 ]
	mov rdx, [ r10 + 0x0 ]
	mov [ rsp - 0x10 ], rbx
	mulx rbx, r9, [ rsi + 0x10 ]
	adcx rax, r13
	adcx r11, r8
	xor rdx, rdx
	adox rax, r15
	adox rcx, r11
	adcx rax, r14
	adc rcx, 0x0
	xor r14, r14
	adox rdi, [ rsp - 0x30 ]
	adox r12, [ rsp - 0x38 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r15, r8, [ r10 + 0x8 ]
	mov rdx, rax
	shrd rdx, rcx, 51
	xor r13, r13
	adox rdi, r9
	adox rbx, r12
	adcx rdi, r8
	adcx r15, rbx
	add rdi, [ rsp - 0x40 ]
	adcx r15, [ rsp - 0x48 ]
	xor r14, r14
	adox rdi, rdx
	adox r15, r14
	mov rdx, [ rsi + 0x0 ]
	mulx r9, r13, [ r10 + 0x18 ]
	mov rdx, 0x33
	bzhi r11, rdi, rdx
	mov rdx, [ rsi + 0x18 ]
	mulx r12, rcx, [ r10 + 0x8 ]
	mov rdx, [ r10 + 0x10 ]
	mulx rbx, r8, [ rsi + 0x8 ]
	mov rdx, [ rsi + 0x10 ]
	mov [ rsp - 0x8 ], r11
	mulx r11, r14, [ r10 + 0x10 ]
	shrd rdi, r15, 51
	mov rdx, r8
	xor r15, r15
	adox rdx, [ rsp - 0x10 ]
	adox rbx, [ rsp - 0x18 ]
	adcx rdx, r13
	adcx r9, rbx
	add rdx, rdi
	adc r9, 0x0
	mov r13, 0x33
	bzhi r8, rdx, r13
	shrd rdx, r9, 51
	mov rdi, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r9, rbx, [ rsi + 0x20 ]
	test al, al
	adox rbx, rcx
	adox r12, r9
	adcx rbx, r14
	adcx r11, r12
	mov rdx, [ rsi + 0x8 ]
	mulx r14, rcx, [ r10 + 0x18 ]
	mov rdx, [ r10 + 0x20 ]
	mulx r12, r9, [ rsi + 0x0 ]
	xor rdx, rdx
	adox rbx, rcx
	adox r14, r11
	bzhi r15, rbp, r13
	adox rbx, r9
	adox r12, r14
	add rbx, rdi
	adc r12, 0x0
	mov rbp, rbx
	shrd rbp, r12, 51
	imul rdi, rbp, 0x13
	bzhi r11, rbx, r13
	lea r15, [ r15 + rdi ]
	bzhi rcx, r15, r13
	mov r9, [ rsp - 0x50 ]
	mov [ r9 + 0x20 ], r11
	bzhi r14, rax, r13
	shr r15, 51
	lea r15, [ r15 + r14 ]
	mov rax, r15
	shr rax, 51
	add rax, [ rsp - 0x8 ]
	bzhi rbx, r15, r13
	mov [ r9 + 0x10 ], rax
	mov [ r9 + 0x0 ], rcx
	mov [ r9 + 0x8 ], rbx
	mov [ r9 + 0x18 ], r8
	mov rbx, [ rsp - 0x80 ]
	mov rbp, [ rsp - 0x78 ]
	mov r12, [ rsp - 0x70 ]
	mov r13, [ rsp - 0x68 ]
	mov r14, [ rsp - 0x60 ]
	mov r15, [ rsp - 0x58 ]

	; === element 3 (offset 0x78 = 120) ===
	mov rdi, [ rsp + 0 ]
	add rdi, 0x78
	mov rsi, [ rsp + 8 ]
	add rsi, 0x78
	mov rdx, [ rsp + 16 ]
	add rdx, 0x78
	imul rax, [ rdx + 0x10 ], 0x13
	mov r10, rdx
	mov rdx, [ rdx + 0x10 ]
	mulx rcx, r11, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r9, r8, [ r10 + 0x0 ]
	imul rdx, [ r10 + 0x20 ], 0x13
	mov [ rsp - 0x80 ], rbx
	mov [ rsp - 0x78 ], rbp
	mulx rbp, rbx, [ rsi + 0x20 ]
	mov [ rsp - 0x70 ], r12
	imul r12, [ r10 + 0x8 ], 0x13
	test al, al
	adox rbx, r8
	adox r9, rbp
	mov r8, rdx
	mov rdx, [ rsi + 0x20 ]
	mov [ rsp - 0x68 ], r13
	mulx r13, rbp, r12
	mov rdx, r8
	mulx r12, r8, [ rsi + 0x10 ]
	mov [ rsp - 0x60 ], r14
	mov [ rsp - 0x58 ], r15
	mulx r15, r14, [ rsi + 0x8 ]
	mov [ rsp - 0x50 ], rdi
	mov [ rsp - 0x48 ], rcx
	mulx rcx, rdi, [ rsi + 0x18 ]
	mov rdx, [ rsi + 0x18 ]
	mov [ rsp - 0x40 ], r11
	mov [ rsp - 0x38 ], rcx
	mulx rcx, r11, rax
	adcx rbp, r11
	adcx rcx, r13
	mov rdx, [ r10 + 0x18 ]
	lea r13, [rdx + 8 * rdx]
	lea r11, [rdx + 2 * r13]
	mov rdx, r11
	mulx r13, r11, [ rsi + 0x10 ]
	mov [ rsp - 0x30 ], rdi
	mov rdi, rdx
	mov rdx, [ r10 + 0x8 ]
	mov [ rsp - 0x28 ], r12
	mov [ rsp - 0x20 ], r8
	mulx r8, r12, [ rsi + 0x10 ]
	add rbx, r12
	adcx r8, r9
	mov rdx, rax
	mulx r9, rax, [ rsi + 0x20 ]
	mov rdx, rdi
	mulx r12, rdi, [ rsi + 0x20 ]
	mov [ rsp - 0x18 ], r8
	xor r8, r8
	adox rbp, r11
	adox r13, rcx
	adcx rbp, r14
	adcx r15, r13
	mov r14, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r11, rcx, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x18 ]
	mulx r8, r13, r14
	xor rdx, rdx
	adox rax, r13
	adox r8, r9
	adcx rbp, rcx
	adcx r11, r15
	mov r14, rbp
	shrd r14, r11, 51
	xor r9, r9
	adox rax, [ rsp - 0x20 ]
	adox r8, [ rsp - 0x28 ]
	mov rdx, [ r10 + 0x8 ]
	mulx rcx, r15, [ rsi + 0x0 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r11, r13, [ r10 + 0x0 ]
	mov rdx, [ r10 + 0x0 ]
	mov [ rsp - 0x10 ], rbx
	mulx rbx, r9, [ rsi + 0x10 ]
	adcx rax, r13
	adcx r11, r8
	xor rdx, rdx
	adox rax, r15
	adox rcx, r11
	adcx rax, r14
	adc rcx, 0x0
	xor r14, r14
	adox rdi, [ rsp - 0x30 ]
	adox r12, [ rsp - 0x38 ]
	mov rdx, [ rsi + 0x8 ]
	mulx r15, r8, [ r10 + 0x8 ]
	mov rdx, rax
	shrd rdx, rcx, 51
	xor r13, r13
	adox rdi, r9
	adox rbx, r12
	adcx rdi, r8
	adcx r15, rbx
	add rdi, [ rsp - 0x40 ]
	adcx r15, [ rsp - 0x48 ]
	xor r14, r14
	adox rdi, rdx
	adox r15, r14
	mov rdx, [ rsi + 0x0 ]
	mulx r9, r13, [ r10 + 0x18 ]
	mov rdx, 0x33
	bzhi r11, rdi, rdx
	mov rdx, [ rsi + 0x18 ]
	mulx r12, rcx, [ r10 + 0x8 ]
	mov rdx, [ r10 + 0x10 ]
	mulx rbx, r8, [ rsi + 0x8 ]
	mov rdx, [ rsi + 0x10 ]
	mov [ rsp - 0x8 ], r11
	mulx r11, r14, [ r10 + 0x10 ]
	shrd rdi, r15, 51
	mov rdx, r8
	xor r15, r15
	adox rdx, [ rsp - 0x10 ]
	adox rbx, [ rsp - 0x18 ]
	adcx rdx, r13
	adcx r9, rbx
	add rdx, rdi
	adc r9, 0x0
	mov r13, 0x33
	bzhi r8, rdx, r13
	shrd rdx, r9, 51
	mov rdi, rdx
	mov rdx, [ r10 + 0x0 ]
	mulx r9, rbx, [ rsi + 0x20 ]
	test al, al
	adox rbx, rcx
	adox r12, r9
	adcx rbx, r14
	adcx r11, r12
	mov rdx, [ rsi + 0x8 ]
	mulx r14, rcx, [ r10 + 0x18 ]
	mov rdx, [ r10 + 0x20 ]
	mulx r12, r9, [ rsi + 0x0 ]
	xor rdx, rdx
	adox rbx, rcx
	adox r14, r11
	bzhi r15, rbp, r13
	adox rbx, r9
	adox r12, r14
	add rbx, rdi
	adc r12, 0x0
	mov rbp, rbx
	shrd rbp, r12, 51
	imul rdi, rbp, 0x13
	bzhi r11, rbx, r13
	lea r15, [ r15 + rdi ]
	bzhi rcx, r15, r13
	mov r9, [ rsp - 0x50 ]
	mov [ r9 + 0x20 ], r11
	bzhi r14, rax, r13
	shr r15, 51
	lea r15, [ r15 + r14 ]
	mov rax, r15
	shr rax, 51
	add rax, [ rsp - 0x8 ]
	bzhi rbx, r15, r13
	mov [ r9 + 0x10 ], rax
	mov [ r9 + 0x0 ], rcx
	mov [ r9 + 0x8 ], rbx
	mov [ r9 + 0x18 ], r8
	mov rbx, [ rsp - 0x80 ]
	mov rbp, [ rsp - 0x78 ]
	mov r12, [ rsp - 0x70 ]
	mov r13, [ rsp - 0x68 ]
	mov r14, [ rsp - 0x60 ]
	mov r15, [ rsp - 0x58 ]

	add rsp, 24
	ret
