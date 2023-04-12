SECTION .text
	GLOBAL fiat_p521_carry_square
fiat_p521_carry_square:
sub rsp, 520
mov rax, [ rsi + 0x40 ]
lea r10, [ 4 * rax]
mov rax, [ rsi + 0x28 ]
mov r11, rax
shl r11, 0x2
mov rdx, r10
mulx r10, rax, [ rsi + 0x20 ]
mov rcx, 0x1 
shlx r8, [ rsi + 0x28 ], rcx
mov r9, [ rsi + 0x38 ]
lea rcx, [ 4 * r9]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0x1 
mov [ rsp - 0x60 ], r14
shlx r14, [ rsi + 0x30 ], rdx
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r14
mulx r14, r15, r8
imul rdx, [ rsi + 0x40 ], 0x2
mov [ rsp - 0x38 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r14
mulx r14, rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r10
mulx r10, r15, r8
mov rdx, rbp
mov [ rsp - 0x10 ], rax
mulx rax, rbp, [ rsi + 0x40 ]
mov [ rsp - 0x8 ], rax
imul rax, [ rsi + 0x10 ], 0x2
mov [ rsp + 0x0 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], rax
mov [ rsp + 0x10 ], r13
mulx r13, rax, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], rax
mulx rax, r13, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], rax
mov [ rsp + 0x30 ], r13
mulx r13, rax, rcx
mov rdx, r8
mov [ rsp + 0x38 ], r12
mulx r12, r8, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r12
mov r12, 0x2 
mov [ rsp + 0x48 ], r8
shlx r8, [ rsi + 0x30 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], rbx
mulx rbx, r14, rdx
mov rdx, r8
mov [ rsp + 0x60 ], rbx
mulx rbx, r8, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
xchg rdx, r12
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r13
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, r12
mov [ rsp + 0x88 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r8
mov r8, rdx
shl r8, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], r8
mulx r8, rax, r11
xor rdx, rdx
adox rax, r14
adox rbx, r8
adcx r15, r12
adcx r13, r10
mov rdx, [ rsp + 0xa0 ]
mulx r10, r11, [ rsi + 0x10 ]
xor r14, r14
adox r15, [ rsp + 0x98 ]
adox r13, [ rsp + 0x80 ]
mov r12, [ rsp + 0x90 ]
mov r8, r12
adcx r8, [ rsp + 0x58 ]
mov [ rsp + 0xa8 ], r10
mov r10, [ rsp + 0x88 ]
adcx r10, [ rsp + 0x50 ]
xchg rdx, rcx
mulx r14, r12, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], r10
mov r10, r12
add r10, [ rsp + 0x78 ]
adcx r14, [ rsp + 0x70 ]
mov [ rsp + 0xb8 ], r8
mulx r8, r12, [ rsi + 0x10 ]
test al, al
adox rax, r12
adox r8, rbx
xchg rdx, r9
mulx r12, rbx, [ rsi + 0x8 ]
adcx rax, rbx
adcx r12, r8
mulx rbx, r8, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r11
xor r11, r11
adox rax, [ rsp + 0x38 ]
adox r12, [ rsp + 0x10 ]
adcx r10, r8
adcx rbx, r14
mulx r8, r14, [ rsi + 0x10 ]
imul r11, [ rsi + 0x8 ], 0x2
mov [ rsp + 0xc8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r10
mov [ rsp + 0xd8 ], r12
mulx r12, r10, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], r12
mulx r12, r11, rdx
xor rdx, rdx
adox r15, r14
adox r8, r13
mov r13, 0x3ffffffffffffff 
mov r14, rax
and r14, r13
adox r15, r10
adox r8, [ rsp + 0xe0 ]
mov r10, [ rsp + 0xd8 ]
shrd rax, r10, 58
shr r10, 58
mov r13, r11
mov [ rsp + 0xe8 ], r14
xor r14, r14
adox r13, [ rsp + 0xd0 ]
adox r12, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, [ rsp + 0x8 ]
adcx r15, rax
adcx r10, r8
xor rdx, rdx
adox r13, r11
adox r14, r12
mov r8, r15
shrd r8, r10, 58
shr r10, 58
add r13, r8
adcx r10, r14
mov rax, [ rsi + 0x20 ]
mov r12, rax
shl r12, 0x1
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, r12
mov rdx, [ rsi + 0x38 ]
lea r14, [rdx + rdx]
mov rdx, r12
mulx r8, r12, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], rax
mov [ rsp + 0x100 ], r8
mulx r8, rax, rdi
mov rdx, r14
mov [ rsp + 0x108 ], r12
mulx r12, r14, [ rsi + 0x38 ]
mov [ rsp + 0x110 ], r12
mov [ rsp + 0x118 ], r14
mulx r14, r12, [ rsi + 0x0 ]
mov [ rsp + 0x120 ], r14
mov r14, 0x3ffffffffffffff 
mov [ rsp + 0x128 ], r12
mov r12, r13
and r12, r14
shrd r13, r10, 58
shr r10, 58
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], r12
mov [ rsp + 0x138 ], r10
mulx r10, r12, r11
mov rdx, r11
mov [ rsp + 0x140 ], r13
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, 0x3ffffffffffffff 
and r15, rdx
mov rdx, r12
adox rdx, [ rsp + 0x0 ]
adox r10, [ rsp - 0x8 ]
mov r12, rdx
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x148 ], r15
mov [ rsp + 0x150 ], r13
mulx r13, r15, [ rsi + 0x8 ]
adcx rax, [ rsp + 0x30 ]
adcx r8, [ rsp + 0x28 ]
test al, al
adox rax, [ rsp - 0x10 ]
adox r8, [ rsp - 0x18 ]
adcx rax, r15
adcx r13, r8
mov rdx, rcx
mulx r15, rcx, [ rsi + 0x0 ]
mov r8, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x158 ], r11
mov [ rsp + 0x160 ], r10
mulx r10, r11, rbx
test al, al
adox r11, [ rsp + 0x68 ]
adox r10, [ rsp + 0x60 ]
adcx rax, rcx
adcx r15, r13
xor rdx, rdx
adox rax, [ rsp + 0x140 ]
adox r15, [ rsp + 0x138 ]
mov rdx, r9
mulx r13, r9, [ rsi + 0x30 ]
mov rdx, 0x3a 
bzhi rcx, rax, rdx
adox r12, [ rsp - 0x20 ]
mov rdx, [ rsp + 0x160 ]
adox rdx, [ rsp - 0x28 ]
mov [ rsp + 0x168 ], rbp
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], rcx
xor rcx, rcx
adox r11, [ rsp + 0x158 ]
adox r10, [ rsp + 0x150 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], r12
mulx r12, rbp, rdx
mov rdx, rbx
mov [ rsp + 0x178 ], rcx
mulx rcx, rbx, [ rsi + 0x30 ]
adcx r9, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
mov rdx, r8
mov [ rsp + 0x180 ], r10
mulx r10, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, rbp
adox r12, r13
mov rbp, rbx
adcx rbp, [ rsp + 0x118 ]
adcx rcx, [ rsp + 0x110 ]
xor rbx, rbx
adox r9, r8
adox r10, r12
adcx r9, [ rsp + 0x108 ]
adcx r10, [ rsp + 0x100 ]
test al, al
adox rbp, [ rsp + 0xc0 ]
adox rcx, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0xf8 ]
adcx rcx, [ rsp + 0xf0 ]
add rbp, [ rsp + 0x48 ]
adcx rcx, [ rsp + 0x40 ]
shrd rax, r15, 58
shr r15, 58
xor rdx, rdx
adox r9, rax
adox r15, r10
adcx r11, [ rsp - 0x30 ]
mov rbx, [ rsp + 0x180 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, rdi
mulx r13, rdi, [ rsi + 0x8 ]
mov r8, rdi
add r8, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x178 ]
mov r12, r9
shrd r12, r15, 58
shr r15, 58
xor r10, r10
adox r8, [ rsp + 0x128 ]
adox r13, [ rsp + 0x120 ]
mov rax, 0x3ffffffffffffff 
and r9, rax
adox rbp, r12
adox r15, rcx
mov rcx, rbp
shrd rcx, r15, 58
shr r15, 58
and rbp, rax
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r9
mov [ rdi + 0x28 ], rbp
adox r11, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
adcx r11, rcx
adcx r15, rbx
mov r12, r11
shrd r12, r15, 58
shr r15, 58
xor r9, r9
adox r8, r12
adox r15, r13
mov r10, r8
shrd r10, r15, 58
shr r15, 58
and r11, rax
mulx rcx, r13, [ rsi + 0x10 ]
mov [ rdi + 0x30 ], r11
mov rdx, r13
adox rdx, [ rsp + 0xb8 ]
adox rcx, [ rsp + 0xb0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, rbx, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r11, r14
adcx rbp, r11
adcx r13, rcx
xor rdx, rdx
adox rbp, rbx
adox r12, r13
adcx rbp, r10
adcx r15, r12
mov r9, rbp
shrd r9, r15, 57
shr r15, 57
xor r14, r14
adox r9, [ rsp + 0xe8 ]
adox r15, r14
mov rdx, r9
shrd rdx, r15, 58
add rdx, [ rsp + 0x148 ]
mov r10, 0x1ffffffffffffff 
and rbp, r10
and r9, rax
mov rcx, rdx
shr rcx, 58
and rdx, rax
add rcx, [ rsp + 0x130 ]
mov [ rdi + 0x10 ], rcx
and r8, rax
mov [ rdi + 0x40 ], rbp
mov [ rdi + 0x8 ], rdx
mov [ rdi + 0x38 ], r8
mov [ rdi + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 520
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2171
; seed 1734130924406055 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2440871 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=181, initial num_batches=31): 101193 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.04145774192900813
; number reverted permutation / tried permutation: 70396 / 89926 =78.282%
; number reverted decision / tried decision: 63229 / 90073 =70.198%
; validated in 1.443s
