SECTION .text
	GLOBAL fiat_p521_carry_mul
fiat_p521_carry_mul:
sub rsp, 736
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, 0x1 
shlx rcx, [ rax + 0x10 ], rdx
mov rdx, [ rax + 0x8 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x40 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
shl rbx, 0x1
mov rdx, rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
shl r15, 0x1
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [rdx + rdx]
mov rdx, 0x1 
mov [ rsp - 0x48 ], r14
shlx r14, [ rax + 0x28 ], rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r11
mulx r11, r13, r12
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r11
mulx r11, r10, r14
mov rdx, r15
mov [ rsp - 0x20 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x38 ]
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r9
mulx r9, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r10
mulx r10, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r9
mulx r9, r10, r11
mov rdx, r14
mov [ rsp + 0x20 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], r10
mov [ rsp + 0x38 ], rbp
mulx rbp, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], r10
mulx r10, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x50 ], r10
mov [ rsp + 0x58 ], rbp
mulx rbp, r10, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], rbp
mov [ rsp + 0x68 ], r10
mulx r10, rbp, [ rsi + 0x38 ]
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0x70 ], r10
mov [ rsp + 0x78 ], rbp
mulx rbp, r10, r12
mov rdx, 0x1 
mov [ rsp + 0x80 ], rbp
shlx rbp, [ rax + 0x20 ], rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], rbx
mulx rbx, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r10
mulx r10, rbx, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r13
mov [ rsp + 0xb0 ], r15
mulx r15, r13, r12
mov rdx, [ rsi + 0x40 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], r13
mulx r13, r15, rdi
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0xc8 ], r8
mulx r8, rdi, rcx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r14
mov [ rsp + 0xd8 ], r10
mulx r10, r14, r11
xor rdx, rdx
adox r15, rdi
adox r8, r13
mov rdx, r11
mulx r13, r11, [ rsi + 0x38 ]
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe0 ], r10
mov [ rsp + 0xe8 ], r14
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, 0x1 
mov [ rsp + 0xf0 ], r13
shlx r13, [ rax + 0x18 ], rdx
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0xf8 ], r11
lea r11, [rdx + rdx]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x100 ], r14
mov [ rsp + 0x108 ], r10
mulx r10, r14, r11
mov rdx, r11
mov [ rsp + 0x110 ], r10
mulx r10, r11, [ rsi + 0x18 ]
xchg rdx, r13
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], r11
mulx r11, r10, [ rsi + 0x30 ]
adcx r15, r10
adcx r11, r8
mulx r10, r8, [ rsi + 0x40 ]
xchg rdx, rcx
mov [ rsp + 0x128 ], r14
mov [ rsp + 0x130 ], r11
mulx r11, r14, [ rsi + 0x40 ]
mov rdx, [ rsi + 0x38 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], rbx
mulx rbx, r15, rcx
test al, al
adox r14, r15
adox rbx, r11
mov rdx, r9
mulx rcx, r9, [ rsi + 0x30 ]
xchg rdx, rbp
mulx r15, r11, [ rsi + 0x38 ]
adcx r8, r11
adcx r15, r10
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], r15
mulx r15, r11, r13
xor rdx, rdx
adox r14, [ rsp + 0x140 ]
adox rbx, [ rsp + 0xd8 ]
adcx r14, [ rsp + 0xd0 ]
adcx rbx, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r11
mulx r11, r15, r10
mov rdx, r15
mov [ rsp + 0x160 ], rbx
xor rbx, rbx
adox rdx, [ rsp + 0x138 ]
adox r11, [ rsp + 0x130 ]
xchg rdx, rbp
mulx rbx, r15, [ rsi + 0x20 ]
adcx rbp, r15
adcx rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx r15, r11, r13
test al, al
adox rbp, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0xa8 ]
adcx rbp, r11
adcx r15, rbx
xor rdx, rdx
adox rbp, [ rsp + 0xc0 ]
adox r15, [ rsp + 0xb8 ]
adcx rbp, [ rsp + 0x108 ]
adcx r15, [ rsp + 0x100 ]
mov rdx, rdi
mulx r11, rdi, [ rsi + 0x40 ]
mov rbx, rbp
shrd rbx, r15, 58
shr r15, 58
mov [ rsp + 0x168 ], r15
mov [ rsp + 0x170 ], rbx
mulx rbx, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox rdi, [ rsp + 0x128 ]
adox r11, [ rsp + 0x110 ]
adcx r8, r9
adcx rcx, [ rsp + 0x148 ]
test al, al
adox rdi, [ rsp + 0x90 ]
adox r11, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x178 ], r11
mulx r11, r9, [ rax + 0x0 ]
adcx r8, [ rsp + 0x30 ]
adcx rcx, [ rsp + 0x28 ]
mov rdx, r13
mov [ rsp + 0x180 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
test al, al
adox r8, r13
adox rdi, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r11
mulx r11, r13, r12
adcx r14, r15
adcx rbx, [ rsp + 0x160 ]
xor rdx, rdx
adox r14, [ rsp + 0x120 ]
adox rbx, [ rsp + 0x118 ]
mov rdx, r12
mulx r15, r12, [ rsi + 0x10 ]
adcx r14, r12
adcx r15, rbx
mov rbx, 0x3ffffffffffffff 
and rbp, rbx
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x190 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
adox r8, r13
adox r11, rdi
adcx r8, r9
adcx r11, [ rsp + 0x188 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r9, [ rax + 0x0 ]
xor rdx, rdx
adox r14, r9
adox rdi, r15
adcx r8, [ rsp + 0x20 ]
adcx r11, [ rsp - 0x8 ]
add r8, rbx
adcx rbp, r11
mov rdx, [ rsi + 0x40 ]
mulx r15, r13, r10
mov rdx, [ rax + 0x8 ]
mulx rbx, r10, [ rsi + 0x0 ]
add r14, r10
adcx rbx, rdi
mov rdx, [ rsp + 0x68 ]
add rdx, [ rsp + 0xf8 ]
mov r9, [ rsp + 0x60 ]
adcx r9, [ rsp + 0xf0 ]
test al, al
adox r14, [ rsp + 0x170 ]
adox rbx, [ rsp + 0x168 ]
mov rdi, r14
shrd rdi, rbx, 58
shr rbx, 58
xchg rdx, r12
mulx r10, r11, [ rsi + 0x20 ]
test al, al
adox r8, rdi
adox rbx, rbp
adcx r13, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x18 ]
mulx rdi, rbp, [ rsi + 0x38 ]
xor rdx, rdx
adox r13, [ rsp + 0xe8 ]
adox r15, [ rsp + 0xe0 ]
mov rdx, 0x3a 
mov [ rsp + 0x198 ], rbx
bzhi rbx, r14, rdx
adox r13, [ rsp + 0x158 ]
adox r15, [ rsp + 0x150 ]
mov rdx, rcx
mulx r14, rcx, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], rbx
xor rbx, rbx
adox r12, rcx
adox r14, r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a8 ], r8
mov [ rsp + 0x1b0 ], rbx
mulx rbx, r8, [ rax + 0x10 ]
mov rdx, r9
mov [ rsp + 0x1b8 ], rbx
mulx rbx, r9, [ rsi + 0x40 ]
adcx r9, rbp
adcx rdi, rbx
add r12, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1c0 ], r14
mov [ rsp + 0x1c8 ], r12
mulx r12, r14, [ rsi + 0x20 ]
add r13, r11
adcx r10, r15
xor rdx, rdx
adox r13, rcx
adox r10, [ rsp + 0x1b0 ]
adcx r9, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x98 ]
xor r11, r11
adox r13, rbp
adox rbx, r10
mov rdx, [ rax + 0x20 ]
mulx rcx, r15, [ rsi + 0x0 ]
adcx r13, r8
adcx rbx, [ rsp + 0x1b8 ]
mov rdx, [ rax + 0x18 ]
mulx rbp, r8, [ rsi + 0x0 ]
test al, al
adox r13, r8
adox rbp, rbx
mov rdx, [ rsp + 0x198 ]
mov r10, [ rsp + 0x1a8 ]
shrd r10, rdx, 58
shr rdx, 58
xor rbx, rbx
adox r13, r10
adox rdx, rbp
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, r8, [ rax + 0x8 ]
adcx r9, r8
adcx rbp, rdi
mov rdx, [ rax + 0x8 ]
mulx r10, rdi, [ rsi + 0x18 ]
test al, al
adox r9, r14
adox r12, rbp
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ rax + 0x10 ]
mov rdx, [ rsp + 0x58 ]
mov rbp, rdx
adcx rbp, [ rsp + 0x1c8 ]
mov [ rsp + 0x1d0 ], r12
mov r12, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x1c0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d8 ], r9
mulx r9, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, rdi
adox r10, r12
mov rdx, [ rax + 0x28 ]
mulx r12, rdi, [ rsi + 0x0 ]
adcx rbp, r14
adcx r8, r10
test al, al
adox rbp, [ rsp - 0x30 ]
adox r8, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1e0 ], r12
mov [ rsp + 0x1e8 ], rdi
mulx rdi, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f0 ], rdi
mov [ rsp + 0x1f8 ], r12
mulx r12, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x200 ], r12
mov [ rsp + 0x208 ], rdi
mulx rdi, r12, [ rsi + 0x28 ]
mov rdx, r13
shrd rdx, r11, 58
shr r11, 58
add rbp, r15
adcx rcx, r8
mov r15, r12
test al, al
adox r15, [ rsp + 0x180 ]
adox rdi, [ rsp + 0x178 ]
adcx rbp, rdx
adcx r11, rcx
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x210 ], r9
mulx r9, rcx, [ rsi + 0x20 ]
mov rdx, 0x3a 
mov [ rsp + 0x218 ], rbx
bzhi rbx, rbp, rdx
adox r15, rcx
adox r9, rdi
xor rdi, rdi
adox r15, r8
adox r12, r9
adcx r15, r14
adcx r10, r12
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x20 ], rbx
mov rdx, [ rax + 0x28 ]
mulx rcx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mulx r9, rbx, [ rax + 0x10 ]
mov rdx, [ rsp + 0x88 ]
xor r12, r12
adox rdx, [ rsp + 0x8 ]
mov rdi, [ rsp + 0x80 ]
adox rdi, [ rsp + 0x0 ]
adcx rdx, [ rsp + 0x218 ]
adcx rdi, [ rsp + 0x210 ]
add rdx, rbx
adcx r9, rdi
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx r12, rdi, [ rsi + 0x8 ]
test al, al
adox r15, rdi
adox r12, r10
adcx rbx, [ rsp + 0x208 ]
adcx r9, [ rsp + 0x200 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, [ rax + 0x28 ]
shrd rbp, r11, 58
shr r11, 58
mov rdx, [ rsp + 0x1f8 ]
mov r14, rdx
test al, al
adox r14, [ rsp + 0x1d8 ]
mov [ rsp + 0x220 ], rdi
mov rdi, [ rsp + 0x1f0 ]
adox rdi, [ rsp + 0x1d0 ]
adcx r14, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
add r15, [ rsp + 0x1e8 ]
adcx r12, [ rsp + 0x1e0 ]
mov rdx, [ rax + 0x38 ]
mov [ rsp + 0x228 ], r10
mov [ rsp + 0x230 ], r9
mulx r9, r10, [ rsi + 0x0 ]
test al, al
adox r15, rbp
adox r11, r12
mov rdx, [ rax + 0x20 ]
mulx r12, rbp, [ rsi + 0x18 ]
adcx r14, r8
adcx rcx, rdi
xor rdx, rdx
adox rbx, rbp
adox r12, [ rsp + 0x230 ]
mov r8, r15
shrd r8, r11, 58
shr r11, 58
mov rdx, [ rax + 0x0 ]
mulx rbp, rdi, [ rsi + 0x40 ]
test al, al
adox rdi, [ rsp + 0x78 ]
adox rbp, [ rsp + 0x70 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x238 ], r9
mov [ rsp + 0x240 ], r10
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x248 ], rbp
mov [ rsp + 0x250 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
adcx r14, r9
adcx r10, rcx
mov rdx, [ rax + 0x40 ]
mulx r9, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, r8
adox r11, r10
mov r8, r14
shrd r8, r11, 58
shr r11, 58
test al, al
adox rbx, [ rsp + 0x228 ]
adox r12, [ rsp + 0x220 ]
adcx rbx, [ rsp + 0x18 ]
adcx r12, [ rsp + 0x10 ]
mov r10, rbp
test al, al
adox r10, [ rsp + 0x250 ]
adox rdi, [ rsp + 0x248 ]
adcx rbx, [ rsp + 0x240 ]
adcx r12, [ rsp + 0x238 ]
test al, al
adox rbx, r8
adox r11, r12
mov rdx, [ rax + 0x20 ]
mulx r8, rbp, [ rsi + 0x20 ]
mov rdx, 0x3ffffffffffffff 
mov r12, rbx
and r12, rdx
and r14, rdx
shrd rbx, r11, 58
shr r11, 58
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x30 ], r14
test al, al
adox r10, [ rsp + 0x48 ]
adox rdi, [ rsp + 0x40 ]
adcx r10, rbp
adcx r8, rdi
mov rbp, rdx
mov rdx, [ rax + 0x28 ]
mulx rdi, r14, [ rsi + 0x18 ]
test al, al
adox r10, r14
adox rdi, r8
mov rdx, [ rax + 0x38 ]
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x258 ], r11
mulx r11, rbp, [ rax + 0x30 ]
adcx r10, rbp
adcx r11, rdi
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x38 ], r12
add r10, r8
adcx r14, r11
test al, al
adox r10, rcx
adox r9, r14
adcx r10, rbx
adcx r9, [ rsp + 0x258 ]
mov rcx, r10
shrd rcx, r9, 57
shr r9, 57
mov r12, 0x3ffffffffffffff 
and r13, r12
mov rbx, 0x39 
bzhi rdi, r10, rbx
adox rcx, [ rsp + 0x190 ]
mov r8, 0x0 
adox r9, r8
mov rbp, rcx
shrd rbp, r9, 58
and r15, r12
and rcx, r12
add rbp, [ rsp + 0x1a0 ]
mov r11, rbp
shr r11, 58
mov r14, [ rsp + 0x1a8 ]
and r14, r12
and rbp, r12
mov [ rdx + 0x28 ], r15
lea r11, [ r11 + r14 ]
mov [ rdx + 0x10 ], r11
mov [ rdx + 0x8 ], rbp
mov [ rdx + 0x18 ], r13
mov [ rdx + 0x0 ], rcx
mov [ rdx + 0x40 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 736
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1667
; seed 2234042592805592 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7235277 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=67, initial num_batches=31): 138740 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01917549252088068
; number reverted permutation / tried permutation: 53572 / 89642 =59.762%
; number reverted decision / tried decision: 38862 / 90357 =43.009%
; validated in 3.608s
