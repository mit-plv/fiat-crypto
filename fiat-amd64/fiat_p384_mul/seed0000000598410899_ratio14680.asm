SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 648
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r12
mulx r12, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], rbp
mulx rbp, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r14
mulx r14, rbp, [ rsi + 0x20 ]
xor rdx, rdx
adox r10, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r10
mulx r10, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r13
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], r10
mulx r10, r15, [ rax + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r14
mulx r14, r10, r9
mov r14, 0xffffffff00000000 
mov rdx, r10
mov [ rsp + 0x20 ], rdi
mulx rdi, r10, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x28 ], r12
mov [ rsp + 0x30 ], r15
mulx r15, r12, r14
mov r14, 0xffffffff 
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], r12
mulx r12, r15, r14
adcx r10, r12
setc r12b
clc
adcx rcx, rbx
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x48 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x50 ], r12b
mov [ rsp + 0x58 ], r10
mulx r10, r12, [ rsi + 0x0 ]
adcx r12, r8
adcx r14, r10
adcx rbp, rdi
mov rdx, [ rax + 0x10 ]
mulx rdi, r8, [ rsi + 0x20 ]
adox r8, r11
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rax + 0x28 ]
adcx r11, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r8
mulx r8, r13, [ rax + 0x18 ]
setc dl
clc
adcx r15, r9
mov r15, 0xfffffffffffffffe 
xchg rdx, r15
mov [ rsp + 0x68 ], r11
mulx r11, r9, rbx
adcx rcx, [ rsp + 0x58 ]
adox r13, rdi
seto bl
movzx rdi, byte [ rsp + 0x50 ]
mov rdx, 0x0 
dec rdx
adox rdi, rdx
adox r9, [ rsp + 0x48 ]
movzx rdi, r15b
lea rdi, [ rdi + r10 ]
adcx r9, r12
adox r11, [ rsp + 0x40 ]
adcx r11, r14
mov rdx, [ rsi + 0x28 ]
mulx r14, r12, [ rax + 0x0 ]
mov rdx, [ rsp + 0x40 ]
mov r10, rdx
adox r10, [ rsp + 0x38 ]
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], r13
mulx r13, r12, [ rax + 0x18 ]
adox r15, [ rsp + 0x38 ]
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x80 ], r13
mov r13, 0x0 
adox rdx, r13
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, -0x2 
inc rdx
adox rcx, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r11
mulx r11, r13, [ rax + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r8
mulx r8, r9, rcx
adcx r10, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r8, [ rax + 0x8 ]
setc dl
clc
adcx rdi, r14
mov r14, 0xffffffff 
xchg rdx, r14
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r10
mulx r10, rdi, r9
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r10
mulx r10, rdi, [ rsi + 0x18 ]
adcx r13, r15
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], r13
mulx r13, r15, r9
adcx r12, r11
setc r11b
clc
adcx r8, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0xe0 ], r11b
mov [ rsp + 0xe8 ], r12
mulx r12, r11, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], r13
mulx r13, r8, r9
adcx rdi, rbp
adcx r10, [ rsp + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x100 ], r10
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x108 ], rdi
setc dil
clc
mov [ rsp + 0x110 ], rbp
mov rbp, -0x1 
movzx rbx, bl
adcx rbx, rbp
adcx rdx, [ rsp + 0x18 ]
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x118 ], dil
mulx rdi, rbp, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x8 ]
adcx rdx, [ rsp + 0x0 ]
mov [ rsp + 0x120 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x128 ], r13
mov [ rsp + 0x130 ], r8
mulx r8, r13, [ rsi + 0x10 ]
setc dl
clc
adcx rbp, r10
adcx rdi, [ rsp - 0x8 ]
adcx r11, [ rsp - 0x20 ]
adcx r13, r12
mov r12b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x138 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
adcx r10, r8
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x140 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x30 ]
clc
adcx rdx, [ rsp + 0x10 ]
mov [ rsp + 0x148 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], r11
mulx r11, r13, [ rax + 0x18 ]
adcx r8, [ rsp - 0x40 ]
adcx r13, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], rdi
mulx rdi, rbx, [ rax + 0x20 ]
adcx rbx, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], rbp
mulx rbp, r11, [ rax + 0x28 ]
adcx r11, rdi
adox r10, [ rsp + 0xa8 ]
adox r8, [ rsp + 0xa0 ]
mov rdx, 0x0 
adcx rbp, rdx
mov rdi, [ rsp + 0x90 ]
clc
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx rdi, [ rsp + 0x68 ]
mov r14, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x98 ]
adox r13, [ rsp + 0xc0 ]
adox rbx, rdi
movzx rdi, r12b
mov rdx, [ rsp - 0x48 ]
lea rdi, [ rdi + rdx ]
adox r11, r14
mov rdx, 0xffffffff00000000 
mulx r14, r12, r9
setc r9b
clc
adcx r12, [ rsp + 0xd0 ]
movzx rdx, r9b
adox rdx, rbp
adcx r15, r14
mov rbp, [ rsp + 0x130 ]
mov r9, rbp
adcx r9, [ rsp + 0xf8 ]
mov r14, rbp
adcx r14, [ rsp + 0x128 ]
adcx rbp, [ rsp + 0x128 ]
mov [ rsp + 0x170 ], rdi
seto dil
mov [ rsp + 0x178 ], rdx
mov rdx, -0x2 
inc rdx
adox rcx, [ rsp + 0xc8 ]
adox r12, r10
adox r15, r8
adox r9, r13
adox r14, rbx
adox rbp, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, [ rax + 0x20 ]
mov rdx, [ rsp + 0x128 ]
mov r8, 0x0 
adcx rdx, r8
clc
adcx r12, [ rsp + 0x110 ]
adox rdx, [ rsp + 0x178 ]
adcx r15, [ rsp + 0x168 ]
adcx r9, [ rsp + 0x160 ]
adcx r14, [ rsp + 0x158 ]
movzx r13, dil
adox r13, r8
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r11, [ rax + 0x28 ]
adcx rbp, [ rsp + 0x150 ]
adcx rbx, [ rsp + 0x148 ]
movzx rdx, byte [ rsp + 0x118 ]
dec r8
adox rdx, r8
adox rcx, [ rsp - 0x28 ]
adcx r13, [ rsp + 0x140 ]
mov rdx, 0x100000001 
mov [ rsp + 0x180 ], rdi
mulx rdi, r8, r12
mov rdi, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp + 0x188 ], rcx
mulx rcx, rdi, r8
mov rdx, 0xffffffff 
mov [ rsp + 0x190 ], r13
mov [ rsp + 0x198 ], rbx
mulx rbx, r13, r8
adox r11, r10
seto r10b
mov rdx, -0x2 
inc rdx
adox r13, r12
setc r13b
clc
adcx rdi, rbx
mov r12, 0xfffffffffffffffe 
mov rdx, r12
mulx rbx, r12, r8
adcx r12, rcx
adox rdi, r15
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r8
adox r12, r9
mov r9, r15
adcx r9, rbx
adox r9, r14
mov r14, r15
adcx r14, rcx
adcx r15, rcx
mov r8, 0x0 
adcx rcx, r8
clc
adcx rdi, [ rsp - 0x38 ]
mov rbx, 0x100000001 
mov rdx, rbx
mulx r8, rbx, rdi
adox r14, rbp
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx rbp, r8, rbx
adox r15, [ rsp + 0x198 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1a0 ], r11
mov byte [ rsp + 0x1a8 ], r10b
mulx r10, r11, rbx
adox rcx, [ rsp + 0x190 ]
adcx r12, [ rsp + 0xf0 ]
adcx r9, [ rsp + 0x108 ]
movzx rdx, r13b
mov [ rsp + 0x1b0 ], rcx
mov rcx, 0x0 
adox rdx, rcx
adcx r14, [ rsp + 0x100 ]
adcx r15, [ rsp + 0x188 ]
mov r13, 0xffffffff 
xchg rdx, r13
mov [ rsp + 0x1b8 ], r15
mulx r15, rcx, rbx
mov rdx, -0x2 
inc rdx
adox r8, r15
adox r11, rbp
mov rbp, 0xffffffffffffffff 
mov rdx, rbx
mulx r15, rbx, rbp
setc dl
clc
adcx rcx, rdi
adcx r8, r12
mov rcx, rbx
adox rcx, r10
mov rdi, rbx
adox rdi, r15
adox rbx, r15
adcx r11, r9
movzx r10, byte [ rsp + 0x1a8 ]
mov r12, [ rsp + 0x180 ]
lea r10, [ r10 + r12 ]
mov r12, [ rsp + 0x1b0 ]
seto r9b
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r12, [ rsp + 0x1a0 ]
movzx rdx, r9b
lea rdx, [ rdx + r15 ]
adox r10, r13
seto r13b
inc rbp
adox r8, [ rsp - 0x10 ]
adox r11, [ rsp - 0x18 ]
adcx rcx, r14
adcx rdi, [ rsp + 0x1b8 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx r9, r15, r8
adox rcx, [ rsp + 0x60 ]
adcx rbx, r12
adcx r14, r10
adox rdi, [ rsp + 0x78 ]
adox rbx, [ rsp + 0x120 ]
movzx r9, r13b
adcx r9, rbp
adox r14, [ rsp + 0x138 ]
mov r12, 0xffffffff00000000 
mov rdx, r12
mulx r13, r12, r15
mov r10, 0xffffffff 
mov rdx, r15
mulx rbp, r15, r10
clc
adcx r12, rbp
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0x1c0 ], r14
mulx r14, r10, rbp
adcx r10, r13
seto r13b
mov rbp, -0x2 
inc rbp
adox r15, r8
mov r15, 0xffffffffffffffff 
mulx rbp, r8, r15
mov rdx, r8
adcx rdx, r14
adox r12, r11
mov r11, r8
adcx r11, rbp
adcx r8, rbp
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1c8 ], r8
mulx r8, r15, [ rsi + 0x28 ]
adox r10, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox r12, [ rsp + 0x70 ]
setc cl
clc
mov [ rsp + 0x1d0 ], r8
mov r8, -0x1 
movzx r13, r13b
adcx r13, r8
adcx r9, [ rsp + 0x170 ]
adox r10, [ rsp + 0xb8 ]
mov r13, 0x100000001 
xchg rdx, r12
mov [ rsp + 0x1d8 ], r10
mulx r10, r8, r13
setc r10b
clc
mov r13, -0x1 
movzx r12, r12b
adcx r12, r13
adcx rdi, r14
adcx r11, rbx
mov rbx, 0xffffffff00000000 
xchg rdx, r8
mulx r12, r14, rbx
mov r13, [ rsp + 0x1c8 ]
adcx r13, [ rsp + 0x1c0 ]
adox rdi, [ rsp + 0xd8 ]
adox r11, [ rsp + 0xe8 ]
mov rbx, 0xffffffff 
mov [ rsp + 0x1e0 ], r11
mov [ rsp + 0x1e8 ], rdi
mulx rdi, r11, rbx
movzx rbx, cl
lea rbx, [ rbx + rbp ]
adcx rbx, r9
movzx rbp, r10b
mov rcx, 0x0 
adcx rbp, rcx
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mulx rcx, r10, [ rsi + 0x28 ]
movzx rdx, byte [ rsp + 0xe0 ]
clc
mov [ rsp + 0x1f0 ], rbp
mov rbp, -0x1 
adcx rdx, rbp
adcx r10, [ rsp + 0x80 ]
adox r10, r13
adcx r15, rcx
mov rdx, 0xffffffffffffffff 
mulx rcx, r13, r9
mov rbp, 0xfffffffffffffffe 
mov rdx, r9
mov [ rsp + 0x1f8 ], r15
mulx r15, r9, rbp
setc dl
clc
adcx r14, rdi
adcx r9, r12
mov r12, r13
adcx r12, r15
mov rdi, r13
adcx rdi, rcx
adcx r13, rcx
setc r15b
clc
adcx r11, r8
movzx r11, dl
mov r8, [ rsp + 0x1d0 ]
lea r11, [ r11 + r8 ]
adcx r14, [ rsp + 0x1d8 ]
adcx r9, [ rsp + 0x1e8 ]
adcx r12, [ rsp + 0x1e0 ]
adcx rdi, r10
adox rbx, [ rsp + 0x1f8 ]
movzx r8, r15b
lea r8, [ r8 + rcx ]
adox r11, [ rsp + 0x1f0 ]
adcx r13, rbx
adcx r8, r11
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov rdx, r14
mov rcx, 0xffffffff 
sub rdx, rcx
mov r15, r9
mov rbx, 0xffffffff00000000 
sbb r15, rbx
mov r11, r12
sbb r11, rbp
mov rbx, rdi
mov rbp, 0xffffffffffffffff 
sbb rbx, rbp
mov rcx, r13
sbb rcx, rbp
mov [ rsp + 0x200 ], r15
mov r15, r8
sbb r15, rbp
movzx rbp, r10b
sbb rbp, 0x00000000
cmovc r11, r12
cmovc rcx, r13
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x20 ], rcx
cmovc rbx, rdi
cmovc rdx, r14
mov [ rbp + 0x0 ], rdx
mov [ rbp + 0x10 ], r11
mov r14, [ rsp + 0x200 ]
cmovc r14, r9
cmovc r15, r8
mov [ rbp + 0x28 ], r15
mov [ rbp + 0x18 ], rbx
mov [ rbp + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 648
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4680
; seed 2692810032476956 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4713815 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=59, initial num_batches=31): 130838 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027756286574674653
; number reverted permutation / tried permutation: 64602 / 90268 =71.567%
; number reverted decision / tried decision: 47152 / 89731 =52.548%
; validated in 37.704s
