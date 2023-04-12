SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 736
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, 0x100000001 
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r14
mulx r14, r9, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r14
mulx r14, r13, r9
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r12
mulx r12, rbx, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], rdi
mulx rdi, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], rdi
mulx rdi, rbp, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r15
mulx r15, rbp, [ rax + 0x18 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rbp
mulx rbp, r15, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r8
mulx r8, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], r9
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], r8
mulx r8, r9, [ rsi + 0x18 ]
test al, al
adox rbx, rdi
adox r15, r12
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r9
mulx r9, r8, [ rax + 0x8 ]
mov rdx, r13
adox rdx, rbp
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, r13
adox rdx, r14
adox r13, r14
adcx r9, r11
mov r11, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r12
mulx r12, rdi, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r14, rdx
adcx rcx, r8
adcx rdi, [ rsp + 0x40 ]
adcx r12, [ rsp + 0x28 ]
mov r8, [ rsp - 0x8 ]
adcx r8, [ rsp - 0x10 ]
mov [ rsp + 0x98 ], r14
mov r14, -0x3 
inc r14
adox r10, [ rsp + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0xa0 ], r14
mov r14, 0x0 
adcx rdx, r14
adox rbx, r9
adox r15, rcx
adox rbp, rdi
adox r11, r12
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mulx rdi, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
clc
adcx r10, rbx
adox r13, r8
mov rdx, 0x100000001 
mulx rbx, r8, r10
mov rbx, 0xffffffff00000000 
mov rdx, r8
mov [ rsp + 0xb8 ], r13
mulx r13, r8, rbx
mov rbx, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xc0 ], r11
mov [ rsp + 0xc8 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd0 ], rbp
mov [ rsp + 0xd8 ], r13
mulx r13, rbp, [ rsi + 0x8 ]
adox r9, [ rsp + 0x98 ]
seto dl
mov [ rsp + 0xe0 ], r9
mov r9, -0x2 
inc r9
adox r12, [ rsp + 0xa0 ]
adcx r12, r15
adox r14, [ rsp + 0x18 ]
adox rbp, [ rsp + 0x10 ]
adox rdi, r13
adox r11, rcx
mov r15, 0xffffffff 
xchg rdx, rbx
mulx r13, rcx, r15
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0xe8 ], bl
mulx rbx, r15, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], r11
mulx r11, rbx, r9
seto dl
mov [ rsp + 0x100 ], rdi
mov rdi, -0x2 
inc rdi
adox rcx, r10
mov rcx, 0xfffffffffffffffe 
xchg rdx, r9
mulx rdi, r10, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox r8, r13
adox r10, [ rsp + 0xd8 ]
mov r13, rbx
adox r13, rdi
mov rdi, rbx
adox rdi, r11
adox rbx, r11
adcx r14, [ rsp + 0xc8 ]
mov rcx, 0x0 
adox r11, rcx
adcx rbp, [ rsp + 0xc0 ]
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r12, r8
seto dl
inc rcx
adox r15, r12
seto r8b
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r14, r10
adox r13, rbp
mov r10, [ rsp + 0xb8 ]
adcx r10, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsp + 0xe0 ]
adcx rdx, [ rsp + 0xf8 ]
adox rdi, r10
movzx r10, r9b
mov rcx, [ rsp + 0xd0 ]
lea r10, [ r10 + rcx ]
mov rcx, 0x100000001 
xchg rdx, r15
mov [ rsp + 0x108 ], rdi
mulx rdi, r9, rcx
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x110 ], r13
mulx r13, rcx, [ rsi + 0x20 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x118 ], r14
mov byte [ rsp + 0x120 ], r8b
mulx r8, r14, r9
movzx rdx, byte [ rsp + 0xe8 ]
adcx rdx, r10
adox rbx, r15
adox r11, rdx
mov r15, 0xffffffff 
mov rdx, r15
mulx r10, r15, r9
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x128 ], r11
setc r11b
clc
adcx rdx, [ rsp + 0xf0 ]
adcx rbp, [ rsp + 0x88 ]
mov [ rsp + 0x130 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], rbp
mulx rbp, r15, [ rsi + 0x20 ]
movzx rdx, r11b
mov [ rsp + 0x148 ], rbx
mov rbx, 0x0 
adox rdx, rbx
adcx r12, [ rsp + 0x38 ]
mov r11, -0x3 
inc r11
adox rcx, [ rsp - 0x20 ]
mov rbx, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x50 ]
adox r15, r13
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x150 ], r15
mulx r15, r11, [ rsi + 0x10 ]
adcx r11, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x158 ], rcx
mov [ rsp + 0x160 ], r13
mulx r13, rcx, [ rax + 0x28 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x168 ], r13
mov [ rsp + 0x170 ], r15
mulx r15, r13, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x178 ], r11
mov [ rsp + 0x180 ], rbx
mulx rbx, r11, r9
clc
adcx r14, r10
adcx r13, r8
mov r9, r11
adcx r9, r15
mov r8, r11
adcx r8, rbx
adox rbp, [ rsp + 0x8 ]
adcx r11, rbx
mov r10, [ rsp - 0x28 ]
adox r10, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x30 ]
mov r15, [ rsp + 0x148 ]
seto dl
mov [ rsp + 0x188 ], rcx
movzx rcx, byte [ rsp + 0x120 ]
mov [ rsp + 0x190 ], r10
mov r10, 0x0 
dec r10
adox rcx, r10
adox r15, [ rsp + 0x118 ]
mov rcx, [ rsp + 0x140 ]
adox rcx, [ rsp + 0x110 ]
adox r12, [ rsp + 0x108 ]
setc r10b
clc
adcx rdi, [ rsp + 0x138 ]
adcx r14, r15
adcx r13, rcx
mov rdi, [ rsp + 0x130 ]
adox rdi, [ rsp + 0x180 ]
mov r15b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], rbp
mulx rbp, rcx, [ rax + 0x20 ]
adcx r9, r12
adcx r8, rdi
mov rdx, [ rsp + 0x128 ]
adox rdx, [ rsp + 0x178 ]
adcx r11, rdx
mov r12, [ rsp + 0x160 ]
adox r12, [ rsp + 0x170 ]
movzx rdi, r10b
lea rdi, [ rdi + rbx ]
adcx rdi, r12
mov rdx, [ rax + 0x8 ]
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x1a0 ], r15b
mulx r15, r12, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x1a8 ], rdi
mov rdi, -0x2 
inc rdi
adox r14, [ rsp - 0x38 ]
movzx rdi, dl
mov [ rsp + 0x1b0 ], rbp
mov rbp, 0x0 
adcx rdi, rbp
clc
adcx rbx, [ rsp - 0x40 ]
adcx r12, r10
adcx r15, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0x68 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, r10, [ rsi + 0x18 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1b8 ], rdi
mov [ rsp + 0x1c0 ], rbp
mulx rbp, rdi, r14
mov rbp, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp + 0x1c8 ], r10
mulx r10, rdi, rbp
adox rbx, r13
mov r13, 0xffffffff 
mov [ rsp + 0x1d0 ], r10
mulx r10, rbp, r13
adox r12, r9
adox r15, r8
adox rcx, r11
mov r9, [ rsp + 0x1c8 ]
adcx r9, [ rsp + 0x1b0 ]
mov r8, [ rsp + 0x1c0 ]
mov r11, 0x0 
adcx r8, r11
mov r11, 0xffffffff00000000 
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r13, r11
clc
adcx r13, r10
adox r9, [ rsp + 0x1a8 ]
adox r8, [ rsp + 0x1b8 ]
seto r10b
mov r11, -0x2 
inc r11
adox rbp, r14
adox r13, rbx
mov rbp, 0xfffffffffffffffe 
mulx rbx, r14, rbp
adcx r14, rcx
adox r14, r12
mov rdx, rdi
adcx rdx, rbx
mov r12, rdi
adcx r12, [ rsp + 0x1d0 ]
adcx rdi, [ rsp + 0x1d0 ]
mov rcx, [ rsp + 0x1d0 ]
mov rbx, 0x0 
adcx rcx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, r11, [ rax + 0x0 ]
adox rbx, r15
adox r12, [ rsp + 0x1d8 ]
clc
adcx r13, [ rsp - 0x48 ]
adcx r14, [ rsp + 0x158 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1e0 ], rbp
mulx rbp, r15, r13
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp + 0x1e8 ], r11
mulx r11, rbp, r15
mov rdx, 0xffffffff 
mov [ rsp + 0x1f0 ], r11
mov [ rsp + 0x1f8 ], rbp
mulx rbp, r11, r15
adcx rbx, [ rsp + 0x150 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x200 ], rbx
mov [ rsp + 0x208 ], r14
mulx r14, rbx, r15
adcx r12, [ rsp + 0x198 ]
adox rdi, r9
adox rcx, r8
adcx rdi, [ rsp + 0x190 ]
adcx rcx, [ rsp + 0x188 ]
movzx r9, r10b
mov r8, 0x0 
adox r9, r8
movzx r10, byte [ rsp + 0x1a0 ]
mov r8, [ rsp + 0x168 ]
lea r10, [ r10 + r8 ]
mov r8, 0xfffffffffffffffe 
mov rdx, r15
mov [ rsp + 0x210 ], rcx
mulx rcx, r15, r8
mov rdx, -0x2 
inc rdx
adox r11, r13
adcx r10, r9
setc r11b
clc
adcx rbx, rbp
adox rbx, [ rsp + 0x208 ]
adcx r15, r14
adcx rcx, [ rsp + 0x1f8 ]
mov r13, [ rsp + 0x1f0 ]
mov rbp, r13
adcx rbp, [ rsp + 0x1f8 ]
adox r15, [ rsp + 0x200 ]
seto r14b
inc rdx
adox rbx, [ rsp + 0x1e8 ]
mov r9, 0x100000001 
mov rdx, r9
mulx r8, r9, rbx
mov r8, 0xffffffff 
mov rdx, r8
mov byte [ rsp + 0x218 ], r11b
mulx r11, r8, r9
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x220 ], r11
mov [ rsp + 0x228 ], r15
mulx r15, r11, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x230 ], r15
mov [ rsp + 0x238 ], r11
mulx r11, r15, r9
setc dl
clc
adcx r8, rbx
mov r8, r13
setc bl
clc
mov [ rsp + 0x240 ], r11
mov r11, -0x1 
movzx rdx, dl
adcx rdx, r11
adcx r8, [ rsp + 0x1f8 ]
mov rdx, 0x0 
adcx r13, rdx
clc
movzx r14, r14b
adcx r14, r11
adcx r12, rcx
adcx rbp, rdi
adcx r8, [ rsp + 0x210 ]
adcx r13, r10
mov rdi, [ rsp + 0x80 ]
setc r10b
clc
adcx rdi, [ rsp + 0x1e0 ]
mov rcx, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x28 ]
mulx r11, r14, [ rax + 0x18 ]
adcx r14, [ rsp + 0x58 ]
adcx r11, [ rsp + 0xb0 ]
adox rdi, [ rsp + 0x228 ]
adox rcx, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x248 ], r13
mulx r13, r12, [ rax + 0x28 ]
adox r14, rbp
adcx r12, [ rsp + 0xa8 ]
mov rdx, 0x0 
adcx r13, rdx
movzx rbp, r10b
movzx rdx, byte [ rsp + 0x218 ]
lea rbp, [ rbp + rdx ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x250 ], r13
mulx r13, r10, r9
clc
adcx r10, [ rsp + 0x220 ]
adox r11, r8
adcx r13, [ rsp + 0x238 ]
seto r9b
mov r8, 0x0 
dec r8
movzx rbx, bl
adox rbx, r8
adox rdi, r10
adox r13, rcx
mov rbx, r15
adcx rbx, [ rsp + 0x230 ]
adox rbx, r14
mov rcx, r15
adcx rcx, [ rsp + 0x240 ]
adcx r15, [ rsp + 0x240 ]
adox rcx, r11
setc r14b
clc
movzx r9, r9b
adcx r9, r8
adcx r12, [ rsp + 0x248 ]
adox r15, r12
movzx r10, r14b
mov r9, [ rsp + 0x240 ]
lea r10, [ r10 + r9 ]
adcx rbp, [ rsp + 0x250 ]
adox r10, rbp
seto r9b
adc r9b, 0x0
movzx r9, r9b
mov r11, rdi
mov r14, 0xffffffff 
sub r11, r14
mov r12, r13
sbb r12, rdx
mov rbp, rbx
mov r8, 0xfffffffffffffffe 
sbb rbp, r8
mov r8, rcx
mov r14, 0xffffffffffffffff 
sbb r8, r14
mov rdx, r15
sbb rdx, r14
mov [ rsp + 0x258 ], r8
mov r8, r10
sbb r8, r14
movzx r14, r9b
sbb r14, 0x00000000
cmovc r11, rdi
cmovc r8, r10
cmovc rdx, r15
cmovc r12, r13
cmovc rbp, rbx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x28 ], r8
mov [ r14 + 0x0 ], r11
mov rdi, [ rsp + 0x258 ]
cmovc rdi, rcx
mov [ r14 + 0x18 ], rdi
mov [ r14 + 0x20 ], rdx
mov [ r14 + 0x8 ], r12
mov [ r14 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 736
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.3576
; seed 1130478791768218 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4272416 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=56, initial num_batches=31): 110350 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02582847737673485
; number reverted permutation / tried permutation: 58804 / 90140 =65.236%
; number reverted decision / tried decision: 50364 / 89859 =56.048%
; validated in 28.07s
