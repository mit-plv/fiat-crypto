SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 648
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r12
mulx r12, r9, [ rsi + 0x8 ]
mov rdx, 0x100000001 
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r8
mulx r8, rbp, r15
mov r8, 0xfffffffffffffffe 
mov rdx, r8
mov [ rsp - 0x28 ], rcx
mulx rcx, r8, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r10
mulx r10, r11, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], r13
mulx r13, rbx, rbp
test al, al
adox rbx, r15
mov rdx, [ rax + 0x18 ]
mulx r15, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], rbx
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], r15
mulx r15, rbx, [ rax + 0x0 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], r15
mulx r15, rbx, rbp
adcx rbx, r13
adcx r8, r15
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x18 ]
mov rdx, r11
adcx rdx, rcx
mov rcx, r11
adcx rcx, r10
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], rbp
mulx rbp, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], r9
mulx r9, r12, [ rsi + 0x10 ]
adcx r11, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], r12
mulx r12, r9, [ rsi + 0x0 ]
setc dl
clc
adcx r13, rdi
adcx r9, rbp
mov dil, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r11
mulx r11, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x88 ], dil
mov [ rsp + 0x90 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
adcx rbp, r12
adcx rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rax + 0x28 ]
adox rbx, r13
adox r8, r9
adcx r12, rcx
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rax + 0x8 ]
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r13, r14
adox r15, rbp
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, [ rax + 0x18 ]
adox rdi, [ rsp + 0x90 ]
adox r12, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r12
mulx r12, rbp, [ rax + 0x10 ]
adcx rbp, r9
adcx r14, r12
adcx rcx, [ rsp + 0x68 ]
mov rdx, [ rax + 0x28 ]
mulx r12, r9, [ rsi + 0x8 ]
adcx r9, [ rsp + 0x60 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rbx, [ rsp + 0x18 ]
adcx r13, r8
adcx rbp, r15
adcx r14, rdi
mov r8, 0x100000001 
mov rdx, rbx
mulx r15, rbx, r8
movzx r15, byte [ rsp + 0x88 ]
lea r10, [ r10 + r15 ]
adox r10, r11
mov r15, [ rsp + 0x48 ]
seto r11b
mov rdi, -0x2 
inc rdi
adox r15, [ rsp + 0x10 ]
mov rdi, [ rsp + 0x0 ]
adox rdi, [ rsp + 0x8 ]
mov r8, [ rsp - 0x8 ]
adox r8, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0x98 ]
mov [ rsp + 0xa0 ], r8
mov r8, 0xffffffff 
xchg rdx, rbx
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], rcx
mulx rcx, rdi, r8
seto r8b
mov [ rsp + 0xb8 ], r14
mov r14, -0x2 
inc r14
adox rdi, rbx
adcx r9, r10
mov rdi, 0xffffffff00000000 
mulx r10, rbx, rdi
movzx r14, r11b
adcx r14, r12
mov r12, 0xfffffffffffffffe 
mulx rdi, r11, r12
setc r12b
clc
adcx rbx, rcx
mov rcx, 0xffffffffffffffff 
mov byte [ rsp + 0xc0 ], r8b
mov byte [ rsp + 0xc8 ], r12b
mulx r12, r8, rcx
adcx r11, r10
mov rdx, r8
adcx rdx, rdi
mov r10, r8
adcx r10, r12
adcx r8, r12
adox rbx, r13
mov r13, 0x0 
adcx r12, r13
clc
adcx rbx, [ rsp + 0x40 ]
adox r11, rbp
adcx r15, r11
adox rdx, [ rsp + 0xb8 ]
adox r10, [ rsp + 0xb0 ]
adcx rdx, [ rsp + 0xa8 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mulx r11, rdi, rbx
adox r8, r9
mov r11, 0xfffffffffffffffe 
mov rdx, r11
mulx r9, r11, rdi
adox r12, r14
movzx r14, byte [ rsp + 0xc8 ]
adox r14, r13
adcx r10, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r13
mov [ rsp + 0xd8 ], r10
mulx r10, r13, [ rax + 0x8 ]
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0xe0 ], rbp
movzx rbp, byte [ rsp + 0xc0 ]
mov [ rsp + 0xe8 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox rbp, r9
adox rdx, [ rsp + 0x70 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r15
mulx r15, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], r14
mulx r14, r11, [ rax + 0x10 ]
adox r9, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], r9
mov [ rsp + 0x110 ], r12
mulx r12, r9, [ rax + 0x28 ]
seto dl
mov [ rsp + 0x118 ], r12
mov r12, -0x2 
inc r12
adox r13, rcx
adox r11, r10
adox r14, [ rsp + 0x28 ]
movzx rcx, dl
lea rcx, [ rcx + r15 ]
mov rdx, [ rax + 0x28 ]
mulx r15, r10, [ rsi + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x120 ], r15
mulx r15, r12, rdi
mov rdx, [ rsp + 0x20 ]
adox rdx, [ rsp + 0x58 ]
mov [ rsp + 0x128 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], r11
mov [ rsp + 0x138 ], r13
mulx r13, r11, [ rax + 0x8 ]
adox r9, [ rsp + 0x50 ]
adcx rbp, r8
mov rdx, [ rsp + 0x108 ]
adcx rdx, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x100 ]
setc r8b
clc
adcx r11, [ rsp - 0x10 ]
mov [ rsp + 0x140 ], r11
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x148 ], r8b
mov [ rsp + 0x150 ], r9
mulx r9, r8, [ rsi + 0x28 ]
adcx r8, r13
mov rdx, 0xffffffff 
mov [ rsp + 0x158 ], r8
mulx r8, r13, rdi
mov rdx, [ rsp + 0x118 ]
mov [ rsp + 0x160 ], r14
mov r14, 0x0 
adox rdx, r14
mov r14, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x168 ], rcx
mov [ rsp + 0x170 ], r11
mulx r11, rcx, [ rsi + 0x28 ]
adcx rcx, r9
adcx r11, [ rsp - 0x18 ]
adcx r10, [ rsp - 0x20 ]
mov rdx, -0x2 
inc rdx
adox r13, rbx
setc r13b
clc
adcx r12, r8
adcx r15, [ rsp + 0xf8 ]
adox r12, [ rsp + 0xf0 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r9, rbx, rdi
mov rdi, rbx
adcx rdi, [ rsp + 0xe8 ]
mov r8, rbx
adcx r8, r9
adcx rbx, r9
adox r15, [ rsp + 0xe0 ]
adox rdi, [ rsp + 0xd8 ]
mov rdx, 0x0 
adcx r9, rdx
adox r8, rbp
clc
adcx r12, [ rsp + 0xd0 ]
mov rbp, 0x100000001 
mov rdx, rbp
mov [ rsp + 0x178 ], r10
mulx r10, rbp, r12
mov r10, 0xffffffff 
mov rdx, r10
mov byte [ rsp + 0x180 ], r13b
mulx r13, r10, rbp
adcx r15, [ rsp + 0x138 ]
adcx rdi, [ rsp + 0x130 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x188 ], r11
mov [ rsp + 0x190 ], rcx
mulx rcx, r11, rbp
adox rbx, [ rsp + 0x170 ]
adox r9, [ rsp + 0x168 ]
adcx r8, [ rsp + 0x128 ]
adcx rbx, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x150 ]
movzx rdx, byte [ rsp + 0x148 ]
mov [ rsp + 0x198 ], r14
mov r14, 0x0 
adox rdx, r14
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1a0 ], r9
mov [ rsp + 0x1a8 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], r9
mulx r9, rbx, rbp
mov rdx, -0x2 
inc rdx
adox rbx, r13
mov r13, 0xfffffffffffffffe 
mov rdx, r13
mov [ rsp + 0x1c0 ], r14
mulx r14, r13, rbp
setc bpl
clc
adcx r10, r12
adcx rbx, r15
adox r13, r9
mov r10, r11
adox r10, r14
mov r12, r11
adox r12, rcx
adcx r13, rdi
adcx r10, r8
adox r11, rcx
mov rdx, [ rsi + 0x20 ]
mulx rdi, r15, [ rax + 0x10 ]
adcx r12, [ rsp + 0x1a8 ]
adcx r11, [ rsp + 0x1a0 ]
mov rdx, [ rax + 0x18 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x1c0 ]
seto r14b
mov [ rsp + 0x1c8 ], r11
mov r11, 0x0 
dec r11
movzx rbp, bpl
adox rbp, r11
adox rdx, [ rsp + 0x198 ]
movzx rbp, r14b
lea rbp, [ rbp + rcx ]
adcx rbp, rdx
setc cl
clc
adcx rbx, [ rsp - 0x28 ]
movzx r14, cl
mov rdx, 0x0 
adox r14, rdx
mov rcx, [ rsp - 0x30 ]
mov r11, -0x3 
inc r11
adox rcx, [ rsp + 0x1b8 ]
adcx rcx, r13
mov r13, 0x100000001 
mov rdx, r13
mulx r11, r13, rbx
adox r15, [ rsp + 0x1b0 ]
mov r11, 0xfffffffffffffffe 
mov rdx, r13
mov [ rsp + 0x1d0 ], rcx
mulx rcx, r13, r11
adox r8, rdi
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
adox r11, r9
adcx r15, r10
adox rcx, [ rsp - 0x38 ]
mov rdx, [ rsp - 0x40 ]
mov r10, 0x0 
adox rdx, r10
adcx r8, r12
adcx r11, [ rsp + 0x1c8 ]
mov r12, 0xffffffff00000000 
xchg rdx, rdi
mulx r10, r9, r12
adcx rcx, rbp
mov rbp, 0xffffffff 
mov [ rsp + 0x1e0 ], rcx
mulx rcx, r12, rbp
mov rbp, -0x2 
inc rbp
adox r12, rbx
adcx rdi, r14
setc r12b
clc
adcx r9, rcx
adcx r13, r10
mov rbx, 0xffffffffffffffff 
mulx r10, r14, rbx
mov rdx, r14
adcx rdx, [ rsp + 0x1d8 ]
mov rcx, r14
adcx rcx, r10
adox r9, [ rsp + 0x1d0 ]
adcx r14, r10
adox r13, r15
adox rdx, r8
adox rcx, r11
seto r15b
inc rbp
adox r9, [ rsp - 0x48 ]
mov r8, 0x100000001 
xchg rdx, r8
mulx rbp, r11, r9
adox r13, [ rsp + 0x140 ]
mov rdx, rbx
mulx rbp, rbx, r11
adox r8, [ rsp + 0x158 ]
adox rcx, [ rsp + 0x190 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1e8 ], rcx
mov [ rsp + 0x1f0 ], r8
mulx r8, rcx, r11
mov rdx, 0x0 
adcx r10, rdx
clc
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx r14, [ rsp + 0x1e0 ]
adcx r10, rdi
movzx rdi, r12b
mov r15, 0x0 
adcx rdi, r15
mov r12, 0xffffffff 
mov rdx, r11
mulx r15, r11, r12
adox r14, [ rsp + 0x188 ]
clc
adcx rcx, r15
mov r15, 0xfffffffffffffffe 
mov [ rsp + 0x1f8 ], r14
mulx r14, r12, r15
movzx rdx, byte [ rsp + 0x180 ]
mov r15, [ rsp + 0x120 ]
lea rdx, [ rdx + r15 ]
adox r10, [ rsp + 0x178 ]
adcx r12, r8
adox rdx, rdi
seto r15b
mov r8, -0x2 
inc r8
adox r11, r9
mov r11, rbx
adcx r11, r14
mov r9, rbx
adcx r9, rbp
adcx rbx, rbp
mov rdi, 0x0 
adcx rbp, rdi
adox rcx, r13
adox r12, [ rsp + 0x1f0 ]
adox r11, [ rsp + 0x1e8 ]
adox r9, [ rsp + 0x1f8 ]
adox rbx, r10
adox rbp, rdx
seto r13b
mov r14, rcx
mov r10, 0xffffffff 
sub r14, r10
mov rdx, r12
mov rdi, 0xffffffff00000000 
sbb rdx, rdi
mov r8, r11
mov rdi, 0xfffffffffffffffe 
sbb r8, rdi
mov rdi, r9
mov r10, 0xffffffffffffffff 
sbb rdi, r10
movzx r10, r13b
movzx r15, r15b
lea r10, [ r10 + r15 ]
mov r15, rbx
mov r13, 0xffffffffffffffff 
sbb r15, r13
mov [ rsp + 0x200 ], r14
mov r14, rbp
sbb r14, r13
sbb r10, 0x00000000
cmovc rdi, r9
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rdi
cmovc r15, rbx
cmovc r8, r11
cmovc r14, rbp
mov [ r10 + 0x28 ], r14
cmovc rdx, r12
mov [ r10 + 0x8 ], rdx
mov r12, [ rsp + 0x200 ]
cmovc r12, rcx
mov [ r10 + 0x10 ], r8
mov [ r10 + 0x0 ], r12
mov [ r10 + 0x20 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 648
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5202
; seed 2469112754678764 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4939287 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=54, initial num_batches=31): 125374 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025383015807747152
; number reverted permutation / tried permutation: 59732 / 89785 =66.528%
; number reverted decision / tried decision: 44612 / 90214 =49.451%
; validated in 36.112s
