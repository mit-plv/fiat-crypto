SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 696
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r9
mulx r9, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], rdi
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], rdi
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], r14
mulx r14, r15, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r11
mulx r11, rcx, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], rbp
mulx rbp, r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rax
mov [ rsp + 0x40 ], r14
mulx r14, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], rax
mulx rax, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r15
mulx r15, r14, [ rsi + 0x10 ]
test al, al
adox r11, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r11
mulx r11, rax, [ rsi + 0x28 ]
adox r14, rbp
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x70 ], r11
mulx r11, rbp, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x78 ], rax
mov [ rsp + 0x80 ], r14
mulx r14, rax, rcx
adcx rbp, r14
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mov [ rsp + 0x88 ], rbp
mulx rbp, r14, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], r8
mulx r8, rax, [ rsi + 0x10 ]
adcx r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r8
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], rax
mov [ rsp + 0xb0 ], r14
mulx r14, rax, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0xb8 ], rax
mov rax, -0x2 
inc rax
adox r11, r14
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0xc0 ], r11
mulx r11, rax, rcx
adox r12, r8
mov rcx, rax
adcx rcx, rbp
adox rdi, r13
setc r13b
clc
mov rbp, -0x1 
movzx r14, r14b
adcx r14, rbp
adcx r15, r10
mov rdx, [ rsi + 0x20 ]
mulx r14, r10, [ rsi + 0x8 ]
adcx r10, r9
mov rdx, [ rsi + 0x28 ]
mulx r8, r9, [ rsi + 0x8 ]
adcx r9, r14
mov rdx, [ rsp + 0x98 ]
adox rdx, [ rsp + 0x60 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r14
mov [ rsp + 0xd8 ], r12
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], r9
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x40 ]
adox rdx, [ rsp + 0x38 ]
mov [ rsp + 0xf0 ], rdx
seto dl
mov [ rsp + 0xf8 ], r10
mov r10, -0x2 
inc r10
adox r14, [ rsp + 0x30 ]
adox r8, r12
adox rbp, r9
adox rdi, [ rsp + 0x28 ]
mov r12, [ rsp + 0x20 ]
adox r12, [ rsp + 0x18 ]
setc r9b
clc
adcx rbx, [ rsp + 0x90 ]
adcx r14, [ rsp + 0x88 ]
setc bl
clc
adcx r14, [ rsp + 0x58 ]
mov r10, 0x100000001 
xchg rdx, r14
mov byte [ rsp + 0x100 ], r14b
mov byte [ rsp + 0x108 ], r9b
mulx r9, r14, r10
mov r9, 0xffffffff 
xchg rdx, r14
mov [ rsp + 0x110 ], r15
mulx r15, r10, r9
seto r9b
mov [ rsp + 0x118 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbx, bl
adox rbx, r10
adox r8, [ rsp + 0xb0 ]
adcx r8, [ rsp + 0x68 ]
adox rcx, rbp
adcx rcx, [ rsp + 0x80 ]
mov rbp, r11
setc bl
clc
movzx r13, r13b
adcx r13, r10
adcx rbp, rax
adcx rax, r11
adox rbp, rdi
adox rax, r12
mov r13, 0x0 
adcx r11, r13
movzx rdi, r9b
mov r12, [ rsp + 0x10 ]
lea rdi, [ rdi + r12 ]
adox r11, rdi
clc
movzx rbx, bl
adcx rbx, r10
adcx rbp, [ rsp + 0x110 ]
adcx rax, [ rsp + 0xf8 ]
adcx r11, [ rsp + 0xe8 ]
mov r12, 0xfffffffffffffffe 
mulx rbx, r9, r12
mov rdi, 0xffffffff00000000 
mulx r10, r13, rdi
movzx r12, byte [ rsp + 0x108 ]
mov rdi, [ rsp + 0xe0 ]
lea r12, [ r12 + rdi ]
seto dil
movzx rdi, dil
adcx rdi, r12
mov r12, -0x2 
inc r12
adox r13, r15
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x120 ], rdi
mulx rdi, r12, r15
adox r9, r10
mov rdx, r12
adox rdx, rbx
mov rbx, r12
adox rbx, rdi
adox r12, rdi
setc r10b
clc
adcx r14, [ rsp + 0x118 ]
mov r14, 0x0 
adox rdi, r14
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x128 ], r10b
mulx r10, r15, [ rsi + 0x8 ]
adcx r13, r8
mov rdx, -0x2 
inc rdx
adox r13, [ rsp + 0xb8 ]
mov r8, 0x100000001 
mov rdx, r13
mov [ rsp + 0x130 ], r10
mulx r10, r13, r8
adcx r9, rcx
adox r9, [ rsp + 0xc0 ]
adcx r14, rbp
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, rcx, [ rsi + 0x20 ]
adcx rbx, rax
adcx r12, r11
mov rdx, 0xffffffff 
mulx r11, rax, r13
adcx rdi, [ rsp + 0x120 ]
movzx r8, byte [ rsp + 0x128 ]
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x138 ], rcx
mov [ rsp + 0x140 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r11
mulx r11, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], rax
mov [ rsp + 0x160 ], r8
mulx r8, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], rdi
mov [ rsp + 0x170 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
clc
adcx rdi, rbp
adcx rax, r12
adcx r8, [ rsp - 0x18 ]
adcx rcx, [ rsp - 0x20 ]
adcx r11, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, rdx
adox r14, [ rsp + 0xd8 ]
adox rbx, [ rsp + 0xc8 ]
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0x178 ], r11
mov r11, 0x0 
adcx rdx, r11
clc
adcx r15, r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x180 ], rcx
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r9
mov [ rsp + 0x190 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x130 ]
adcx rdx, [ rsp - 0x28 ]
mov [ rsp + 0x198 ], rax
mov rax, [ rsp + 0x170 ]
adox rax, [ rsp + 0xd0 ]
adcx rbp, [ rsp - 0x30 ]
mov [ rsp + 0x1a0 ], rdi
mov rdi, [ rsp + 0x168 ]
adox rdi, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0x8 ]
mov [ rsp + 0x1a8 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b0 ], rbp
mov [ rsp + 0x1b8 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
adcx rbp, [ rsp + 0x0 ]
mov rdx, 0x0 
adcx rdi, rdx
mov [ rsp + 0x1c0 ], rdi
mov rdi, [ rsp - 0x38 ]
clc
adcx rdi, [ rsp + 0x78 ]
mov rdx, [ rsp + 0x70 ]
adcx rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x1c8 ], rdx
mov rdx, [ rsp + 0xa0 ]
adcx rdx, [ rsp - 0x8 ]
mov [ rsp + 0x1d0 ], rdx
movzx rdx, byte [ rsp + 0x100 ]
mov [ rsp + 0x1d8 ], rdi
mov rdi, [ rsp - 0x40 ]
lea rdx, [ rdx + rdi ]
adox rdx, [ rsp + 0x160 ]
adcx r9, [ rsp - 0x10 ]
adcx r11, r8
seto dil
mov r8, -0x2 
inc r8
adox r10, [ rsp + 0x158 ]
mov r10, 0xffffffff00000000 
xchg rdx, r10
mov [ rsp + 0x1e0 ], r11
mulx r11, r8, r13
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1e8 ], rcx
mov [ rsp + 0x1f0 ], r9
mulx r9, rcx, r13
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1f8 ], rbp
mov byte [ rsp + 0x200 ], dil
mulx rdi, rbp, r13
clc
adcx r8, [ rsp + 0x150 ]
adox r8, [ rsp + 0x140 ]
adcx rbp, r11
adox rbp, r14
mov r13, rcx
adcx r13, rdi
adox r13, rbx
mov r14, rcx
adcx r14, r9
adcx rcx, r9
adox r14, rax
mov rbx, 0x0 
adcx r9, rbx
clc
adcx r8, [ rsp + 0x148 ]
adcx r15, rbp
adox rcx, [ rsp + 0x1b8 ]
mov rax, 0x100000001 
mov rdx, r8
mulx r11, r8, rax
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mulx rbp, rdi, r8
adcx r12, r13
adox r9, r10
mov r10, 0xffffffff 
mov rdx, r8
mulx r13, r8, r10
adcx r14, [ rsp + 0x1b0 ]
adcx rcx, [ rsp + 0x1a8 ]
mov rbx, 0xffffffff00000000 
mulx rax, r10, rbx
mov rbx, 0xfffffffffffffffe 
mov [ rsp + 0x208 ], rcx
mov [ rsp + 0x210 ], r14
mulx r14, rcx, rbx
setc dl
clc
adcx r10, r13
adcx rcx, rax
movzx r13, byte [ rsp + 0x200 ]
mov rax, 0x0 
adox r13, rax
dec rax
movzx rdx, dl
adox rdx, rax
adox r9, [ rsp + 0x1f8 ]
adox r13, [ rsp + 0x1c0 ]
mov rdx, rdi
adcx rdx, r14
mov r14, rdi
adcx r14, rbp
adcx rdi, rbp
setc al
clc
adcx r8, r11
adcx r10, r15
seto r8b
mov r11, -0x2 
inc r11
adox r10, [ rsp + 0x138 ]
adcx rcx, r12
movzx r15, al
lea r15, [ r15 + rbp ]
mov rbp, 0x100000001 
xchg rdx, r10
mulx rax, r12, rbp
adox rcx, [ rsp + 0x1a0 ]
xchg rdx, r12
mulx r11, rax, rbx
mov rbx, 0xffffffff 
mov [ rsp + 0x218 ], rcx
mulx rcx, rbp, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x220 ], r11
mov [ rsp + 0x228 ], rax
mulx rax, r11, rbx
adcx r10, [ rsp + 0x210 ]
adcx r14, [ rsp + 0x208 ]
adcx rdi, r9
adox r10, [ rsp + 0x198 ]
adox r14, [ rsp + 0x190 ]
adox rdi, [ rsp + 0x180 ]
adcx r15, r13
adox r15, [ rsp + 0x178 ]
movzx r9, r8b
mov r13, 0x0 
adcx r9, r13
adox r9, [ rsp + 0x188 ]
mov r8, 0xffffffff00000000 
mulx rbx, r13, r8
clc
adcx r13, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox rbp, r12
adcx rbx, [ rsp + 0x228 ]
mov rbp, r11
adcx rbp, [ rsp + 0x220 ]
mov r12, r11
adcx r12, rax
adcx r11, rax
adox r13, [ rsp + 0x218 ]
adox rbx, r10
adox rbp, r14
adox r12, rdi
mov r10, 0x0 
adcx rax, r10
clc
adcx r13, [ rsp - 0x48 ]
adox r11, r15
adox rax, r9
movzx r14, dl
adox r14, r10
adcx rbx, [ rsp + 0x1d8 ]
adcx rbp, [ rsp + 0x1c8 ]
adcx r12, [ rsp + 0x1d0 ]
mov rdi, 0x100000001 
mov rdx, r13
mulx r15, r13, rdi
adcx r11, [ rsp + 0x1f0 ]
adcx rax, [ rsp + 0x1e0 ]
mov r15, 0xffffffff 
xchg rdx, r13
mulx r10, r9, r15
mulx r15, rcx, r8
mov r8, -0x2 
inc r8
adox r9, r13
adcx r14, [ rsp + 0x1e8 ]
setc r9b
clc
adcx rcx, r10
mov r13, 0xffffffffffffffff 
mulx r8, r10, r13
mov r13, 0xfffffffffffffffe 
mov byte [ rsp + 0x230 ], r9b
mulx r9, rdi, r13
adox rcx, rbx
adcx rdi, r15
adox rdi, rbp
mov rbx, r10
adcx rbx, r9
mov rbp, r10
adcx rbp, r8
adcx r10, r8
adox rbx, r12
adox rbp, r11
adox r10, rax
mov r12, 0x0 
adcx r8, r12
adox r8, r14
movzx rdx, byte [ rsp + 0x230 ]
adox rdx, r12
mov r11, rcx
mov rax, 0xffffffff 
sub r11, rax
mov r15, rdi
mov r14, 0xffffffff00000000 
sbb r15, r14
mov r9, rbx
sbb r9, r13
mov r12, rbp
mov r14, 0xffffffffffffffff 
sbb r12, r14
mov r13, r10
sbb r13, r14
mov rax, r8
sbb rax, r14
sbb rdx, 0x00000000
cmovc r9, rbx
cmovc rax, r8
cmovc r15, rdi
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r9
cmovc r12, rbp
mov [ rdx + 0x8 ], r15
mov [ rdx + 0x18 ], r12
cmovc r13, r10
cmovc r11, rcx
mov [ rdx + 0x0 ], r11
mov [ rdx + 0x28 ], rax
mov [ rdx + 0x20 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 696
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4683
; seed 1281486076484068 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5337410 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=64, initial num_batches=31): 140938 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02640569114982735
; number reverted permutation / tried permutation: 65331 / 89568 =72.940%
; number reverted decision / tried decision: 50728 / 90431 =56.096%
; validated in 29.826s
