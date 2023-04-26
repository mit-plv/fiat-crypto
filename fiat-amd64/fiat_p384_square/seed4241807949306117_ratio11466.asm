SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 776
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], rdi
mulx rdi, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rax
mulx rax, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r12
mulx r12, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], rax
mulx rax, r12, [ rsi + 0x10 ]
test al, al
adox rbx, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], rax
mov [ rsp + 0x40 ], r12
mulx r12, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], rax
mov [ rsp + 0x50 ], rdi
mulx rdi, rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
adcx rdi, r12
mov rdx, 0x100000001 
mov [ rsp + 0x68 ], rdi
mulx rdi, r12, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], r12
mulx r12, r13, [ rsi + 0x28 ]
adox r11, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r11
mulx r11, rbp, [ rsi + 0x18 ]
setc dl
clc
adcx r13, r10
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r13
mov [ rsp + 0xa8 ], r11
mulx r11, r13, [ rsi + 0x28 ]
adcx r13, r12
adox rdi, rcx
seto dl
mov rcx, -0x1 
inc rcx
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox rbx, r9
mov r9b, dl
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], rbx
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r10
mov byte [ rsp + 0xe0 ], r9b
mulx r9, r10, [ rsi + 0x8 ]
adcx r12, r11
adcx rdi, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], rdi
mov [ rsp + 0xf0 ], r12
mulx r12, rdi, rdx
seto dl
mov [ rsp + 0xf8 ], rbx
mov rbx, -0x2 
inc rbx
adox r14, rcx
adox r10, r15
setc r15b
clc
movzx rdx, dl
adcx rdx, rbx
adcx r8, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, [ rsi + 0x20 ]
setc dl
clc
adcx r13, [ rsp + 0x80 ]
mov rbx, [ rsp + 0x50 ]
adcx rbx, [ rsp + 0x60 ]
adox rbp, r9
mov r9, 0xffffffff 
xchg rdx, r9
mov [ rsp + 0x100 ], rbx
mov [ rsp + 0x108 ], r13
mulx r13, rbx, [ rsp + 0x70 ]
seto dl
mov [ rsp + 0x110 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r9, r9b
adox r9, r8
adox r12, [ rsp + 0x8 ]
mov r9b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r12
mulx r12, r8, rdx
mov rdx, [ rsp - 0x18 ]
adox rdx, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x0 ]
mov [ rsp + 0x120 ], rcx
seto cl
mov [ rsp + 0x128 ], rdx
mov rdx, 0x0 
dec rdx
movzx r9, r9b
adox r9, rdx
adox r11, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], r11
mulx r11, r9, [ rsi + 0x8 ]
adcx rdi, [ rsp - 0x20 ]
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x138 ], rdi
setc dil
mov [ rsp + 0x140 ], rbp
movzx rbp, byte [ rsp + 0xe0 ]
clc
mov [ rsp + 0x148 ], r10
mov r10, -0x1 
adcx rbp, r10
adcx rdx, [ rsp + 0x78 ]
adox r9, [ rsp + 0xf8 ]
mov rbp, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0x40 ]
mov r10, 0xffffffff00000000 
xchg rdx, r10
mov byte [ rsp + 0x150 ], dil
mov [ rsp + 0x158 ], rbp
mulx rbp, rdi, [ rsp + 0x70 ]
setc dl
clc
adcx rdi, r13
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x160 ], r10
mov r10b, dl
mov rdx, [ rsp + 0x70 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], r14
mulx r14, r9, r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], r9
mulx r9, r14, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp + 0x188 ], rbp
mov rbp, -0x1 
movzx r15, r15b
adcx r15, rbp
adcx r8, [ rsp + 0xd8 ]
seto r15b
inc rbp
adox r14, [ rsp + 0x58 ]
adcx r12, rbp
clc
adcx rbx, rax
movzx rbx, r15b
lea rbx, [ rbx + r11 ]
mov al, dl
mov rdx, [ rsi + 0x28 ]
mulx r15, r11, [ rsi + 0x0 ]
movzx rdx, r10b
mov rbp, [ rsp + 0x38 ]
lea rdx, [ rdx + rbp ]
adcx rdi, r14
mov rbp, 0xfffffffffffffffe 
xchg rdx, r13
mulx r14, r10, rbp
movzx rdx, cl
mov rbp, [ rsp + 0x10 ]
lea rdx, [ rdx + rbp ]
adox r9, [ rsp - 0x8 ]
mov rbp, [ rsp - 0x28 ]
adox rbp, [ rsp - 0x10 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r12
mov [ rsp + 0x198 ], r8
mulx r8, r12, [ rsi + 0x20 ]
adox r12, [ rsp - 0x30 ]
setc dl
clc
mov [ rsp + 0x1a0 ], rcx
mov rcx, -0x1 
movzx rax, al
adcx rax, rcx
adcx r10, [ rsp + 0x188 ]
adcx r14, [ rsp + 0x180 ]
adox r11, r8
mov rax, [ rsp + 0x180 ]
mov r8, rax
adcx r8, [ rsp + 0x178 ]
seto cl
mov [ rsp + 0x1a8 ], r13
mov r13, -0x2 
inc r13
adox rdi, [ rsp + 0xd0 ]
setc r13b
clc
mov [ rsp + 0x1b0 ], rbx
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx r9, r10
adox r9, [ rsp + 0x170 ]
mov rdx, 0x100000001 
mulx rbx, r10, rdi
mov rbx, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp + 0x1b8 ], r15
mulx r15, r10, rbx
adcx r14, rbp
adox r14, [ rsp + 0x148 ]
adcx r8, r12
seto bpl
mov r12, 0x0 
dec r12
movzx r13, r13b
adox r13, r12
adox rax, [ rsp + 0x178 ]
setc r13b
clc
movzx rbp, bpl
adcx rbp, r12
adcx r8, [ rsp + 0x140 ]
mov rbp, 0xffffffff00000000 
mulx rbx, r12, rbp
mov rbp, 0xffffffff 
mov byte [ rsp + 0x1c0 ], cl
mov [ rsp + 0x1c8 ], r15
mulx r15, rcx, rbp
seto bpl
mov [ rsp + 0x1d0 ], r8
mov r8, -0x2 
inc r8
adox r12, r15
setc r15b
clc
adcx rcx, rdi
mov rcx, 0xfffffffffffffffe 
mulx r8, rdi, rcx
adcx r12, r9
adox rdi, rbx
adcx rdi, r14
setc r9b
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r11, rax
mov r14, r10
adox r14, r8
seto r13b
inc rdx
mov rax, -0x1 
movzx r15, r15b
adox r15, rax
adox r11, [ rsp + 0x130 ]
setc r15b
clc
movzx r9, r9b
adcx r9, rax
adcx r14, [ rsp + 0x1d0 ]
mov rbx, r10
setc r8b
clc
movzx r13, r13b
adcx r13, rax
adcx rbx, [ rsp + 0x1c8 ]
adcx r10, [ rsp + 0x1c8 ]
setc r9b
clc
adcx r12, [ rsp - 0x38 ]
movzx r13, byte [ rsp + 0x1c0 ]
mov rdx, [ rsp + 0x1b8 ]
lea r13, [ r13 + rdx ]
movzx rdx, bpl
mov rax, [ rsp + 0x178 ]
lea rdx, [ rdx + rax ]
seto al
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r15, r15b
adox r15, rbp
adox r13, rdx
adcx rdi, [ rsp + 0x30 ]
seto r15b
inc rbp
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox r13, [ rsp + 0x168 ]
movzx rax, r9b
mov rbp, [ rsp + 0x1c8 ]
lea rax, [ rax + rbp ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx r9, rbp, r12
adcx r14, [ rsp + 0x98 ]
mov rdx, rbp
mulx rbp, r9, rcx
mov rcx, 0xffffffff 
mov [ rsp + 0x1d8 ], r14
mov [ rsp + 0x1e0 ], rax
mulx rax, r14, rcx
mov rcx, 0xffffffff00000000 
mov byte [ rsp + 0x1e8 ], r15b
mov [ rsp + 0x1f0 ], r10
mulx r10, r15, rcx
setc cl
clc
adcx r15, rax
adcx r9, r10
seto al
mov r10, -0x2 
inc r10
adox r14, r12
adox r15, rdi
mov r14, 0xffffffffffffffff 
mulx rdi, r12, r14
seto dl
inc r10
adox r15, [ rsp + 0x48 ]
mov r10, r12
adcx r10, rbp
seto bpl
mov r14, 0x0 
dec r14
movzx r8, r8b
adox r8, r14
adox r11, rbx
adox r13, [ rsp + 0x1f0 ]
movzx r8, byte [ rsp + 0x1e8 ]
setc bl
clc
movzx rax, al
adcx rax, r14
adcx r8, [ rsp + 0x1b0 ]
adox r8, [ rsp + 0x1e0 ]
mov rax, rdi
setc r14b
clc
mov byte [ rsp + 0x1f8 ], bpl
mov rbp, -0x1 
movzx rbx, bl
adcx rbx, rbp
adcx rax, r12
adcx r12, rdi
movzx rbx, r14b
mov rbp, 0x0 
adox rbx, rbp
dec rbp
movzx rcx, cl
adox rcx, rbp
adox r11, [ rsp + 0xc8 ]
adox r13, [ rsp + 0x160 ]
setc cl
clc
movzx rdx, dl
adcx rdx, rbp
adcx r9, [ rsp + 0x1d8 ]
adcx r10, r11
mov rdx, 0x100000001 
mulx r11, r14, r15
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rbp, r11, r14
adox r8, [ rsp + 0x158 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x200 ], rbp
mov [ rsp + 0x208 ], r11
mulx r11, rbp, r14
adcx rax, r13
setc r13b
movzx rdx, byte [ rsp + 0x1f8 ]
clc
mov [ rsp + 0x210 ], rax
mov rax, -0x1 
adcx rdx, rax
adcx r9, [ rsp + 0x68 ]
adox rbx, [ rsp + 0x1a8 ]
seto dl
inc rax
mov rax, -0x1 
movzx r13, r13b
adox r13, rax
adox r8, r12
adcx r10, [ rsp + 0xc0 ]
movzx r12, cl
lea r12, [ r12 + rdi ]
mov rdi, 0xfffffffffffffffe 
xchg rdx, rdi
mulx r13, rcx, r14
adox r12, rbx
mov rbx, 0xffffffff 
mov rdx, r14
mulx rax, r14, rbx
seto dl
mov rbx, -0x2 
inc rbx
adox rbp, rax
adox rcx, r11
mov r11, [ rsp + 0x210 ]
adcx r11, [ rsp + 0x110 ]
adox r13, [ rsp + 0x208 ]
mov rax, [ rsp + 0x200 ]
mov rbx, rax
adox rbx, [ rsp + 0x208 ]
mov [ rsp + 0x218 ], rbx
seto bl
mov [ rsp + 0x220 ], r13
mov r13, -0x2 
inc r13
adox r14, r15
adox rbp, r9
adcx r8, [ rsp + 0x118 ]
adox rcx, r10
movzx r14, dl
movzx rdi, dil
lea r14, [ r14 + rdi ]
adcx r12, [ rsp + 0x128 ]
adox r11, [ rsp + 0x220 ]
adcx r14, [ rsp + 0x1a0 ]
seto r15b
inc r13
adox rbp, [ rsp + 0xb8 ]
mov r9, 0x100000001 
mov rdx, rbp
mulx rdi, rbp, r9
adox rcx, [ rsp + 0x108 ]
mov rdi, 0xffffffff 
xchg rdx, rdi
mulx r13, r10, rbp
mov r9, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp + 0x228 ], r14
mulx r14, rbp, r9
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x230 ], r12
mov [ rsp + 0x238 ], rcx
mulx rcx, r12, r9
setc r9b
clc
adcx rbp, r13
adcx r12, r14
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x240 ], r12
mulx r12, r14, r13
adox r11, [ rsp + 0x100 ]
seto dl
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r15, r15b
adox r15, r13
adox r8, [ rsp + 0x218 ]
mov r15, r14
adcx r15, rcx
mov rcx, rax
setc r13b
clc
mov [ rsp + 0x248 ], r15
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx rcx, [ rsp + 0x208 ]
mov rbx, 0x0 
adcx rax, rbx
clc
adcx r10, rdi
adcx rbp, [ rsp + 0x238 ]
setc r10b
clc
adcx rbp, [ rsp - 0x40 ]
mov rdi, [ rsp - 0x48 ]
setc bl
movzx r15, byte [ rsp + 0x150 ]
clc
mov [ rsp + 0x250 ], r11
mov r11, -0x1 
adcx r15, r11
adcx rdi, [ rsp + 0x28 ]
adox rcx, [ rsp + 0x230 ]
mov r15, [ rsp + 0x20 ]
mov r11, 0x0 
adcx r15, r11
mov r11, 0x100000001 
xchg rdx, rbp
mov byte [ rsp + 0x258 ], bl
mov byte [ rsp + 0x260 ], r10b
mulx r10, rbx, r11
clc
mov r10, -0x1 
movzx rbp, bpl
adcx rbp, r10
adcx r8, [ rsp + 0x120 ]
mov rbp, 0xfffffffffffffffe 
xchg rdx, rbp
mulx r11, r10, rbx
adox rax, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0x138 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x268 ], rcx
mov [ rsp + 0x270 ], r11
mulx r11, rcx, rbx
adcx rdi, rax
setc al
clc
adcx rcx, rbp
mov rcx, r12
setc bpl
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx rcx, r14
movzx r13, r9b
mov rdx, 0x0 
adox r13, rdx
adcx r14, r12
mov r9, 0xffffffff00000000 
mov rdx, r9
mov byte [ rsp + 0x278 ], bpl
mulx rbp, r9, rbx
mov rdx, 0x0 
dec rdx
movzx rax, al
adox rax, rdx
adox r13, r15
setc r15b
clc
adcx r9, r11
adcx r10, rbp
mov r11, [ rsp + 0x250 ]
seto al
movzx rbp, byte [ rsp + 0x260 ]
inc rdx
mov rdx, -0x1 
adox rbp, rdx
adox r11, [ rsp + 0x240 ]
adox r8, [ rsp + 0x248 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp + 0x280 ], r10
mulx r10, rbp, rbx
mov rbx, rbp
adcx rbx, [ rsp + 0x270 ]
adox rcx, [ rsp + 0x268 ]
adox r14, rdi
movzx rdi, r15b
lea rdi, [ rdi + r12 ]
mov r12, rbp
adcx r12, r10
adox rdi, r13
adcx rbp, r10
movzx r15, al
mov r13, 0x0 
adox r15, r13
movzx rax, byte [ rsp + 0x258 ]
dec r13
adox rax, r13
adox r11, [ rsp + 0xa0 ]
setc al
movzx r13, byte [ rsp + 0x278 ]
clc
mov rdx, -0x1 
adcx r13, rdx
adcx r11, r9
adox r8, [ rsp + 0xb0 ]
adcx r8, [ rsp + 0x280 ]
adox rcx, [ rsp + 0xf0 ]
adox r14, [ rsp + 0xe8 ]
adcx rbx, rcx
adox rdi, [ rsp + 0x198 ]
movzx r13, al
lea r13, [ r13 + r10 ]
adcx r12, r14
adcx rbp, rdi
setc r9b
seto r10b
mov rax, r11
mov rcx, 0xffffffff 
sub rax, rcx
mov r14, r8
mov rdi, 0xffffffff00000000 
sbb r14, rdi
mov rdx, rbx
mov rdi, 0xfffffffffffffffe 
sbb rdx, rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r10, r10b
adox r10, rdi
adox r15, [ rsp + 0x190 ]
seto r10b
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r15, r13
seto r13b
mov r9, r12
mov rdi, 0xffffffffffffffff 
sbb r9, rdi
mov rcx, rbp
sbb rcx, rdi
movzx rdi, r13b
movzx r10, r10b
lea rdi, [ rdi + r10 ]
mov r10, r15
mov r13, 0xffffffffffffffff 
sbb r10, r13
sbb rdi, 0x00000000
cmovc rax, r11
cmovc r10, r15
cmovc r14, r8
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], rax
cmovc rcx, rbp
mov [ rdi + 0x28 ], r10
mov [ rdi + 0x20 ], rcx
cmovc rdx, rbx
cmovc r9, r12
mov [ rdi + 0x18 ], r9
mov [ rdi + 0x8 ], r14
mov [ rdi + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 776
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1466
; seed 4241807949306117 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 27281 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=78, initial num_batches=31): 754 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.027638283054140244
; number reverted permutation / tried permutation: 297 / 523 =56.788%
; number reverted decision / tried decision: 278 / 476 =58.403%
; validated in 21.305s
