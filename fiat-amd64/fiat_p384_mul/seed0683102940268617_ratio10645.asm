SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 784
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], r14
mulx r14, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r13
mulx r13, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r11
mulx r11, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r8
mulx r8, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r11
mulx r11, r8, [ rax + 0x8 ]
test al, al
adox r8, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r8
mulx r8, r13, [ rax + 0x0 ]
adcx rbp, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r13
mulx r13, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rcx
mulx rcx, r14, [ rax + 0x0 ]
adcx r9, r12
adcx rbp, rbx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rbp
mulx rbp, r14, [ rax + 0x28 ]
setc dl
clc
adcx r10, r8
mov r8b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r10
mov [ rsp + 0x50 ], r9
mulx r9, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], r9
mulx r9, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], r14
mulx r14, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], r12
mulx r12, r10, [ rax + 0x18 ]
adox rbx, r11
adox r9, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x98 ], r9
mov [ rsp + 0xa0 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0xa8 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r8, r8b
adox r8, rbx
adox r13, r15
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mulx rbx, r8, [ rax + 0x8 ]
adox rdi, [ rsp + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
adcx r9, [ rsp - 0x20 ]
setc dl
clc
adcx r8, rcx
mov cl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r13
mulx r13, r8, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], r13
mulx r13, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], r8
mov [ rsp + 0xe8 ], rdi
mulx rdi, r8, [ rax + 0x28 ]
seto dl
mov byte [ rsp + 0xf0 ], cl
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox r14, r9
adox r8, r13
mov r15b, dl
mov rdx, [ rax + 0x8 ]
mulx r13, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xf8 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp + 0x100 ], rdi
mov rdi, -0x3 
inc rdi
adox r9, [ rsp + 0x90 ]
adox r13, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r14
mulx r14, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov byte [ rsp + 0x110 ], r15b
mov [ rsp + 0x118 ], r13
mulx r13, r15, [ rsi + 0x0 ]
adcx rbx, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x40 ]
seto dl
mov [ rsp + 0x120 ], r11
mov r11, -0x2 
inc r11
adox rdi, r13
adox rcx, r14
adcx rbp, [ rsp - 0x10 ]
mov r14b, dl
mov rdx, [ rax + 0x20 ]
mulx r11, r13, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x128 ], rbp
mov rbp, 0x0 
dec rbp
movzx r14, r14b
adox r14, rbp
adox r10, [ rsp + 0x70 ]
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], rbx
mulx rbx, rbp, [ rax + 0x18 ]
mov rdx, [ rsp - 0x18 ]
adcx rdx, [ rsp + 0x68 ]
adox r13, r12
mov r12, [ rsp + 0x60 ]
mov [ rsp + 0x138 ], rdx
mov rdx, 0x0 
adcx r12, rdx
mov rdx, 0x100000001 
mov [ rsp + 0x140 ], r12
mov [ rsp + 0x148 ], r13
mulx r13, r12, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], r10
mulx r10, r13, [ rax + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x158 ], r9
mov [ rsp + 0x160 ], rcx
mulx rcx, r9, r12
adox r13, r11
mov r11, 0xfffffffffffffffe 
mov rdx, r11
mov [ rsp + 0x168 ], r13
mulx r13, r11, r12
clc
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r8, rbp
adcx rbx, [ rsp + 0x80 ]
mov r14, [ rsp + 0xa8 ]
seto bpl
movzx rdx, byte [ rsp + 0xf0 ]
mov [ rsp + 0x170 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rdx, rbx
adox r14, [ rsp + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x178 ], r14
mulx r14, rbx, r12
mov rdx, 0xffffffff 
mov [ rsp + 0x180 ], r8
mov [ rsp + 0x188 ], rdi
mulx rdi, r8, r12
mov r12, [ rsp + 0x28 ]
adox r12, [ rsp - 0x8 ]
mov rdx, [ rsp + 0x20 ]
adox rdx, [ rsp + 0xe8 ]
mov [ rsp + 0x190 ], rdx
seto dl
mov [ rsp + 0x198 ], r12
mov r12, -0x2 
inc r12
adox r9, rdi
adox r11, rcx
mov rcx, rbx
adox rcx, r13
movzx r13, bpl
lea r13, [ r13 + r10 ]
mov r10, [ rsp + 0x78 ]
adcx r10, [ rsp + 0xe0 ]
mov rbp, rbx
adox rbp, r14
mov rdi, [ rsp + 0xd8 ]
mov r12, 0x0 
adcx rdi, r12
adox rbx, r14
clc
adcx r8, r15
adox r14, r12
adcx r9, [ rsp + 0x188 ]
mov r8, -0x3 
inc r8
adox r9, [ rsp + 0x58 ]
adcx r11, [ rsp + 0x160 ]
mov r15, 0x100000001 
xchg rdx, r9
mulx r8, r12, r15
adox r11, [ rsp + 0x158 ]
mov r8, 0xffffffff00000000 
xchg rdx, r8
mov byte [ rsp + 0x1a0 ], r9b
mulx r9, r15, r12
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1a8 ], r13
mov [ rsp + 0x1b0 ], r11
mulx r11, r13, r12
adcx rcx, [ rsp + 0x180 ]
adox rcx, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x170 ]
adcx rbx, r10
adcx r14, rdi
adox rbp, [ rsp + 0x150 ]
adox rbx, [ rsp + 0x148 ]
adox r14, [ rsp + 0x168 ]
mov r10, 0xffffffff 
mov rdx, r10
mulx rdi, r10, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1b8 ], r14
mov [ rsp + 0x1c0 ], rbx
mulx rbx, r14, r12
seto r12b
mov rdx, -0x2 
inc rdx
adox r15, rdi
setc dil
clc
adcx r10, r8
adox r13, r9
adcx r15, [ rsp + 0x1b0 ]
mov r10, r14
adox r10, r11
mov r8, r14
adox r8, rbx
adcx r13, rcx
setc r9b
clc
adcx r15, [ rsp - 0x38 ]
adcx r13, [ rsp + 0x18 ]
mov r11, 0x100000001 
mov rdx, r11
mulx rcx, r11, r15
mov rcx, 0xffffffff 
mov rdx, r11
mov [ rsp + 0x1c8 ], r8
mulx r8, r11, rcx
setc cl
clc
mov byte [ rsp + 0x1d0 ], dil
mov rdi, -0x1 
movzx r9, r9b
adcx r9, rdi
adcx rbp, r10
mov r10, 0xfffffffffffffffe 
mulx rdi, r9, r10
mov r10, 0xffffffff00000000 
mov [ rsp + 0x1d8 ], rbp
mov byte [ rsp + 0x1e0 ], cl
mulx rcx, rbp, r10
mov r10, 0xffffffffffffffff 
mov byte [ rsp + 0x1e8 ], r12b
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r12, r10
seto dl
mov r10, -0x2 
inc r10
adox rbp, r8
adox r9, rcx
setc r8b
clc
adcx r11, r15
adcx rbp, r13
mov r11, r12
adox r11, [ rsp + 0x1f0 ]
mov r15, [ rsp + 0x1a8 ]
setc r13b
movzx rcx, byte [ rsp + 0x1e8 ]
clc
mov [ rsp + 0x1f8 ], r11
movzx r11, byte [ rsp + 0x1d0 ]
adcx rcx, r10
adcx r15, r11
mov r11, rbx
seto cl
inc r10
mov r10, -0x1 
movzx rdx, dl
adox rdx, r10
adox r11, r14
mov r14, [ rsp + 0x1c0 ]
seto dl
inc r10
mov r10, -0x1 
movzx r8, r8b
adox r8, r10
adox r14, [ rsp + 0x1c8 ]
adox r11, [ rsp + 0x1b8 ]
mov r8, rdi
setc r10b
clc
mov [ rsp + 0x200 ], r11
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx r8, r12
movzx rcx, dl
lea rcx, [ rcx + rbx ]
mov rbx, [ rsp + 0x1d8 ]
setc dl
movzx r11, byte [ rsp + 0x1e0 ]
clc
mov [ rsp + 0x208 ], r8
mov r8, -0x1 
adcx r11, r8
adcx rbx, [ rsp + 0x50 ]
adox rcx, r15
movzx r11, r10b
mov r15, 0x0 
adox r11, r15
dec r15
movzx r13, r13b
adox r13, r15
adox rbx, r9
seto r8b
inc r15
adox rbp, [ rsp + 0x10 ]
adcx r14, [ rsp + 0x40 ]
mov r9, 0x100000001 
xchg rdx, rbp
mulx r10, r13, r9
mov r10, [ rsp + 0x200 ]
adcx r10, [ rsp + 0xb8 ]
adcx rcx, [ rsp + 0xb0 ]
adox rbx, [ rsp + 0x48 ]
seto r15b
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox r14, [ rsp + 0x1f8 ]
setc r8b
clc
movzx r15, r15b
adcx r15, r9
adcx r14, [ rsp + 0xd0 ]
adox r10, [ rsp + 0x208 ]
movzx r15, byte [ rsp + 0x110 ]
mov r9, [ rsp - 0x48 ]
lea r15, [ r15 + r9 ]
adcx r10, [ rsp + 0x178 ]
mov r9, rdi
mov [ rsp + 0x210 ], r10
seto r10b
mov [ rsp + 0x218 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rbp, bpl
adox rbp, r14
adox r9, r12
movzx r12, byte [ rsp + 0x1a0 ]
mov rbp, [ rsp + 0xc8 ]
lea r12, [ r12 + rbp ]
setc bpl
clc
movzx r8, r8b
adcx r8, r14
adcx r11, r15
setc r8b
clc
movzx r10, r10b
adcx r10, r14
adcx rcx, r9
mov r10, 0x0 
adox rdi, r10
inc r14
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rcx, [ rsp + 0x198 ]
adcx rdi, r11
adox rdi, [ rsp + 0x190 ]
movzx r15, r8b
adcx r15, r14
mov rbp, 0xfffffffffffffffe 
xchg rdx, r13
mulx r11, r9, rbp
mov r8, 0xffffffffffffffff 
mulx r10, r14, r8
mov r8, 0xffffffff 
mov [ rsp + 0x220 ], rdi
mulx rdi, rbp, r8
adox r12, r15
mov r15, 0xffffffff00000000 
mov [ rsp + 0x228 ], r12
mulx r12, r8, r15
clc
adcx rbp, r13
setc bpl
clc
adcx r8, rdi
seto r13b
mov rdx, -0x1 
inc rdx
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox rbx, r8
seto bpl
mov r8, -0x3 
inc r8
adox rbx, [ rsp - 0x28 ]
adcx r9, r12
seto r12b
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r9, [ rsp + 0x218 ]
mov rdi, r14
adcx rdi, r11
mov r11, 0x100000001 
mov rdx, rbx
mulx rbp, rbx, r11
mov rbp, 0xffffffff 
xchg rdx, rbp
mulx r15, r8, rbx
mov rdx, 0xffffffff00000000 
mov byte [ rsp + 0x230 ], r13b
mulx r13, r11, rbx
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x238 ], rcx
mov [ rsp + 0x240 ], r9
mulx r9, rcx, rbx
adox rdi, [ rsp + 0x210 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x248 ], rdi
mov byte [ rsp + 0x250 ], r12b
mulx r12, rdi, rbx
seto bl
mov rdx, -0x2 
inc rdx
adox r8, rbp
setc r8b
clc
adcx r11, r15
adcx rcx, r13
mov rbp, rdi
adcx rbp, r9
mov r15, rdi
adcx r15, r12
adcx rdi, r12
mov r13, r10
seto r9b
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r13, r14
mov r8, [ rsp + 0x240 ]
setc dl
mov [ rsp + 0x258 ], rdi
movzx rdi, byte [ rsp + 0x250 ]
clc
mov [ rsp + 0x260 ], r15
mov r15, -0x1 
adcx rdi, r15
adcx r8, [ rsp + 0x8 ]
seto dil
inc r15
mov r15, -0x1 
movzx r9, r9b
adox r9, r15
adox r8, r11
movzx r9, dl
lea r9, [ r9 + r12 ]
seto r12b
inc r15
adox r8, [ rsp + 0x38 ]
mov r11, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0x248 ]
mov rdx, r10
setc r15b
clc
mov [ rsp + 0x268 ], r9
mov r9, -0x1 
movzx rdi, dil
adcx rdi, r9
adcx rdx, r14
seto r14b
inc r9
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r13, [ rsp + 0x238 ]
adox rdx, [ rsp + 0x220 ]
adcx r10, r9
clc
movzx r12, r12b
adcx r12, rdi
adcx r11, rcx
adox r10, [ rsp + 0x228 ]
seto bl
dec r9
movzx r15, r15b
adox r15, r9
adox r13, [ rsp + 0x98 ]
adox rdx, [ rsp + 0x108 ]
adox r10, [ rsp + 0xf8 ]
mov rdi, 0x100000001 
xchg rdx, r8
mulx r12, rcx, rdi
movzx r12, bl
movzx r15, byte [ rsp + 0x230 ]
lea r12, [ r12 + r15 ]
adcx rbp, r13
mov r15, 0xffffffff 
xchg rdx, rcx
mulx r13, rbx, r15
adcx r8, [ rsp + 0x260 ]
seto r9b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r14, r14b
adox r14, r15
adox r11, [ rsp + 0xc0 ]
setc r14b
clc
adcx rbx, rcx
adox rbp, [ rsp + 0x130 ]
adox r8, [ rsp + 0x120 ]
setc bl
clc
movzx r9, r9b
adcx r9, r15
adcx r12, [ rsp + 0x100 ]
mov rcx, 0xffffffff00000000 
mulx r15, r9, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0x270 ], r12
mulx r12, rdi, rcx
setc cl
clc
adcx r9, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x278 ], cl
mov [ rsp + 0x280 ], r8
mulx r8, rcx, r13
adcx rdi, r15
mov rdx, rcx
adcx rdx, r12
seto r15b
mov r12, 0x0 
dec r12
movzx rbx, bl
adox rbx, r12
adox r11, r9
mov rbx, rcx
adcx rbx, r8
adcx rcx, r8
mov r9, 0x0 
adcx r8, r9
clc
movzx r14, r14b
adcx r14, r12
adcx r10, [ rsp + 0x258 ]
setc r14b
clc
movzx r15, r15b
adcx r15, r12
adcx r10, [ rsp + 0x128 ]
adox rdi, rbp
adox rdx, [ rsp + 0x280 ]
adox rbx, r10
mov rbp, [ rsp + 0x268 ]
setc r15b
clc
movzx r14, r14b
adcx r14, r12
adcx rbp, [ rsp + 0x270 ]
seto r14b
dec r9
movzx r15, r15b
adox r15, r9
adox rbp, [ rsp + 0x138 ]
seto r12b
inc r9
mov r10, -0x1 
movzx r14, r14b
adox r14, r10
adox rbp, rcx
movzx rcx, byte [ rsp + 0x278 ]
adcx rcx, r9
clc
movzx r12, r12b
adcx r12, r10
adcx rcx, [ rsp + 0x140 ]
setc r15b
seto r14b
mov r12, r11
mov r10, 0xffffffff 
sub r12, r10
mov r9, rdi
mov r10, 0xffffffff00000000 
sbb r9, r10
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox rcx, r8
seto r8b
mov r14, rdx
mov r13, 0xfffffffffffffffe 
sbb r14, r13
mov r13, rbx
mov r10, 0xffffffffffffffff 
sbb r13, r10
movzx r10, r8b
movzx r15, r15b
lea r10, [ r10 + r15 ]
mov r15, rbp
mov r8, 0xffffffffffffffff 
sbb r15, r8
mov [ rsp + 0x288 ], r14
mov r14, rcx
sbb r14, r8
sbb r10, 0x00000000
cmovc r15, rbp
cmovc r12, r11
cmovc r9, rdi
cmovc r14, rcx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x0 ], r12
mov [ r10 + 0x28 ], r14
cmovc r13, rbx
mov [ r10 + 0x18 ], r13
mov [ r10 + 0x20 ], r15
mov r11, [ rsp + 0x288 ]
cmovc r11, rdx
mov [ r10 + 0x8 ], r9
mov [ r10 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 784
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0645
; seed 0683102940268617 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 54633 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 1291 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.023630406530851317
; number reverted permutation / tried permutation: 287 / 495 =57.980%
; number reverted decision / tried decision: 226 / 504 =44.841%
; validated in 46.015s
