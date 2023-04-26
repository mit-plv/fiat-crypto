SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 912
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r8
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], rbx
mulx rbx, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r11
mulx r11, rbp, [ rsi + 0x20 ]
test al, al
adox r13, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x38 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], rbx
mulx rbx, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], r13
mulx r13, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], r8
mulx r8, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r10
mulx r10, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x80 ], r8
mov [ rsp + 0x88 ], r12
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x90 ], rcx
mov [ rsp + 0x98 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], rcx
mulx rcx, rdi, [ rsi + 0x18 ]
adcx r8, r10
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb0 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], rcx
mov [ rsp + 0xc0 ], r8
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], rdi
mulx rdi, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
adox rbp, r14
adox r10, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r14, [ rax + 0x10 ]
adox r9, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r9
mulx r9, rdi, [ rax + 0x18 ]
seto dl
mov [ rsp + 0xf0 ], r10
mov r10, -0x2 
inc r10
adox r11, r8
mov r8b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], rbp
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], r11
mov byte [ rsp + 0x108 ], r8b
mulx r8, r11, [ rsi + 0x0 ]
adox r11, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], r11
mulx r11, r13, [ rax + 0x0 ]
adox rdi, r8
adcx r14, r12
setc dl
clc
adcx r11, [ rsp + 0xe0 ]
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], r11
mulx r11, r8, [ rax + 0x28 ]
mov rdx, [ rsp + 0x90 ]
adcx rdx, [ rsp + 0x98 ]
adox r9, [ rsp + 0x88 ]
adox r8, [ rsp + 0x68 ]
mov [ rsp + 0x120 ], r13
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r9
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r11, rdx
mov rdx, 0x100000001 
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r11
mulx r11, r13, [ rsp + 0xd8 ]
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox rbx, [ rsp + 0x60 ]
mov r12, 0xffffffff00000000 
mov rdx, r12
mulx r11, r12, r13
mov rdx, 0xffffffff 
mov [ rsp + 0x148 ], rbx
mov [ rsp + 0x150 ], r14
mulx r14, rbx, r13
mov rdx, [ rsp + 0x10 ]
adox rdx, [ rsp + 0x30 ]
mov [ rsp + 0x158 ], rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x160 ], rdi
mov [ rsp + 0x168 ], r11
mulx r11, rdi, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], r11
mov [ rsp + 0x178 ], rdi
mulx rdi, r11, [ rax + 0x18 ]
seto dl
mov [ rsp + 0x180 ], rbx
mov rbx, -0x2 
inc rbx
adox r8, [ rsp + 0x58 ]
adox rcx, r9
adox r11, r15
mov r15, [ rsp + 0x0 ]
setc r9b
clc
movzx rdx, dl
adcx rdx, rbx
adcx r15, [ rsp + 0x78 ]
mov rdx, [ rsp + 0x8 ]
seto bl
mov [ rsp + 0x188 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox rdx, [ rsp + 0x20 ]
setc r9b
clc
movzx rbx, bl
adcx rbx, r11
adcx rdi, [ rsp + 0xd0 ]
setc bl
clc
adcx r10, [ rsp + 0x50 ]
mov r11, [ rsp + 0x18 ]
adox r11, [ rsp + 0xc8 ]
adcx rbp, [ rsp - 0x8 ]
mov [ rsp + 0x190 ], rbp
mov rbp, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x198 ], r10
mov [ rsp + 0x1a0 ], rdi
mulx rdi, r10, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x1a8 ], rcx
movzx rcx, byte [ rsp + 0x108 ]
mov [ rsp + 0x1b0 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rcx, r11
adox r10, [ rsp - 0x10 ]
mov cl, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1b8 ], r10
mulx r10, r11, [ rsi + 0x20 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x1c0 ], r10
seto r10b
mov [ rsp + 0x1c8 ], r8
mov r8, 0x0 
dec r8
movzx rcx, cl
adox rcx, r8
adox rdx, [ rsp + 0xc0 ]
mov rcx, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x20 ]
movzx r8, r10b
lea r8, [ r8 + rdi ]
mov rdi, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x38 ]
setc r10b
clc
adcx r12, r14
mov r14, [ rsp + 0xd8 ]
mov [ rsp + 0x1d0 ], r8
setc r8b
clc
adcx r14, [ rsp + 0x180 ]
adcx r12, [ rsp + 0x100 ]
mov r14, 0xfffffffffffffffe 
xchg rdx, r13
mov [ rsp + 0x1d8 ], rdi
mov [ rsp + 0x1e0 ], rcx
mulx rcx, rdi, r14
mov rdx, [ rsp + 0xb8 ]
setc r14b
clc
mov [ rsp + 0x1e8 ], r13
mov r13, -0x1 
movzx rbx, bl
adcx rbx, r13
adcx rdx, [ rsp + 0xa8 ]
mov rbx, [ rsp + 0xa0 ]
mov r13, 0x0 
adcx rbx, r13
clc
mov r13, -0x1 
movzx r8, r8b
adcx r8, r13
adcx rdi, [ rsp + 0x168 ]
mov r8, [ rsp - 0x28 ]
mov r13, 0x0 
adox r8, r13
dec r13
movzx r10, r10b
adox r10, r13
adox r11, [ rsp - 0x48 ]
adcx rcx, [ rsp + 0x178 ]
setc r10b
clc
movzx r14, r14b
adcx r14, r13
adcx rdi, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x160 ]
seto r14b
inc r13
adox r12, [ rsp + 0x80 ]
mov r13, 0x100000001 
xchg rdx, r13
mov byte [ rsp + 0x1f0 ], r14b
mov [ rsp + 0x1f8 ], r11
mulx r11, r14, r12
mov r11, 0xffffffff 
mov rdx, r11
mov [ rsp + 0x200 ], rbx
mulx rbx, r11, r14
adox rdi, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0x150 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x208 ], r13
mov [ rsp + 0x210 ], r8
mulx r8, r13, r14
mov rdx, [ rsp + 0x170 ]
mov [ rsp + 0x218 ], rbp
mov rbp, rdx
mov [ rsp + 0x220 ], rcx
setc cl
clc
mov [ rsp + 0x228 ], r15
mov r15, -0x1 
movzx r10, r10b
adcx r10, r15
adcx rbp, [ rsp + 0x178 ]
setc r10b
clc
movzx rcx, cl
adcx rcx, r15
adcx rbp, [ rsp + 0x130 ]
mov rcx, 0xffffffff00000000 
xchg rdx, r14
mov [ rsp + 0x230 ], r8
mulx r8, r15, rcx
adox rbp, [ rsp + 0x148 ]
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x238 ], rbp
mov byte [ rsp + 0x240 ], r9b
mulx r9, rbp, rcx
setc dl
clc
adcx r11, r12
seto r11b
mov r12, -0x2 
inc r12
adox r15, rbx
mov rbx, r14
seto r12b
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r10, r10b
adox r10, rcx
adox rbx, [ rsp + 0x178 ]
mov r10, 0x0 
adox r14, r10
dec r10
movzx rdx, dl
adox rdx, r10
adox rbx, [ rsp + 0x128 ]
adox r14, [ rsp + 0x140 ]
adcx r15, rdi
seto cl
inc r10
mov rdi, -0x1 
movzx r12, r12b
adox r12, rdi
adox r8, r13
movzx r13, byte [ rsp + 0x240 ]
mov rdx, [ rsp + 0x70 ]
lea r13, [ r13 + rdx ]
mov rdx, rbp
adox rdx, [ rsp + 0x230 ]
seto r12b
inc rdi
mov r10, -0x1 
movzx r11, r11b
adox r11, r10
adox rbx, [ rsp + 0x158 ]
adox r14, [ rsp + 0x228 ]
movzx r11, cl
adox r11, r13
adcx r8, [ rsp + 0x220 ]
seto cl
mov r13, -0x3 
inc r13
adox r15, [ rsp + 0x120 ]
mov rdi, 0x100000001 
xchg rdx, r15
mulx r10, r13, rdi
mov r10, r9
seto dil
mov byte [ rsp + 0x248 ], cl
mov rcx, 0x0 
dec rcx
movzx r12, r12b
adox r12, rcx
adox r10, rbp
adcx r15, [ rsp + 0x238 ]
mov r12, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x250 ], r15
mulx r15, rcx, r12
adcx r10, rbx
mov rbx, 0xffffffff 
mov [ rsp + 0x258 ], r10
mulx r10, r12, rbx
adox rbp, r9
setc bl
clc
adcx r12, r13
mov r12, 0xfffffffffffffffe 
mov [ rsp + 0x260 ], r15
mulx r15, r13, r12
mov r12, 0x0 
adox r9, r12
mov r12, 0xffffffff00000000 
mov [ rsp + 0x268 ], r8
mov byte [ rsp + 0x270 ], dil
mulx rdi, r8, r12
mov rdx, -0x2 
inc rdx
adox r8, r10
adox r13, rdi
setc r10b
clc
movzx rbx, bl
adcx rbx, rdx
adcx r14, rbp
mov rbx, rcx
adox rbx, r15
adcx r9, r11
mov r11, [ rsp + 0x268 ]
seto bpl
movzx r15, byte [ rsp + 0x270 ]
inc rdx
mov rdi, -0x1 
adox r15, rdi
adox r11, [ rsp + 0x118 ]
movzx r15, byte [ rsp + 0x248 ]
adcx r15, rdx
clc
movzx r10, r10b
adcx r10, rdi
adcx r11, r8
seto r10b
mov r8, -0x3 
inc r8
adox r11, [ rsp + 0x48 ]
mov rdx, 0x100000001 
mulx rdi, r8, r11
mov rdi, 0xfffffffffffffffe 
mov rdx, r8
mulx r12, r8, rdi
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x278 ], r12
mov [ rsp + 0x280 ], r8
mulx r8, r12, rdi
mov rdi, rcx
mov [ rsp + 0x288 ], r8
seto r8b
mov [ rsp + 0x290 ], r12
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox rdi, [ rsp + 0x260 ]
adox rcx, [ rsp + 0x260 ]
mov rbp, 0xffffffff 
mov [ rsp + 0x298 ], r15
mulx r15, r12, rbp
mov rbp, [ rsp + 0x250 ]
mov [ rsp + 0x2a0 ], r15
seto r15b
mov [ rsp + 0x2a8 ], rcx
mov rcx, 0x0 
dec rcx
movzx r10, r10b
adox r10, rcx
adox rbp, [ rsp + 0x138 ]
mov r10, [ rsp + 0x258 ]
adox r10, [ rsp + 0x218 ]
adcx r13, rbp
setc bpl
clc
movzx r8, r8b
adcx r8, rcx
adcx r13, [ rsp + 0x1c8 ]
seto r8b
inc rcx
adox r12, r11
movzx r12, r15b
mov r11, [ rsp + 0x260 ]
lea r12, [ r12 + r11 ]
setc r11b
clc
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx r10, rbx
seto bl
dec rcx
movzx r8, r8b
adox r8, rcx
adox r14, [ rsp + 0x1b0 ]
adox r9, [ rsp + 0x1e8 ]
seto r15b
inc rcx
mov r8, -0x1 
movzx r11, r11b
adox r11, r8
adox r10, [ rsp + 0x1a8 ]
adcx rdi, r14
adox rdi, [ rsp + 0x188 ]
adcx r9, [ rsp + 0x2a8 ]
mov rbp, [ rsp + 0x298 ]
seto r11b
inc r8
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox rbp, [ rsp + 0x210 ]
adcx r12, rbp
mov r14, 0xffffffffffffffff 
mulx rbp, r15, r14
mov rdx, [ rsp + 0x2a0 ]
setc cl
clc
adcx rdx, [ rsp + 0x290 ]
movzx r8, cl
mov r14, 0x0 
adox r8, r14
mov rcx, [ rsp + 0x280 ]
adcx rcx, [ rsp + 0x288 ]
mov r14, r15
adcx r14, [ rsp + 0x278 ]
mov [ rsp + 0x2b0 ], r14
mov r14, r15
adcx r14, rbp
mov [ rsp + 0x2b8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox r9, [ rsp + 0x1a0 ]
seto r11b
inc r14
mov r14, -0x1 
movzx rbx, bl
adox rbx, r14
adox r13, rdx
adcx r15, rbp
mov rbx, 0x0 
adcx rbp, rbx
adox rcx, r10
clc
movzx r11, r11b
adcx r11, r14
adcx r12, [ rsp + 0x208 ]
adcx r8, [ rsp + 0x200 ]
setc r10b
clc
adcx r13, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x198 ]
adox rdi, [ rsp + 0x2b0 ]
mov rdx, 0x100000001 
mulx rbx, r11, r13
adcx rdi, [ rsp + 0x190 ]
mov rbx, 0xfffffffffffffffe 
mov rdx, rbx
mulx r14, rbx, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x2c0 ], rdi
mov [ rsp + 0x2c8 ], r14
mulx r14, rdi, r11
adox r9, [ rsp + 0x2b8 ]
adox r15, r12
adcx r9, [ rsp + 0x1e0 ]
adox rbp, r8
movzx r12, r10b
mov r8, 0x0 
adox r12, r8
mov r10, 0xffffffff 
mov rdx, r11
mulx r8, r11, r10
mov r10, 0xffffffff00000000 
mov [ rsp + 0x2d0 ], r12
mov [ rsp + 0x2d8 ], rbp
mulx rbp, r12, r10
mov rdx, -0x2 
inc rdx
adox r12, r8
setc r8b
clc
adcx r11, r13
adox rbx, rbp
adcx r12, rcx
mov r11, rdi
adox r11, [ rsp + 0x2c8 ]
mov r13, rdi
adox r13, r14
adcx rbx, [ rsp + 0x2c0 ]
seto cl
inc rdx
adox r12, [ rsp + 0x28 ]
adox rbx, [ rsp + 0x38 ]
mov rbp, r14
setc dl
clc
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rbp, rdi
mov rdi, 0x0 
adcx r14, rdi
clc
movzx rdx, dl
adcx rdx, r10
adcx r9, r11
adox r9, [ rsp + 0xf8 ]
seto r11b
dec rdi
movzx r8, r8b
adox r8, rdi
adox r15, [ rsp + 0x1d8 ]
mov r10, [ rsp + 0x2d8 ]
adox r10, [ rsp + 0x1f8 ]
movzx r8, byte [ rsp + 0x1f0 ]
mov rcx, [ rsp + 0x1c0 ]
lea r8, [ r8 + rcx ]
adcx r13, r15
adox r8, [ rsp + 0x2d0 ]
seto cl
inc rdi
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox r13, [ rsp + 0xf0 ]
mov r11, 0x100000001 
mov rdx, r11
mulx r15, r11, r12
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rdi, r15, r11
adcx rbp, r10
mov r10, 0xffffffff00000000 
mov rdx, r10
mov [ rsp + 0x2e0 ], r13
mulx r13, r10, r11
adox rbp, [ rsp + 0xe8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x2e8 ], rbp
mov [ rsp + 0x2f0 ], r9
mulx r9, rbp, r11
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x2f8 ], rbx
mov byte [ rsp + 0x300 ], cl
mulx rcx, rbx, r11
seto r11b
mov rdx, -0x2 
inc rdx
adox r10, r9
adox rbx, r13
mov r13, r15
adox r13, rcx
mov r9, r15
adox r9, rdi
adcx r14, r8
setc r8b
clc
movzx r11, r11b
adcx r11, rdx
adcx r14, [ rsp + 0x1b8 ]
adox r15, rdi
setc r11b
clc
adcx rbp, r12
movzx rbp, r8b
movzx r12, byte [ rsp + 0x300 ]
lea rbp, [ rbp + r12 ]
adcx r10, [ rsp + 0x2f8 ]
mov r12, 0x0 
adox rdi, r12
adcx rbx, [ rsp + 0x2f0 ]
setc cl
mov r8, r10
mov rdx, 0xffffffff 
sub r8, rdx
mov r12, rbx
mov rdx, 0xffffffff00000000 
sbb r12, rdx
mov rdx, 0x0 
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r13, [ rsp + 0x2e0 ]
adox r9, [ rsp + 0x2e8 ]
adox r15, r14
seto r14b
mov rcx, r13
mov rdx, 0xfffffffffffffffe 
sbb rcx, rdx
mov rdx, r9
mov [ rsp + 0x308 ], r12
mov r12, 0xffffffffffffffff 
sbb rdx, r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r11, r11b
adox r11, r12
adox rbp, [ rsp + 0x1d0 ]
seto r11b
inc r12
mov r12, -0x1 
movzx r14, r14b
adox r14, r12
adox rbp, rdi
movzx rdi, r11b
mov r14, 0x0 
adox rdi, r14
mov r11, r15
mov r14, 0xffffffffffffffff 
sbb r11, r14
mov r12, rbp
sbb r12, r14
sbb rdi, 0x00000000
cmovc r8, r10
cmovc rcx, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], rcx
cmovc r12, rbp
cmovc r11, r15
mov [ rdi + 0x28 ], r12
mov [ rdi + 0x0 ], r8
mov [ rdi + 0x20 ], r11
cmovc rdx, r9
mov [ rdi + 0x18 ], rdx
mov r10, [ rsp + 0x308 ]
cmovc r10, rbx
mov [ rdi + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 912
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2524
; seed 0858333718086986 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 26516 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=82, initial num_batches=31): 747 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.028171669935133505
; number reverted permutation / tried permutation: 314 / 495 =63.434%
; number reverted decision / tried decision: 303 / 504 =60.119%
; validated in 22.246s
