SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 1024
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r11
mulx r11, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r13
mulx r13, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], rbp
mulx rbp, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], r10
mulx r10, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r11
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r8
mulx r8, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r9
mulx r9, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], rdi
mulx rdi, r12, [ rax + 0x0 ]
test al, al
adox rcx, rdi
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc8 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r14
mulx r14, r12, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe0 ], r14
mov [ rsp + 0xe8 ], r12
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], r10
mulx r10, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r10
mov [ rsp + 0x108 ], rbp
mulx rbp, r10, [ rax + 0x20 ]
mov rdx, 0x100000001 
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], r10
mulx r10, rbp, r14
mov r10, 0xffffffff00000000 
mov rdx, r10
mov [ rsp + 0x120 ], r8
mulx r8, r10, rbp
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r10
mulx r10, r8, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x138 ], r10
mov [ rsp + 0x140 ], r8
mulx r8, r10, rbp
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x148 ], r8
mov [ rsp + 0x150 ], r10
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rbx
mulx rbx, r13, [ rax + 0x10 ]
adcx rdi, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x168 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
adox r13, r9
adox r11, rbx
adcx r8, rcx
adcx r15, r10
seto dl
mov r9, -0x2 
inc r9
adox r12, [ rsp + 0x160 ]
mov rcx, 0xffffffff 
xchg rdx, rbp
mulx rbx, r10, rcx
mov rdx, [ rax + 0x10 ]
mulx rcx, r9, [ rsi + 0x18 ]
adox rdi, [ rsp + 0x158 ]
mov rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x170 ], rdi
seto dil
mov [ rsp + 0x178 ], r12
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox rdx, [ rsp + 0x120 ]
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x180 ], r11
mulx r11, r12, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x108 ]
mov [ rsp + 0x188 ], rbp
seto bpl
mov [ rsp + 0x190 ], r13
mov r13, -0x2 
inc r13
adox rdx, [ rsp + 0xf0 ]
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x198 ], r15
mov byte [ rsp + 0x1a0 ], dil
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1a8 ], r13
mov [ rsp + 0x1b0 ], r8
mulx r8, r13, [ rax + 0x0 ]
seto dl
mov [ rsp + 0x1b8 ], r13
mov r13, -0x2 
inc r13
adox r12, r8
seto r8b
inc r13
adox r15, [ rsp + 0xd8 ]
mov r13, [ rsp + 0x98 ]
adcx r13, [ rsp + 0xa0 ]
mov [ rsp + 0x1c0 ], r12
seto r12b
mov [ rsp + 0x1c8 ], r15
mov r15, -0x2 
inc r15
adox rbx, [ rsp + 0x130 ]
mov r15, [ rsp + 0x128 ]
adox r15, [ rsp + 0x140 ]
mov [ rsp + 0x1d0 ], r13
mov r13, [ rsp + 0x150 ]
mov [ rsp + 0x1d8 ], r15
mov r15, r13
adox r15, [ rsp + 0x138 ]
mov [ rsp + 0x1e0 ], r15
mov r15, [ rsp + 0x90 ]
mov [ rsp + 0x1e8 ], rcx
seto cl
mov [ rsp + 0x1f0 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox r15, [ rsp + 0x100 ]
mov rdx, [ rsp + 0x60 ]
adox rdx, [ rsp + 0x58 ]
mov rbx, [ rsp + 0x50 ]
adox rbx, [ rsp + 0x30 ]
mov [ rsp + 0x1f8 ], rbx
mov rbx, [ rsp + 0x20 ]
adcx rbx, [ rsp + 0x18 ]
mov [ rsp + 0x200 ], rdx
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0x208 ], r15
seto r15b
mov [ rsp + 0x210 ], rbx
mov rbx, 0x0 
dec rbx
movzx rbp, bpl
adox rbp, rbx
adox rdx, [ rsp - 0x10 ]
mov rbp, [ rsp - 0x20 ]
mov rbx, 0x0 
adox rbp, rbx
dec rbx
movzx r8, r8b
adox r8, rbx
adox r11, [ rsp + 0x10 ]
setc r8b
clc
adcx r10, r14
seto r10b
inc rbx
mov r14, -0x1 
movzx r12, r12b
adox r12, r14
adox rdi, r9
mov r9, [ rsp + 0x168 ]
adcx r9, [ rsp + 0x1f0 ]
movzx r12, r8b
mov rbx, [ rsp - 0x28 ]
lea r12, [ r12 + rbx ]
mov rbx, [ rsp + 0x1e8 ]
adox rbx, [ rsp + 0xe8 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x218 ], r11
mulx r11, r14, [ rax + 0x28 ]
mov rdx, [ rsp + 0xe0 ]
adox rdx, [ rsp - 0x30 ]
mov [ rsp + 0x220 ], rdx
mov rdx, [ rsp + 0x1b0 ]
adcx rdx, [ rsp + 0x1d8 ]
mov [ rsp + 0x228 ], rbx
mov rbx, [ rsp + 0x70 ]
mov [ rsp + 0x230 ], rdi
setc dil
mov [ rsp + 0x238 ], rbp
movzx rbp, byte [ rsp + 0x1a0 ]
clc
mov [ rsp + 0x240 ], r8
mov r8, -0x1 
adcx rbp, r8
adcx rbx, [ rsp - 0x18 ]
mov rbp, [ rsp - 0x38 ]
adox rbp, [ rsp + 0xc0 ]
mov r8, [ rsp + 0x68 ]
adcx r8, [ rsp + 0x0 ]
mov [ rsp + 0x248 ], rbp
mov rbp, [ rsp + 0x8 ]
mov [ rsp + 0x250 ], r8
seto r8b
mov [ rsp + 0x258 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rbp, [ rsp + 0x80 ]
mov r10, [ rsp - 0x40 ]
setc bl
clc
mov [ rsp + 0x260 ], rbp
mov rbp, -0x1 
movzx r15, r15b
adcx r15, rbp
adcx r10, [ rsp + 0x40 ]
mov r15, [ rsp + 0x38 ]
mov rbp, 0x0 
adcx r15, rbp
mov rbp, [ rsp + 0x118 ]
adox rbp, [ rsp + 0x78 ]
clc
adcx r9, [ rsp + 0xd0 ]
adox r14, [ rsp + 0x110 ]
mov [ rsp + 0x268 ], r15
mov r15, 0x100000001 
xchg rdx, r15
mov [ rsp + 0x270 ], r10
mov [ rsp + 0x278 ], r14
mulx r14, r10, r9
mov r14, 0xffffffff 
mov rdx, r14
mov [ rsp + 0x280 ], rbp
mulx rbp, r14, r10
adcx r15, [ rsp + 0xc8 ]
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x288 ], r8b
mov [ rsp + 0x290 ], r15
mulx r15, r8, r10
setc dl
clc
adcx r14, r9
mov r14, r13
seto r9b
mov [ rsp + 0x298 ], r15
mov r15, 0x0 
dec r15
movzx rcx, cl
adox rcx, r15
adox r14, [ rsp + 0x148 ]
adox r13, [ rsp + 0x148 ]
mov rcx, [ rsp - 0x8 ]
seto r15b
mov [ rsp + 0x2a0 ], r8
mov r8, 0x0 
dec r8
movzx rbx, bl
adox rbx, r8
adox rcx, [ rsp + 0xb0 ]
mov rbx, [ rsp + 0x198 ]
setc r8b
clc
mov [ rsp + 0x2a8 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx rbx, [ rsp + 0x1e0 ]
seto dil
inc rcx
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox rbx, [ rsp + 0x190 ]
adcx r14, [ rsp + 0x1d0 ]
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x2b0 ], dil
mulx rdi, rcx, r10
movzx rdx, r9b
lea rdx, [ rdx + r11 ]
adcx r13, [ rsp + 0x210 ]
movzx r11, r15b
mov r9, [ rsp + 0x148 ]
lea r11, [ r11 + r9 ]
adox r14, [ rsp + 0x180 ]
adcx r11, r12
adox r13, [ rsp + 0x188 ]
mov r9, 0xffffffff00000000 
xchg rdx, r9
mulx r15, r12, r10
setc r10b
clc
adcx r12, rbp
adox r11, [ rsp + 0x240 ]
adcx rcx, r15
adcx rdi, [ rsp + 0x2a0 ]
setc bpl
clc
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r12, [ rsp + 0x290 ]
adcx rcx, rbx
seto r8b
inc r15
adox r12, [ rsp + 0x88 ]
mov rbx, 0x100000001 
mov rdx, r12
mulx r15, r12, rbx
mov r15, [ rsp + 0x2a0 ]
mov rbx, r15
mov [ rsp + 0x2b8 ], r9
seto r9b
mov byte [ rsp + 0x2c0 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rbx, [ rsp + 0x298 ]
adox r15, [ rsp + 0x298 ]
adcx rdi, r14
mov r14, 0xffffffff 
xchg rdx, r12
mulx r10, rbp, r14
adcx rbx, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x2c8 ], r8b
mulx r8, r14, r13
mov r13, 0xffffffff00000000 
mov [ rsp + 0x2d0 ], rbx
mov [ rsp + 0x2d8 ], rdi
mulx rdi, rbx, r13
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0x2e0 ], rcx
mov byte [ rsp + 0x2e8 ], r9b
mulx r9, rcx, r13
mov rdx, [ rsp + 0x298 ]
mov r13, 0x0 
adox rdx, r13
mov [ rsp + 0x2f0 ], rdx
mov rdx, -0x3 
inc rdx
adox rbp, r12
adcx r15, r11
setc bpl
clc
adcx rbx, r10
adcx rcx, rdi
mov r11, r14
adcx r11, r9
mov r12, r14
adcx r12, r8
mov r10, [ rsp + 0x178 ]
seto dil
movzx r9, byte [ rsp + 0x2e8 ]
dec r13
adox r9, r13
adox r10, [ rsp + 0x2e0 ]
mov r9, [ rsp + 0x2d8 ]
adox r9, [ rsp + 0x170 ]
adcx r14, r8
mov r13, 0x0 
adcx r8, r13
clc
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx r10, rbx
adcx rcx, r9
setc dil
clc
adcx r10, [ rsp - 0x48 ]
mov rbx, [ rsp + 0x258 ]
adox rbx, [ rsp + 0x2d0 ]
mov r9, [ rsp + 0x238 ]
seto r13b
movzx rdx, byte [ rsp + 0x2c8 ]
mov [ rsp + 0x2f8 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
mov [ rsp + 0x300 ], r10
movzx r10, byte [ rsp + 0x2c0 ]
adox rdx, r8
adox r9, r10
seto r10b
inc r8
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox r15, [ rsp + 0x250 ]
setc r13b
clc
movzx rdi, dil
adcx rdi, rdx
adcx rbx, r11
setc r11b
clc
movzx rbp, bpl
adcx rbp, rdx
adcx r9, [ rsp + 0x2f0 ]
adox r9, [ rsp + 0x2a8 ]
movzx rbp, r10b
adcx rbp, r8
movzx rdi, byte [ rsp + 0x2b0 ]
mov r10, [ rsp + 0xa8 ]
lea rdi, [ rdi + r10 ]
clc
movzx r13, r13b
adcx r13, rdx
adcx rcx, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x230 ]
adox rdi, rbp
seto r10b
dec r8
movzx r11, r11b
adox r11, r8
adox r15, r12
adox r14, r9
adcx r15, [ rsp + 0x228 ]
mov rdx, 0x100000001 
mulx r13, r12, [ rsp + 0x300 ]
mov r13, 0xfffffffffffffffe 
mov rdx, r12
mulx r11, r12, r13
movzx r9, byte [ rsp + 0x288 ]
mov rbp, [ rsp + 0xb8 ]
lea r9, [ r9 + rbp ]
mov rbp, 0xffffffffffffffff 
mulx r13, r8, rbp
mov rbp, 0xffffffff00000000 
mov [ rsp + 0x308 ], r15
mov [ rsp + 0x310 ], rbx
mulx rbx, r15, rbp
adcx r14, [ rsp + 0x220 ]
adox rdi, [ rsp + 0x2f8 ]
mov rbp, 0xffffffff 
mov [ rsp + 0x318 ], r14
mov [ rsp + 0x320 ], rcx
mulx rcx, r14, rbp
adcx rdi, [ rsp + 0x248 ]
movzx rdx, r10b
mov rbp, 0x0 
adox rdx, rbp
adcx r9, rdx
mov r10, -0x3 
inc r10
adox r15, rcx
adox r12, rbx
mov rbx, r8
adox rbx, r11
setc r11b
clc
adcx r14, [ rsp + 0x300 ]
mov r14, r8
adox r14, r13
adcx r15, [ rsp + 0x320 ]
adcx r12, [ rsp + 0x310 ]
adcx rbx, [ rsp + 0x308 ]
adox r8, r13
adcx r14, [ rsp + 0x318 ]
adcx r8, rdi
setc cl
clc
adcx r15, [ rsp + 0x1b8 ]
adcx r12, [ rsp + 0x1c0 ]
mov rdi, 0x100000001 
mov rdx, r15
mulx rbp, r15, rdi
mov rbp, 0x0 
adox r13, rbp
adcx rbx, [ rsp + 0x218 ]
mov rbp, 0xffffffff00000000 
xchg rdx, r15
mulx rdi, r10, rbp
mov rbp, 0x0 
dec rbp
movzx rcx, cl
adox rcx, rbp
adox r9, r13
mov rcx, 0xffffffffffffffff 
mulx rbp, r13, rcx
movzx rcx, r11b
mov [ rsp + 0x328 ], r9
mov r9, 0x0 
adox rcx, r9
mov r11, 0xffffffff 
mov [ rsp + 0x330 ], rcx
mulx rcx, r9, r11
mov r11, -0x2 
inc r11
adox r9, r15
mov r9, 0xfffffffffffffffe 
mulx r11, r15, r9
setc dl
clc
adcx r10, rcx
adcx r15, rdi
mov rdi, r13
adcx rdi, r11
mov rcx, r13
adcx rcx, rbp
adcx r13, rbp
setc r11b
clc
mov r9, -0x1 
movzx rdx, dl
adcx rdx, r9
adcx r14, [ rsp + 0x260 ]
adox r10, r12
adox r15, rbx
adox rdi, r14
adcx r8, [ rsp + 0x280 ]
seto r12b
inc r9
adox r10, [ rsp + 0x28 ]
mov rdx, 0x100000001 
mulx r14, rbx, r10
adox r15, [ rsp + 0x1a8 ]
mov r14, 0xffffffff00000000 
mov rdx, r14
mulx r9, r14, rbx
mov rdx, [ rsp + 0x278 ]
adcx rdx, [ rsp + 0x328 ]
mov byte [ rsp + 0x338 ], r11b
mov r11, [ rsp + 0x330 ]
adcx r11, [ rsp + 0x2b8 ]
adox rdi, [ rsp + 0x208 ]
mov [ rsp + 0x340 ], r11
setc r11b
clc
mov [ rsp + 0x348 ], rdi
mov rdi, -0x1 
movzx r12, r12b
adcx r12, rdi
adcx r8, rcx
adox r8, [ rsp + 0x200 ]
adcx r13, rdx
mov rcx, 0xffffffff 
mov rdx, rbx
mulx r12, rbx, rcx
setc dil
clc
adcx r14, r12
mov r12, 0xfffffffffffffffe 
mov byte [ rsp + 0x350 ], r11b
mulx r11, rcx, r12
adcx rcx, r9
adox r13, [ rsp + 0x1f8 ]
mov r9, 0xffffffffffffffff 
mov byte [ rsp + 0x358 ], dil
mulx rdi, r12, r9
mov rdx, r12
adcx rdx, r11
mov r11, r12
adcx r11, rdi
adcx r12, rdi
seto r9b
mov [ rsp + 0x360 ], r12
mov r12, -0x2 
inc r12
adox rbx, r10
adox r14, r15
adox rcx, [ rsp + 0x348 ]
movzx rbx, byte [ rsp + 0x338 ]
lea rbp, [ rbp + rbx ]
setc bl
seto r10b
mov r15, r14
mov r12, 0xffffffff 
sub r15, r12
mov r12, rcx
mov [ rsp + 0x368 ], r15
mov r15, 0xffffffff00000000 
sbb r12, r15
mov r15, 0x0 
dec r15
movzx r10, r10b
adox r10, r15
adox r8, rdx
adox r11, r13
seto r13b
mov rdx, r8
mov r10, 0xfffffffffffffffe 
sbb rdx, r10
movzx r15, byte [ rsp + 0x358 ]
mov r10, 0x0 
dec r10
adox r15, r10
adox rbp, [ rsp + 0x340 ]
seto r15b
mov r10, r11
mov [ rsp + 0x370 ], rdx
mov rdx, 0xffffffffffffffff 
sbb r10, rdx
movzx rdx, r15b
mov [ rsp + 0x378 ], r10
movzx r10, byte [ rsp + 0x350 ]
lea rdx, [ rdx + r10 ]
mov r10, 0x0 
dec r10
movzx r9, r9b
adox r9, r10
adox rbp, [ rsp + 0x270 ]
setc r9b
clc
movzx r13, r13b
adcx r13, r10
adcx rbp, [ rsp + 0x360 ]
adox rdx, [ rsp + 0x268 ]
movzx r13, bl
lea r13, [ r13 + rdi ]
setc dil
seto bl
movzx r15, r9b
add r15, -0x1
mov r9, rbp
mov r15, 0xffffffffffffffff 
sbb r9, r15
inc r10
mov r10, -0x1 
movzx rdi, dil
adox rdi, r10
adox rdx, r13
movzx rdi, bl
mov r13, 0x0 
adox rdi, r13
mov rbx, rdx
sbb rbx, r15
sbb rdi, 0x00000000
cmovc r12, rcx
mov rdi, [ rsp + 0x370 ]
cmovc rdi, r8
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r12
cmovc r9, rbp
cmovc rbx, rdx
mov [ rcx + 0x20 ], r9
mov [ rcx + 0x28 ], rbx
mov [ rcx + 0x10 ], rdi
mov r8, [ rsp + 0x368 ]
cmovc r8, r14
mov [ rcx + 0x0 ], r8
mov r14, [ rsp + 0x378 ]
cmovc r14, r11
mov [ rcx + 0x18 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1024
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2493
; seed 3356014320470077 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 27287 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=83, initial num_batches=31): 744 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.027265730934144465
; number reverted permutation / tried permutation: 326 / 498 =65.462%
; number reverted decision / tried decision: 306 / 501 =61.078%
; validated in 22.843s
