SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 968
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rdi
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rax
mulx rax, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rax
mov [ rsp - 0x18 ], r10
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], rdi
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], r11
mulx r11, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r11
mov [ rsp + 0x38 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r14
mulx r14, rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r14
mulx r14, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r14
mov [ rsp + 0x78 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r14
mulx r14, rdi, [ rsi + 0x8 ]
test al, al
adox rdi, rbp
mov rdx, 0x100000001 
mov [ rsp + 0xa0 ], rdi
mulx rdi, rbp, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], r13
mulx r13, rdi, rbp
adcx r11, rcx
mov rcx, 0xffffffff 
mov rdx, rcx
mov [ rsp + 0xc0 ], r11
mulx r11, rcx, rbp
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xc8 ], r13
mov [ rsp + 0xd0 ], rdi
mulx rdi, r13, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], rdi
mov [ rsp + 0xe0 ], r13
mulx r13, rdi, [ rsi + 0x0 ]
setc dl
clc
adcx rcx, rbx
mov cl, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r11
mov byte [ rsp + 0xf8 ], cl
mulx rcx, r11, [ rsi + 0x10 ]
adox rax, r14
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x100 ], rax
mulx rax, r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rax
mulx rax, rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x110 ], r14
mov [ rsp + 0x118 ], rdi
mulx rdi, r14, [ rsi + 0x28 ]
adox r8, r10
setc dl
clc
adcx r14, r15
setc r15b
clc
adcx rbp, r13
adcx r11, rax
mov r10b, dl
mov rdx, [ rsi + 0x0 ]
mulx rax, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r14
mov [ rsp + 0x128 ], r11
mulx r11, r14, [ rsi + 0x18 ]
adox r13, r9
adcx r12, rcx
mov rdx, [ rsp + 0xa8 ]
adcx rdx, [ rsp + 0xb8 ]
setc r9b
clc
adcx rbx, [ rsp + 0x88 ]
adcx r14, [ rsp + 0x118 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], r14
mov [ rsp + 0x138 ], rbx
mulx rbx, r14, rdx
seto dl
mov [ rsp + 0x140 ], rcx
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox rdi, [ rsp + 0x48 ]
mov r15, [ rsp - 0x8 ]
adox r15, [ rsp + 0x8 ]
mov rcx, [ rsp - 0x10 ]
adox rcx, [ rsp + 0x68 ]
mov [ rsp + 0x148 ], rcx
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adcx r14, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], r14
mulx r14, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r14
mov [ rsp + 0x170 ], r12
mulx r12, r14, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x58 ]
adox rdx, [ rsp + 0x60 ]
mov [ rsp + 0x178 ], rdx
seto dl
mov [ rsp + 0x180 ], r12
mov r12, 0x0 
dec r12
movzx r9, r9b
adox r9, r12
adox r14, [ rsp + 0x0 ]
mov r9b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x190 ], r9b
mov [ rsp + 0x198 ], r13
mulx r13, r9, [ rsi + 0x20 ]
setc dl
clc
adcx r9, [ rsp + 0x28 ]
mov [ rsp + 0x1a0 ], r9
seto r9b
mov [ rsp + 0x1a8 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox rbx, r15
adox r11, rdi
mov r15, [ rsp + 0x40 ]
seto dil
movzx rdx, byte [ rsp + 0xf8 ]
inc rbp
mov rbp, -0x1 
adox rdx, rbp
adox r15, [ rsp - 0x28 ]
mov rdx, [ rsp - 0x18 ]
adox rdx, [ rsp - 0x30 ]
adcx r13, [ rsp + 0x98 ]
setc bpl
clc
mov [ rsp + 0x1b0 ], r13
mov r13, -0x1 
movzx rcx, cl
adcx rcx, r13
adcx rax, [ rsp - 0x38 ]
mov rcx, [ rsp - 0x40 ]
mov r13, 0x0 
adcx rcx, r13
mov [ rsp + 0x1b8 ], r11
mov r11, [ rsp + 0xe0 ]
clc
adcx r11, [ rsp + 0xf0 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], rbx
mov byte [ rsp + 0x1c8 ], dil
mulx rdi, rbx, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x20 ]
adox rdx, [ rsp + 0x78 ]
mov [ rsp + 0x1d0 ], rdx
mov rdx, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0x110 ]
mov [ rsp + 0x1d8 ], r13
mov r13, [ rsp + 0xd0 ]
mov [ rsp + 0x1e0 ], r15
mov r15, r13
adcx r15, [ rsp + 0x108 ]
adox rbx, [ rsp + 0x70 ]
mov [ rsp + 0x1e8 ], rbx
seto bl
mov byte [ rsp + 0x1f0 ], r9b
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx rbp, bpl
adox rbp, r9
adox r12, [ rsp + 0x90 ]
movzx rbp, bl
lea rbp, [ rbp + rdi ]
adox r14, [ rsp + 0x38 ]
setc dil
clc
movzx r10, r10b
adcx r10, r9
adcx r11, [ rsp + 0xa0 ]
seto r10b
inc r9
adox r11, [ rsp + 0xe8 ]
mov rbx, 0x100000001 
xchg rdx, r11
mov [ rsp + 0x1f8 ], r14
mulx r14, r9, rbx
mov r14, [ rsp + 0x30 ]
seto bl
mov [ rsp + 0x200 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox r14, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x100 ]
adcx r15, r8
seto r8b
inc r12
mov r10, -0x1 
movzx rbx, bl
adox rbx, r10
adox r11, [ rsp + 0x1a8 ]
mov rbx, r13
setc r12b
clc
movzx rdi, dil
adcx rdi, r10
adcx rbx, [ rsp + 0xc8 ]
adox r15, [ rsp + 0x128 ]
adcx r13, [ rsp + 0xc8 ]
mov rdi, [ rsp + 0xc8 ]
mov r10, 0x0 
adcx rdi, r10
mov r10, 0xffffffffffffffff 
xchg rdx, r10
mov [ rsp + 0x208 ], r14
mov [ rsp + 0x210 ], rbp
mulx rbp, r14, r9
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx rbx, [ rsp + 0x198 ]
mov r12, 0xffffffff 
mov rdx, r9
mov [ rsp + 0x218 ], rbp
mulx rbp, r9, r12
adcx r13, rax
adox rbx, [ rsp + 0x170 ]
mov rax, 0xffffffff00000000 
mov [ rsp + 0x220 ], rbx
mulx rbx, r12, rax
movzx rax, r8b
mov [ rsp + 0x228 ], r14
mov r14, [ rsp + 0x10 ]
lea rax, [ rax + r14 ]
mov r14, 0xfffffffffffffffe 
mov [ rsp + 0x230 ], rax
mulx rax, r8, r14
adcx rdi, rcx
adox r13, [ rsp + 0x140 ]
movzx rcx, byte [ rsp + 0x1f0 ]
mov rdx, [ rsp + 0x180 ]
lea rcx, [ rcx + rdx ]
adox rdi, [ rsp + 0x188 ]
setc dl
clc
adcx r9, r10
movzx r9, dl
adox r9, rcx
seto r10b
mov rdx, -0x2 
inc rdx
adox r12, rbp
adcx r12, r11
adox r8, rbx
adcx r8, r15
adox rax, [ rsp + 0x228 ]
mov r11, [ rsp + 0x218 ]
mov r15, r11
adox r15, [ rsp + 0x228 ]
adcx rax, [ rsp + 0x220 ]
setc bpl
clc
adcx r12, [ rsp + 0xb0 ]
mov rbx, 0x100000001 
mov rdx, r12
mulx rcx, r12, rbx
mov rcx, 0xffffffff00000000 
xchg rdx, r12
mulx rbx, r14, rcx
mov rcx, r11
adox rcx, [ rsp + 0x228 ]
mov byte [ rsp + 0x238 ], r10b
mov r10, 0xfffffffffffffffe 
mov [ rsp + 0x240 ], r9
mov [ rsp + 0x248 ], rcx
mulx rcx, r9, r10
mov r10, 0x0 
adox r11, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x250 ], r11
mov [ rsp + 0x258 ], rdi
mulx rdi, r11, r10
adcx r8, [ rsp + 0xc0 ]
mov r10, 0xffffffff 
mov [ rsp + 0x260 ], r8
mov [ rsp + 0x268 ], rdi
mulx rdi, r8, r10
mov rdx, -0x2 
inc rdx
adox r14, rdi
adcx rax, [ rsp + 0x1e0 ]
adox r9, rbx
mov rbx, r11
adox rbx, rcx
setc cl
clc
movzx rbp, bpl
adcx rbp, rdx
adcx r13, r15
mov r15, [ rsp + 0x258 ]
adcx r15, [ rsp + 0x248 ]
mov rbp, r11
adox rbp, [ rsp + 0x268 ]
adox r11, [ rsp + 0x268 ]
seto dil
inc rdx
adox r8, r12
mov r8, [ rsp + 0x240 ]
adcx r8, [ rsp + 0x250 ]
movzx r12, byte [ rsp + 0x238 ]
adcx r12, rdx
adox r14, [ rsp + 0x260 ]
clc
adcx r14, [ rsp + 0x80 ]
mov rdx, 0x100000001 
mov [ rsp + 0x270 ], r11
mulx r11, r10, r14
adox r9, rax
adcx r9, [ rsp + 0x138 ]
movzx r11, dil
mov rax, [ rsp + 0x268 ]
lea r11, [ r11 + rax ]
mov rax, 0xfffffffffffffffe 
mov rdx, rax
mulx rdi, rax, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x278 ], r11
mov [ rsp + 0x280 ], rbp
mulx rbp, r11, r10
mov rdx, 0xffffffff 
mov [ rsp + 0x288 ], rbx
mov [ rsp + 0x290 ], rbp
mulx rbp, rbx, r10
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x298 ], r11
mov [ rsp + 0x2a0 ], rdi
mulx rdi, r11, r10
seto r10b
mov rdx, -0x2 
inc rdx
adox r11, rbp
adox rax, rdi
seto bpl
inc rdx
adox rbx, r14
adox r11, r9
seto bl
mov r14, -0x3 
inc r14
adox r11, [ rsp + 0x20 ]
seto r9b
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r13, [ rsp + 0x1d8 ]
adox r15, [ rsp + 0x1d0 ]
mov rcx, 0x100000001 
mov rdx, r11
mulx rdi, r11, rcx
adox r8, [ rsp + 0x1e8 ]
adox r12, [ rsp + 0x210 ]
mov rdi, [ rsp + 0x2a0 ]
seto r14b
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rbp, bpl
adox rbp, rcx
adox rdi, [ rsp + 0x298 ]
mov rbp, [ rsp + 0x298 ]
mov rcx, rbp
adox rcx, [ rsp + 0x290 ]
mov [ rsp + 0x2a8 ], rcx
mov rcx, 0xffffffff 
xchg rdx, rcx
mov [ rsp + 0x2b0 ], rdi
mov byte [ rsp + 0x2b8 ], r9b
mulx r9, rdi, r11
setc dl
clc
adcx rdi, rcx
adox rbp, [ rsp + 0x290 ]
seto dil
mov rcx, 0x0 
dec rcx
movzx r10, r10b
adox r10, rcx
adox r13, [ rsp + 0x288 ]
adox r15, [ rsp + 0x280 ]
movzx r10, byte [ rsp + 0x1c8 ]
mov rcx, [ rsp + 0x168 ]
lea r10, [ r10 + rcx ]
mov rcx, 0xffffffff00000000 
xchg rdx, r11
mov byte [ rsp + 0x2c0 ], dil
mov [ rsp + 0x2c8 ], rbp
mulx rbp, rdi, rcx
adox r8, [ rsp + 0x270 ]
setc cl
clc
adcx rdi, r9
seto r9b
mov [ rsp + 0x2d0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r11, r11b
adox r11, rbp
adox r13, [ rsp + 0x130 ]
adox r15, [ rsp + 0x160 ]
adox r8, [ rsp + 0x1c0 ]
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x2d8 ], r8
mulx r8, rbp, r11
setc r11b
clc
mov [ rsp + 0x2e0 ], r15
mov r15, -0x1 
movzx r9, r9b
adcx r9, r15
adcx r12, [ rsp + 0x278 ]
adox r12, [ rsp + 0x1b8 ]
movzx r9, r14b
mov r15, 0x0 
adcx r9, r15
clc
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx r13, rax
adox r10, r9
seto al
movzx rbx, byte [ rsp + 0x2b8 ]
inc r14
mov r15, -0x1 
adox rbx, r15
adox r13, [ rsp + 0x1a0 ]
setc bl
clc
movzx rcx, cl
adcx rcx, r15
adcx r13, rdi
setc cl
clc
adcx r13, [ rsp - 0x48 ]
seto dil
inc r15
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox rbp, [ rsp + 0x2d0 ]
mov r11, 0x100000001 
xchg rdx, r11
mulx r15, r9, r13
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, r9
mov byte [ rsp + 0x2e8 ], al
mov [ rsp + 0x2f0 ], r10
mulx r10, rax, r11
mov r11, 0xffffffff 
mov rdx, r11
mov [ rsp + 0x2f8 ], rbp
mulx rbp, r11, r9
mov rdx, rax
adox rdx, r8
mov r8, rax
adox r8, r10
mov [ rsp + 0x300 ], r8
mov r8, 0xffffffff00000000 
xchg rdx, r8
mov [ rsp + 0x308 ], r8
mov [ rsp + 0x310 ], r11
mulx r11, r8, r9
mov rdx, [ rsp + 0x2b0 ]
mov byte [ rsp + 0x318 ], cl
setc cl
clc
mov [ rsp + 0x320 ], r14
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx rdx, [ rsp + 0x2e0 ]
setc bl
clc
adcx r8, rbp
seto bpl
inc r14
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox rdx, [ rsp + 0x1b0 ]
mov rdi, 0xfffffffffffffffe 
xchg rdx, rdi
mov [ rsp + 0x328 ], r8
mulx r8, r14, r9
mov r9, [ rsp + 0x2a8 ]
seto dl
mov byte [ rsp + 0x330 ], cl
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox r9, [ rsp + 0x2d8 ]
adcx r14, r11
adox r12, [ rsp + 0x2c8 ]
mov r11, r15
adcx r11, r8
mov rbx, r15
adcx rbx, [ rsp + 0x320 ]
mov r8, r10
seto cl
mov [ rsp + 0x338 ], rbx
mov rbx, 0x0 
dec rbx
movzx rbp, bpl
adox rbp, rbx
adox r8, rax
seto al
movzx rbp, byte [ rsp + 0x318 ]
inc rbx
mov rbx, -0x1 
adox rbp, rbx
adox rdi, [ rsp + 0x2f8 ]
seto bpl
movzx rbx, byte [ rsp + 0x330 ]
mov [ rsp + 0x340 ], r11
mov r11, 0x0 
dec r11
adox rbx, r11
adox rdi, [ rsp + 0x120 ]
movzx rbx, al
lea rbx, [ rbx + r10 ]
seto r10b
inc r11
mov rax, -0x1 
movzx rdx, dl
adox rdx, rax
adox r9, [ rsp + 0x200 ]
adcx r15, [ rsp + 0x320 ]
mov rdx, [ rsp + 0x320 ]
adcx rdx, r11
clc
adcx r13, [ rsp + 0x310 ]
movzx r13, byte [ rsp + 0x2c0 ]
mov r11, [ rsp + 0x290 ]
lea r13, [ r13 + r11 ]
adcx rdi, [ rsp + 0x328 ]
seto r11b
inc rax
mov rax, -0x1 
movzx rcx, cl
adox rcx, rax
adox r13, [ rsp + 0x2f0 ]
setc cl
clc
movzx r11, r11b
adcx r11, rax
adcx r12, [ rsp + 0x1f8 ]
movzx r11, byte [ rsp + 0x2e8 ]
mov rax, 0x0 
adox r11, rax
dec rax
movzx rbp, bpl
adox rbp, rax
adox r9, [ rsp + 0x308 ]
adcx r13, [ rsp + 0x208 ]
adcx r11, [ rsp + 0x230 ]
adox r12, [ rsp + 0x300 ]
adox r8, r13
adox rbx, r11
seto bpl
adc bpl, 0x0
movzx rbp, bpl
add r10b, 0x7F
adox r9, [ rsp + 0x158 ]
movzx rcx, cl
adcx rcx, rax
adcx r9, r14
movzx r14, byte [ rsp + 0x190 ]
mov r10, [ rsp + 0x50 ]
lea r14, [ r14 + r10 ]
adox r12, [ rsp + 0x150 ]
adcx r12, [ rsp + 0x340 ]
adox r8, [ rsp + 0x148 ]
adox rbx, [ rsp + 0x178 ]
adcx r8, [ rsp + 0x338 ]
adcx r15, rbx
setc r10b
seto cl
mov r13, rdi
mov r11, 0xffffffff 
sub r13, r11
inc rax
mov rbx, -0x1 
movzx rbp, bpl
movzx rcx, cl
adox rcx, rbx
adox r14, rbp
setc bpl
clc
movzx r10, r10b
adcx r10, rbx
adcx r14, rdx
setc dl
seto cl
movzx r10, bpl
add r10, -0x1
mov r10, r9
mov rbp, 0xffffffff00000000 
sbb r10, rbp
mov rax, r12
mov rbx, 0xfffffffffffffffe 
sbb rax, rbx
mov rbx, r8
mov rbp, 0xffffffffffffffff 
sbb rbx, rbp
movzx r11, dl
movzx rcx, cl
lea r11, [ r11 + rcx ]
mov rcx, r15
sbb rcx, rbp
mov rdx, r14
sbb rdx, rbp
sbb r11, 0x00000000
cmovc r13, rdi
cmovc r10, r9
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r13
mov [ r11 + 0x8 ], r10
cmovc rdx, r14
mov [ r11 + 0x28 ], rdx
cmovc rbx, r8
cmovc rcx, r15
mov [ r11 + 0x20 ], rcx
cmovc rax, r12
mov [ r11 + 0x18 ], rbx
mov [ r11 + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 968
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1222
; seed 2114371213324087 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 27614 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=90, initial num_batches=31): 772 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.027956833490258563
; number reverted permutation / tried permutation: 273 / 496 =55.040%
; number reverted decision / tried decision: 287 / 503 =57.058%
; validated in 19.304s
