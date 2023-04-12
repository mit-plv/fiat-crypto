SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 936
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r14
mulx r14, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], rbp
mulx rbp, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], r8
mulx r8, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r12
mulx r12, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], r8
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], rbp
mulx rbp, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], rcx
mulx rcx, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], rcx
mov [ rsp + 0x50 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], rcx
mulx rcx, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], rbp
mulx rbp, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x78 ], rcx
mov [ rsp + 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], rcx
mulx rcx, rbx, [ rax + 0x10 ]
add r15, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r15
mulx r15, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r9
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xc0 ], r9
mov [ rsp + 0xc8 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], r12
mulx r12, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], r15
mulx r15, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r14, r11
adox r9, r13
mov r11, 0x100000001 
mov rdx, r12
mulx r13, r12, r11
mov r13, 0xffffffff 
xchg rdx, r13
mov [ rsp + 0x100 ], r9
mulx r9, r11, r12
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x108 ], r14
mov [ rsp + 0x110 ], rcx
mulx rcx, r14, r12
setc dl
clc
adcx r14, r9
setc r9b
clc
adcx r11, r13
mov r11, 0xfffffffffffffffe 
xchg rdx, r11
mov [ rsp + 0x118 ], r14
mulx r14, r13, r12
adox r10, r8
setc r8b
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rdi, rbx
mov rdx, [ rax + 0x8 ]
mulx r11, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], rdi
mulx rdi, r10, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x130 ], r14
mov r14, -0x2 
inc r14
adox rbp, r15
mov r15b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x138 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
mov rdx, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0xf8 ]
adox r10, [ rsp + 0xd0 ]
adox rdi, [ rsp + 0xb8 ]
adcx r14, [ rsp + 0xb0 ]
mov [ rsp + 0x140 ], rdi
mov rdi, [ rsp + 0xa0 ]
mov [ rsp + 0x148 ], r10
setc r10b
clc
adcx rdi, [ rsp + 0x90 ]
mov [ rsp + 0x150 ], rdi
mov rdi, [ rsp + 0x80 ]
adox rdi, [ rsp + 0x70 ]
mov [ rsp + 0x158 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r14
mov byte [ rsp + 0x168 ], r8b
mulx r8, r14, [ rax + 0x28 ]
setc dl
clc
mov [ rsp + 0x170 ], rdi
mov rdi, -0x1 
movzx r9, r9b
adcx r9, rdi
adcx rcx, r13
adox r14, [ rsp + 0x68 ]
mov r9b, dl
mov rdx, [ rax + 0x10 ]
mulx rdi, r13, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x30 ]
mov [ rsp + 0x178 ], r14
setc r14b
clc
mov [ rsp + 0x180 ], rcx
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rdx, [ rsp + 0x28 ]
mov r15, 0x0 
adox r8, r15
mov r15, [ rsp + 0x98 ]
inc rcx
mov rcx, -0x1 
movzx r9, r9b
adox r9, rcx
adox r15, [ rsp + 0xc8 ]
mov r9, [ rsp + 0xc0 ]
adox r9, [ rsp + 0xe8 ]
mov rcx, [ rsp + 0x0 ]
adcx rcx, [ rsp + 0x20 ]
mov [ rsp + 0x188 ], rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r9
mov [ rsp + 0x198 ], r15
mulx r15, r9, [ rax + 0x10 ]
mov rdx, [ rsp - 0x8 ]
mov [ rsp + 0x1a0 ], rcx
setc cl
clc
adcx rdx, [ rsp + 0x60 ]
adcx r13, [ rsp + 0x58 ]
mov [ rsp + 0x1a8 ], r13
movzx r13, cl
mov [ rsp + 0x1b0 ], rdx
mov rdx, [ rsp + 0x18 ]
lea r13, [ r13 + rdx ]
setc dl
clc
mov rcx, -0x1 
movzx r10, r10b
adcx r10, rcx
adcx rbp, [ rsp - 0x10 ]
setc r10b
clc
adcx rbx, [ rsp + 0x110 ]
mov cl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], r8
mulx r8, r13, [ rsi + 0x0 ]
mov rdx, [ rsp + 0xe0 ]
adox rdx, [ rsp - 0x18 ]
mov byte [ rsp + 0x1c8 ], r10b
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1d0 ], rbp
mov byte [ rsp + 0x1d8 ], r14b
mulx r14, rbp, [ rax + 0x20 ]
setc dl
clc
mov [ rsp + 0x1e0 ], r10
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rdi, [ rsp + 0x10 ]
seto cl
inc r10
mov r10, -0x1 
movzx rdx, dl
adox rdx, r10
adox r11, r9
setc r9b
movzx rdx, byte [ rsp + 0x168 ]
clc
adcx rdx, r10
adcx rbx, [ rsp + 0x118 ]
adox r13, r15
adox rbp, r8
adcx r11, [ rsp + 0x180 ]
mov rdx, 0xffffffffffffffff 
mulx r8, r15, r12
seto r12b
inc r10
adox rbx, [ rsp + 0x78 ]
adox r11, [ rsp + 0xa8 ]
mov r10, 0x100000001 
mov rdx, rbx
mov [ rsp + 0x1e8 ], rdi
mulx rdi, rbx, r10
mov rdi, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x1f0 ], r11
mulx r11, r10, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x1f8 ], r11
mov [ rsp + 0x200 ], r10
mulx r10, r11, rdi
mov rdi, r15
mov [ rsp + 0x208 ], r10
seto r10b
mov [ rsp + 0x210 ], r11
movzx r11, byte [ rsp + 0x1d8 ]
mov byte [ rsp + 0x218 ], cl
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox r11, rcx
adox rdi, [ rsp + 0x130 ]
adcx rdi, r13
mov r11, r15
adox r11, r8
setc r13b
clc
movzx r12, r12b
adcx r12, rcx
adcx r14, [ rsp - 0x20 ]
adox r15, r8
mov r12, 0x0 
adox r8, r12
mov r12, [ rsp - 0x30 ]
adc r12, 0x0
add r13b, 0xFF
adcx rbp, r11
mov r13, [ rsp + 0x8 ]
movzx r9, r9b
adox r9, rcx
adox r13, [ rsp + 0x50 ]
mov r9, [ rsp - 0x28 ]
seto r11b
movzx rcx, byte [ rsp + 0x218 ]
mov [ rsp + 0x220 ], r13
mov r13, 0x0 
dec r13
adox rcx, r13
adox r9, [ rsp + 0x40 ]
adcx r15, r14
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, [ rax + 0x28 ]
setc dl
clc
mov [ rsp + 0x228 ], r9
mov r9, -0x1 
movzx r11, r11b
adcx r11, r9
adcx r14, [ rsp + 0x48 ]
mov r11, [ rsp + 0x38 ]
mov r9, 0x0 
adox r11, r9
adc r13, 0x0
add dl, 0x7F
adox r12, r8
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx r9, r8, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x230 ], r11
mov [ rsp + 0x238 ], r13
mulx r13, r11, rcx
mov rcx, -0x1 
movzx r10, r10b
adcx r10, rcx
adcx rdi, [ rsp + 0x128 ]
setc r10b
clc
adcx r8, r13
adcx r9, [ rsp + 0x210 ]
seto r13b
inc rcx
mov rcx, -0x1 
movzx r10, r10b
adox r10, rcx
adox rbp, [ rsp + 0x170 ]
adox r15, [ rsp + 0x160 ]
mov r10, [ rsp + 0x200 ]
mov rcx, r10
adcx rcx, [ rsp + 0x208 ]
mov rdx, r10
adcx rdx, [ rsp + 0x1f8 ]
adcx r10, [ rsp + 0x1f8 ]
mov [ rsp + 0x240 ], r14
seto r14b
mov byte [ rsp + 0x248 ], r13b
mov r13, -0x2 
inc r13
adox r11, rbx
mov r11, [ rsp + 0x1f8 ]
mov rbx, 0x0 
adcx r11, rbx
adox r8, [ rsp + 0x1f0 ]
adox r9, rdi
adox rcx, rbp
adox rdx, r15
clc
movzx r14, r14b
adcx r14, r13
adcx r12, [ rsp + 0x1d0 ]
adox r10, r12
seto dil
mov rbp, -0x3 
inc rbp
adox r8, [ rsp + 0xf0 ]
movzx r14, byte [ rsp + 0x1c8 ]
mov r15, [ rsp - 0x40 ]
lea r14, [ r14 + r15 ]
adox r9, [ rsp + 0x138 ]
mov r15, 0x100000001 
xchg rdx, r15
mulx rbx, r12, r8
movzx rbx, byte [ rsp + 0x248 ]
adcx rbx, r14
mov r14, 0xffffffffffffffff 
mov rdx, r12
mulx rbp, r12, r14
mov r13, 0xffffffff 
mov [ rsp + 0x250 ], r9
mulx r9, r14, r13
seto r13b
mov [ rsp + 0x258 ], rbp
mov rbp, -0x2 
inc rbp
adox r14, r8
seto r14b
inc rbp
mov r8, -0x1 
movzx rdi, dil
adox rdi, r8
adox rbx, r11
mov r11, 0xffffffff00000000 
mulx rbp, rdi, r11
seto r8b
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rcx, [ rsp + 0x148 ]
setc r13b
clc
adcx rdi, r9
adox r15, [ rsp + 0x140 ]
adox r10, [ rsp + 0x158 ]
adox rbx, [ rsp + 0x178 ]
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x260 ], rbx
mulx rbx, r11, r9
adcx r11, rbp
mov rdx, r12
adcx rdx, rbx
mov rbp, r12
adcx rbp, [ rsp + 0x258 ]
setc bl
clc
mov r9, -0x1 
movzx r14, r14b
adcx r14, r9
adcx rdi, [ rsp + 0x250 ]
movzx r14, r8b
movzx r13, r13b
lea r14, [ r14 + r13 ]
adox r14, [ rsp + 0x1c0 ]
seto r13b
inc r9
adox rdi, [ rsp - 0x38 ]
adcx r11, rcx
adcx rdx, r15
adcx rbp, r10
mov r8, 0x100000001 
xchg rdx, r8
mulx r15, rcx, rdi
adox r11, [ rsp + 0x1b0 ]
setc r15b
clc
mov r10, -0x1 
movzx rbx, bl
adcx rbx, r10
adcx r12, [ rsp + 0x258 ]
mov rbx, [ rsp + 0x258 ]
adcx rbx, r9
mov r9, 0xfffffffffffffffe 
mov rdx, r9
mulx r10, r9, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x268 ], r10
mov [ rsp + 0x270 ], r11
mulx r11, r10, rcx
clc
adcx r10, rdi
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx rdi, r10, rcx
adox r8, [ rsp + 0x1a8 ]
setc dl
clc
mov [ rsp + 0x278 ], r8
mov r8, -0x1 
movzx r15, r15b
adcx r15, r8
adcx r12, [ rsp + 0x260 ]
adox rbp, [ rsp + 0x1e8 ]
adcx rbx, r14
setc r14b
clc
adcx r10, r11
adox r12, [ rsp + 0x220 ]
adcx r9, rdi
adox rbx, [ rsp + 0x240 ]
movzx r15, r14b
movzx r13, r13b
lea r15, [ r15 + r13 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, r8
adcx r10, [ rsp + 0x270 ]
adox r15, [ rsp + 0x238 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rdi, r11, rcx
seto cl
inc r8
adox r10, [ rsp + 0x88 ]
mov r14, r11
seto r8b
mov rdx, 0x0 
dec rdx
movzx r13, r13b
adox r13, rdx
adox r14, [ rsp + 0x268 ]
mov r13, r11
adox r13, rdi
adox r11, rdi
mov rdx, 0x100000001 
mov byte [ rsp + 0x280 ], cl
mov [ rsp + 0x288 ], r15
mulx r15, rcx, r10
mov r15, 0xffffffff 
mov rdx, r15
mov [ rsp + 0x290 ], r11
mulx r11, r15, rcx
seto dl
mov [ rsp + 0x298 ], rbx
mov rbx, -0x2 
inc rbx
adox r15, r10
mov r15, 0xffffffff00000000 
xchg rdx, rcx
mulx rbx, r10, r15
seto r15b
mov byte [ rsp + 0x2a0 ], cl
mov rcx, -0x2 
inc rcx
adox r10, r11
adcx r9, [ rsp + 0x278 ]
adcx r14, rbp
mov rbp, 0xfffffffffffffffe 
mulx rcx, r11, rbp
adox r11, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x2a8 ], r13
mulx r13, rbp, rbx
seto dl
mov rbx, 0x0 
dec rbx
movzx r8, r8b
adox r8, rbx
adox r9, [ rsp + 0x150 ]
adox r14, [ rsp + 0x198 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, rbx
adcx rcx, rbp
setc dl
clc
movzx r15, r15b
adcx r15, rbx
adcx r9, r10
adcx r11, r14
seto r15b
inc rbx
adox r9, [ rsp - 0x48 ]
setc r10b
clc
mov r14, -0x1 
movzx r8, r8b
adcx r8, r14
adcx r12, [ rsp + 0x2a8 ]
mov r8, [ rsp + 0x290 ]
adcx r8, [ rsp + 0x298 ]
movzx rbx, byte [ rsp + 0x2a0 ]
lea rdi, [ rdi + rbx ]
adcx rdi, [ rsp + 0x288 ]
movzx rbx, byte [ rsp + 0x280 ]
mov r14, 0x0 
adcx rbx, r14
mov r14, 0x100000001 
xchg rdx, r14
mov [ rsp + 0x2b0 ], rbx
mov [ rsp + 0x2b8 ], rdi
mulx rdi, rbx, r9
mov rdi, 0xffffffff 
mov rdx, rbx
mov [ rsp + 0x2c0 ], rcx
mulx rcx, rbx, rdi
adox r11, [ rsp + 0x108 ]
mov rdi, 0xffffffffffffffff 
mov byte [ rsp + 0x2c8 ], r10b
mov [ rsp + 0x2d0 ], r8
mulx r8, r10, rdi
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x2d8 ], r12
mov byte [ rsp + 0x2e0 ], r15b
mulx r15, r12, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x2e8 ], r11
mov [ rsp + 0x2f0 ], rbx
mulx rbx, r11, rdi
clc
adcx r12, rcx
adcx r11, r15
mov rdx, r10
adcx rdx, rbx
mov rcx, r10
adcx rcx, r8
mov r15, r13
seto bl
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r14, r14b
adox r14, rdi
adox r15, rbp
adox rbp, r13
setc r14b
clc
adcx r9, [ rsp + 0x2f0 ]
adcx r12, [ rsp + 0x2e8 ]
mov r9, 0x0 
adox r13, r9
mov r9, [ rsp + 0x2d8 ]
movzx rdi, byte [ rsp + 0x2e0 ]
mov [ rsp + 0x2f8 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox rdi, rcx
adox r9, [ rsp + 0x190 ]
setc dil
seto cl
mov [ rsp + 0x300 ], r13
mov r13, r12
mov [ rsp + 0x308 ], rdx
mov rdx, 0xffffffff 
sub r13, rdx
mov rdx, [ rsp + 0x2d0 ]
mov [ rsp + 0x310 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rcx, cl
adox rcx, r13
adox rdx, [ rsp + 0x1e0 ]
setc cl
movzx r13, byte [ rsp + 0x2c8 ]
clc
mov byte [ rsp + 0x318 ], r14b
mov r14, -0x1 
adcx r13, r14
adcx r9, [ rsp + 0x2c0 ]
mov r13, [ rsp + 0x228 ]
adox r13, [ rsp + 0x2b8 ]
mov r14, [ rsp + 0x2b0 ]
adox r14, [ rsp + 0x230 ]
adcx r15, rdx
setc dl
clc
mov byte [ rsp + 0x320 ], cl
mov rcx, -0x1 
movzx rbx, bl
adcx rbx, rcx
adcx r9, [ rsp + 0x100 ]
adcx r15, [ rsp + 0x120 ]
seto bl
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox r9, r11
seto r11b
inc rcx
mov rdi, -0x1 
movzx rdx, dl
adox rdx, rdi
adox r13, rbp
mov rbp, r8
seto dl
movzx rcx, byte [ rsp + 0x318 ]
inc rdi
mov rdi, -0x1 
adox rcx, rdi
adox rbp, r10
adcx r13, [ rsp + 0x1a0 ]
mov r10, 0x0 
adox r8, r10
dec r10
movzx r11, r11b
adox r11, r10
adox r15, [ rsp + 0x308 ]
seto dil
inc r10
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox r14, [ rsp + 0x300 ]
adcx r14, [ rsp + 0x188 ]
movzx r11, bl
adox r11, r10
adcx r11, [ rsp + 0x1b8 ]
dec r10
movzx rdi, dil
adox rdi, r10
adox r13, [ rsp + 0x2f8 ]
setc cl
seto bl
movzx rdx, byte [ rsp + 0x320 ]
add rdx, -0x1
mov rdx, r9
mov rdi, 0xffffffff00000000 
sbb rdx, rdi
mov r10, r15
mov rdi, 0xfffffffffffffffe 
sbb r10, rdi
mov rdi, 0x0 
dec rdi
movzx rbx, bl
adox rbx, rdi
adox r14, rbp
adox r8, r11
movzx rbp, cl
mov r11, 0x0 
adox rbp, r11
mov rcx, r13
mov rbx, 0xffffffffffffffff 
sbb rcx, rbx
mov r11, r14
sbb r11, rbx
mov rdi, r8
sbb rdi, rbx
sbb rbp, 0x00000000
cmovc r11, r14
cmovc r10, r15
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x20 ], r11
cmovc rdx, r9
mov [ rbp + 0x8 ], rdx
mov [ rbp + 0x10 ], r10
mov r9, [ rsp + 0x310 ]
cmovc r9, r12
cmovc rcx, r13
mov [ rbp + 0x18 ], rcx
cmovc rdi, r8
mov [ rbp + 0x28 ], rdi
mov [ rbp + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 936
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0510
; seed 1789707175983676 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 64385 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 1650 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.025627087054438145
; number reverted permutation / tried permutation: 313 / 500 =62.600%
; number reverted decision / tried decision: 252 / 499 =50.501%
; validated in 48.555s
