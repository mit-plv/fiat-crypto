SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 920
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], r11
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r13
mulx r13, r14, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r8
mulx r8, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r13
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r8
mulx r8, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], rcx
mulx rcx, r8, [ rax + 0x28 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r8
mulx r8, rcx, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r8
mulx r8, rcx, [ rax + 0x0 ]
xor rdx, rdx
adox r10, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x40 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x48 ], rcx
mov [ rsp + 0x50 ], r12
mulx r12, rcx, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], r8
mulx r8, r10, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r10
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r8
mulx r8, r10, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], r10
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], r8
mulx r8, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xa8 ], r8
mov [ rsp + 0xb0 ], r10
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r12
mov [ rsp + 0xc0 ], rcx
mulx rcx, r12, [ rax + 0x0 ]
adox r8, r11
adcx r15, rcx
adcx r9, rdi
adox r13, r10
mov rdx, 0xffffffffffffffff 
mulx r11, rdi, r14
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx rcx, r10, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xc8 ], r9
mulx r9, r14, [ rsi + 0x28 ]
adcx rbx, [ rsp + 0xc0 ]
adcx r14, [ rsp + 0xb8 ]
adcx r9, [ rsp + 0x90 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], r14
mulx r14, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], r15
mulx r15, rbx, [ rax + 0x0 ]
seto dl
mov [ rsp + 0xf0 ], r12
mov r12, -0x2 
inc r12
adox r14, [ rsp + 0x8 ]
mov r12b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
adox rbx, [ rsp - 0x28 ]
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x108 ], rbx
mov rbx, 0x0 
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], r11
mov byte [ rsp + 0x118 ], r12b
mulx r12, r11, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], rbx
mov [ rsp + 0x128 ], r14
mulx r14, rbx, [ rax + 0x8 ]
clc
adcx rbx, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], r8
mulx r8, r9, [ rax + 0x10 ]
mov rdx, [ rsp + 0x60 ]
mov [ rsp + 0x148 ], rdi
seto dil
mov [ rsp + 0x150 ], rcx
mov rcx, -0x2 
inc rcx
adox rdx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adox r8, [ rsp - 0x8 ]
adcx r15, r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r15
mulx r15, rcx, [ rax + 0x18 ]
adcx rbx, [ rsp + 0x38 ]
seto dl
mov [ rsp + 0x160 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx rdi, dil
adox rdi, rbx
adox r13, rcx
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mulx rbx, rcx, [ rax + 0x28 ]
adcx r11, [ rsp + 0x30 ]
adcx rcx, r12
mov rdx, [ rsp - 0x10 ]
seto r12b
mov [ rsp + 0x168 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox rdx, [ rsp + 0xa0 ]
mov rdi, 0x0 
adcx rbx, rdi
mov rdi, [ rsp - 0x18 ]
adox rdi, [ rsp + 0x98 ]
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], rbx
mov [ rsp + 0x178 ], r11
mulx r11, rbx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x180 ], rdi
mov [ rsp + 0x188 ], rcx
mulx rcx, rdi, [ rax + 0x10 ]
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx r15, rbx
mov r12, [ rsp + 0xb0 ]
setc bl
clc
adcx r12, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x190 ], r12
mov [ rsp + 0x198 ], r8
mulx r8, r12, [ rax + 0x18 ]
adcx rdi, [ rsp + 0xa8 ]
adcx r12, rcx
seto dl
mov rcx, -0x2 
inc rcx
adox rbp, [ rsp + 0x28 ]
adcx r8, [ rsp + 0x80 ]
mov bpl, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1a0 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
setc dl
clc
adcx r10, [ rsp + 0x20 ]
mov byte [ rsp + 0x1a8 ], dl
mov rdx, [ rsp + 0x150 ]
adcx rdx, [ rsp + 0x70 ]
mov [ rsp + 0x1b0 ], r12
mov r12, [ rsp + 0x68 ]
adcx r12, [ rsp + 0x148 ]
mov [ rsp + 0x1b8 ], rdi
movzx rdi, bpl
mov [ rsp + 0x1c0 ], r9
mov r9, [ rsp - 0x20 ]
lea rdi, [ rdi + r9 ]
adox r10, [ rsp + 0x58 ]
setc r9b
clc
mov rbp, -0x1 
movzx rbx, bl
adcx rbx, rbp
adcx r11, [ rsp + 0x18 ]
adox rdx, [ rsp + 0x140 ]
setc bl
clc
adcx r10, [ rsp + 0x138 ]
adcx rdx, [ rsp + 0x128 ]
mov rbp, 0x100000001 
xchg rdx, r10
mov [ rsp + 0x1c8 ], rdi
mov [ rsp + 0x1d0 ], r14
mulx r14, rdi, rbp
mov r14, 0xfffffffffffffffe 
xchg rdx, rdi
mov byte [ rsp + 0x1d8 ], bl
mulx rbx, rbp, r14
mov r14, [ rsp + 0x50 ]
mov [ rsp + 0x1e0 ], rbx
seto bl
mov [ rsp + 0x1e8 ], r11
movzx r11, byte [ rsp + 0x118 ]
mov [ rsp + 0x1f0 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r11, r15
adox r14, [ rsp + 0x0 ]
mov r11, [ rsp + 0x148 ]
mov r15, r11
mov [ rsp + 0x1f8 ], r10
setc r10b
clc
mov [ rsp + 0x200 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx r15, [ rsp + 0x110 ]
setc r9b
clc
movzx rbx, bl
adcx rbx, r13
adcx r12, [ rsp + 0x100 ]
seto bl
inc r13
mov r13, -0x1 
movzx r10, r10b
adox r10, r13
adox r12, [ rsp + 0x108 ]
seto r10b
inc r13
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox rcx, [ rsp + 0x48 ]
mov rbx, 0x0 
adox r8, rbx
dec rbx
movzx r9, r9b
adox r9, rbx
adox r11, [ rsp + 0x110 ]
mov r13, 0xffffffff00000000 
mulx rbx, r9, r13
adcx r15, r14
mov r14, 0xffffffff 
mov [ rsp + 0x208 ], r12
mulx r12, r13, r14
mov r14, [ rsp + 0x110 ]
mov [ rsp + 0x210 ], r15
mov r15, 0x0 
adox r14, r15
adcx r11, rcx
mov rcx, -0x3 
inc rcx
adox r13, rdi
mov r13, 0xffffffffffffffff 
mulx r15, rdi, r13
setc dl
clc
adcx r9, r12
adcx rbp, rbx
mov rbx, [ rsp + 0x200 ]
seto r12b
mov rcx, 0x0 
dec rcx
movzx r10, r10b
adox r10, rcx
adox rbx, [ rsp + 0x210 ]
seto r10b
inc rcx
mov rcx, -0x1 
movzx r12, r12b
adox r12, rcx
adox r9, [ rsp + 0x1f8 ]
setc r12b
clc
adcx r9, [ rsp + 0x40 ]
mov rcx, 0x100000001 
xchg rdx, r9
mov [ rsp + 0x218 ], rbx
mulx rbx, r13, rcx
seto bl
mov rcx, 0x0 
dec rcx
movzx r9, r9b
adox r9, rcx
adox r8, r14
setc r14b
clc
movzx r10, r10b
adcx r10, rcx
adcx r11, [ rsp + 0x1f0 ]
adcx r8, [ rsp + 0x1e8 ]
mov r9, rdi
seto r10b
inc rcx
mov rcx, -0x1 
movzx r12, r12b
adox r12, rcx
adox r9, [ rsp + 0x1e0 ]
movzx r12, byte [ rsp + 0x1d8 ]
mov rcx, [ rsp + 0x10 ]
lea r12, [ r12 + rcx ]
movzx rcx, r10b
adcx rcx, r12
mov r10, rdi
adox r10, r15
adox rdi, r15
seto r12b
mov [ rsp + 0x220 ], r13
mov r13, 0x0 
dec r13
movzx rbx, bl
adox rbx, r13
adox rbp, [ rsp + 0x208 ]
movzx rbx, r12b
lea rbx, [ rbx + r15 ]
adox r9, [ rsp + 0x218 ]
adox r10, r11
adox rdi, r8
adox rbx, rcx
seto r15b
inc r13
mov r11, -0x1 
movzx r14, r14b
adox r14, r11
adox rbp, [ rsp + 0x1d0 ]
movzx r14, r15b
adcx r14, r13
mov r8, 0xfffffffffffffffe 
mov rcx, rdx
mov rdx, [ rsp + 0x220 ]
mulx r15, r12, r8
mov r13, 0xffffffffffffffff 
mulx r8, r11, r13
adox r9, [ rsp + 0x1c0 ]
mov r13, 0xffffffff00000000 
mov [ rsp + 0x228 ], r14
mov [ rsp + 0x230 ], r9
mulx r9, r14, r13
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x238 ], r8
mov [ rsp + 0x240 ], r11
mulx r11, r8, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x248 ], r11
mov [ rsp + 0x250 ], r8
mulx r8, r11, r13
adox r10, [ rsp + 0x198 ]
clc
adcx r11, rcx
adox rdi, [ rsp + 0x188 ]
seto r11b
mov rcx, -0x2 
inc rcx
adox r14, r8
adcx r14, rbp
seto r13b
inc rcx
adox r14, [ rsp - 0x48 ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx r8, rbp, r14
mov r8, 0xffffffffffffffff 
mov rdx, rbp
mulx rcx, rbp, r8
mov r8, 0xffffffff 
mov [ rsp + 0x258 ], rcx
mov [ rsp + 0x260 ], rbp
mulx rbp, rcx, r8
setc r8b
clc
mov [ rsp + 0x268 ], rcx
mov rcx, -0x1 
movzx r11, r11b
adcx r11, rcx
adcx rbx, [ rsp + 0x180 ]
seto r11b
inc rcx
mov rcx, -0x1 
movzx r13, r13b
adox r13, rcx
adox r9, r12
adox r15, [ rsp + 0x240 ]
mov r12, [ rsp + 0x240 ]
mov r13, r12
adox r13, [ rsp + 0x238 ]
setc cl
clc
mov [ rsp + 0x270 ], rbx
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx r9, [ rsp + 0x230 ]
adcx r15, r10
adcx r13, rdi
mov r10, [ rsp + 0x228 ]
seto dil
inc rbx
mov r8, -0x1 
movzx rcx, cl
adox rcx, r8
adox r10, [ rsp + 0x1c8 ]
mov rcx, 0xffffffff00000000 
mulx r8, rbx, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0x278 ], r10
mov byte [ rsp + 0x280 ], dil
mulx rdi, r10, rcx
seto dl
mov rcx, 0x0 
dec rcx
movzx r11, r11b
adox r11, rcx
adox r9, [ rsp + 0x190 ]
adox r15, [ rsp + 0x1b8 ]
setc r11b
clc
adcx rbx, rbp
adcx r10, r8
adcx rdi, [ rsp + 0x260 ]
mov rbp, [ rsp + 0x260 ]
mov r8, rbp
adcx r8, [ rsp + 0x258 ]
adox r13, [ rsp + 0x1b0 ]
seto cl
mov [ rsp + 0x288 ], r8
mov r8, -0x2 
inc r8
adox r14, [ rsp + 0x268 ]
setc r14b
movzx r8, byte [ rsp + 0x280 ]
clc
mov byte [ rsp + 0x290 ], cl
mov rcx, -0x1 
adcx r8, rcx
adcx r12, [ rsp + 0x238 ]
mov r8, [ rsp + 0x238 ]
mov rcx, 0x0 
adcx r8, rcx
clc
mov rcx, -0x1 
movzx r14, r14b
adcx r14, rcx
adcx rbp, [ rsp + 0x258 ]
adox rbx, r9
seto r9b
inc rcx
adox rbx, [ rsp + 0xf8 ]
mov r14, [ rsp + 0x78 ]
seto cl
mov [ rsp + 0x298 ], rbp
movzx rbp, byte [ rsp + 0x1a8 ]
mov byte [ rsp + 0x2a0 ], dl
mov rdx, 0x0 
dec rdx
adox rbp, rdx
adox r14, [ rsp + 0x250 ]
mov rbp, 0x100000001 
mov rdx, rbp
mov [ rsp + 0x2a8 ], r14
mulx r14, rbp, rbx
mov r14, [ rsp + 0x248 ]
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rsp + 0x258 ]
adc rdx, 0x0
add r11b, 0x7F
adox r12, [ rsp + 0x270 ]
mov r11, 0xffffffff00000000 
xchg rdx, rbp
mov [ rsp + 0x2b0 ], rbp
mov [ rsp + 0x2b8 ], r14
mulx r14, rbp, r11
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx r15, r10
adox r8, [ rsp + 0x278 ]
setc r10b
clc
movzx rcx, cl
adcx rcx, r11
adcx r15, [ rsp + 0x130 ]
setc r9b
clc
movzx r10, r10b
adcx r10, r11
adcx r13, rdi
movzx rdi, byte [ rsp + 0x2a0 ]
mov rcx, 0x0 
adox rdi, rcx
mov r10, 0xffffffffffffffff 
mulx r11, rcx, r10
mov r10, 0xffffffff 
mov [ rsp + 0x2c0 ], r11
mov [ rsp + 0x2c8 ], rcx
mulx rcx, r11, r10
movzx r10, byte [ rsp + 0x290 ]
mov [ rsp + 0x2d0 ], r15
mov r15, 0x0 
dec r15
adox r10, r15
adox r12, [ rsp + 0x1a0 ]
setc r10b
clc
movzx r9, r9b
adcx r9, r15
adcx r13, [ rsp + 0x158 ]
adox r8, [ rsp + 0x2a8 ]
setc r9b
clc
movzx r10, r10b
adcx r10, r15
adcx r12, [ rsp + 0x288 ]
adox rdi, [ rsp + 0x2b8 ]
mov r10, 0xfffffffffffffffe 
mov [ rsp + 0x2d8 ], r13
mulx r13, r15, r10
adcx r8, [ rsp + 0x298 ]
seto dl
mov r10, -0x2 
inc r10
adox rbp, rcx
adox r15, r14
seto r14b
inc r10
adox r11, rbx
adox rbp, [ rsp + 0x2d0 ]
adcx rdi, [ rsp + 0x2b0 ]
setc r11b
clc
adcx rbp, [ rsp + 0xf0 ]
setc bl
clc
mov rcx, -0x1 
movzx r14, r14b
adcx r14, rcx
adcx r13, [ rsp + 0x2c8 ]
seto r14b
dec r10
movzx r9, r9b
adox r9, r10
adox r12, [ rsp + 0x160 ]
setc cl
clc
movzx r14, r14b
adcx r14, r10
adcx r15, [ rsp + 0x2d8 ]
adox r8, [ rsp + 0x178 ]
adox rdi, [ rsp + 0x168 ]
adcx r13, r12
movzx r9, r11b
movzx rdx, dl
lea r9, [ r9 + rdx ]
adox r9, [ rsp + 0x170 ]
mov rdx, 0x100000001 
mulx r11, r14, rbp
mov r11, 0xffffffff 
mov rdx, r11
mulx r12, r11, r14
mov r10, 0xfffffffffffffffe 
mov rdx, r14
mov [ rsp + 0x2e0 ], r11
mulx r11, r14, r10
mov r10, [ rsp + 0x2c8 ]
mov [ rsp + 0x2e8 ], r11
mov r11, r10
mov [ rsp + 0x2f0 ], r14
seto r14b
mov [ rsp + 0x2f8 ], r12
mov r12, 0x0 
dec r12
movzx rcx, cl
adox rcx, r12
adox r11, [ rsp + 0x2c0 ]
adcx r11, r8
adox r10, [ rsp + 0x2c0 ]
mov rcx, [ rsp + 0x2c0 ]
mov r8, 0x0 
adox rcx, r8
adcx r10, rdi
mov rdi, 0xffffffffffffffff 
mulx r12, r8, rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r15, [ rsp + 0xe8 ]
adcx rcx, r9
adox r13, [ rsp + 0xc8 ]
mov rbx, 0xffffffff00000000 
mulx rdi, r9, rbx
adox r11, [ rsp + 0xe0 ]
adox r10, [ rsp + 0xd8 ]
setc dl
clc
adcx r9, [ rsp + 0x2f8 ]
adcx rdi, [ rsp + 0x2f0 ]
mov rbx, r8
adcx rbx, [ rsp + 0x2e8 ]
mov [ rsp + 0x300 ], r10
mov r10, r8
adcx r10, r12
adox rcx, [ rsp + 0xd0 ]
mov [ rsp + 0x308 ], rcx
movzx rcx, dl
movzx r14, r14b
lea rcx, [ rcx + r14 ]
seto r14b
mov rdx, -0x2 
inc rdx
adox rbp, [ rsp + 0x2e0 ]
adox r9, r15
adcx r8, r12
adox rdi, r13
adox rbx, r11
adox r10, [ rsp + 0x300 ]
mov rbp, 0x0 
adcx r12, rbp
adox r8, [ rsp + 0x308 ]
clc
movzx r14, r14b
adcx r14, rdx
adcx rcx, [ rsp + 0x120 ]
setc r15b
seto r13b
mov r11, r9
mov r14, 0xffffffff 
sub r11, r14
inc rdx
mov rbp, -0x1 
movzx r13, r13b
adox r13, rbp
adox rcx, r12
seto r12b
mov r13, rdi
mov rdx, 0xffffffff00000000 
sbb r13, rdx
mov rbp, rbx
mov r14, 0xfffffffffffffffe 
sbb rbp, r14
mov rdx, r10
mov r14, 0xffffffffffffffff 
sbb rdx, r14
mov [ rsp + 0x310 ], r13
mov r13, r8
sbb r13, r14
movzx r14, r12b
movzx r15, r15b
lea r14, [ r14 + r15 ]
mov r15, rcx
mov r12, 0xffffffffffffffff 
sbb r15, r12
sbb r14, 0x00000000
cmovc r11, r9
cmovc rbp, rbx
cmovc r15, rcx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x28 ], r15
cmovc rdx, r10
mov [ r14 + 0x18 ], rdx
cmovc r13, r8
mov [ r14 + 0x20 ], r13
mov [ r14 + 0x0 ], r11
mov [ r14 + 0x10 ], rbp
mov r9, [ rsp + 0x310 ]
cmovc r9, rdi
mov [ r14 + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 920
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2064
; seed 4314836478256216 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 28350 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=70, initial num_batches=31): 785 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.027689594356261022
; number reverted permutation / tried permutation: 298 / 510 =58.431%
; number reverted decision / tried decision: 293 / 489 =59.918%
; validated in 24.84s
