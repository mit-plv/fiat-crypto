SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 936
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r9
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rdi
mulx rdi, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], rcx
mulx rcx, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r15
mulx r15, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r11
mulx r11, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], r15
mulx r15, r11, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], rcx
mulx rcx, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r15
mulx r15, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], rcx
mulx rcx, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r9
mulx r9, rdi, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0x50 ], r8
mov [ rsp + 0x58 ], r9
mulx r9, r8, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], rdi
mulx rdi, r9, [ rax + 0x18 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r9
mulx r9, rdi, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], r9
mov [ rsp + 0x80 ], rdi
mulx rdi, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], rcx
mulx rcx, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], rcx
mulx rcx, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], rcx
mulx rcx, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xe8 ], r15
mov [ rsp + 0xf0 ], r11
mulx r11, r15, r8
adox rcx, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], rcx
mulx rcx, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x100 ], rbx
mov [ rsp + 0x108 ], r11
mulx r11, rbx, [ rsi + 0x0 ]
adcx rbp, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x110 ], rbp
mulx rbp, rcx, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x118 ], r11
mov r11, -0x2 
inc r11
adox rbx, r14
adcx r10, r12
mov r12b, dl
mov rdx, [ rsi + 0x28 ]
mulx r11, r14, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], rbx
mulx rbx, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r15
mulx r15, r10, [ rax + 0x0 ]
seto dl
mov [ rsp + 0x140 ], r10
mov r10, -0x2 
inc r10
adox r9, rbx
adox rdi, [ rsp + 0xf0 ]
setc bl
clc
adcx r15, [ rsp + 0xc0 ]
mov r10b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r15
mov [ rsp + 0x150 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rsp + 0xb0 ]
adcx rdx, [ rsp + 0xb8 ]
adcx r14, [ rsp + 0xa8 ]
adcx r11, [ rsp + 0x90 ]
mov [ rsp + 0x158 ], r11
mov r11, [ rsp + 0x88 ]
adcx r11, [ rsp + 0x60 ]
mov [ rsp + 0x160 ], r11
mov r11, [ rsp + 0xa0 ]
mov [ rsp + 0x168 ], r14
seto r14b
mov [ rsp + 0x170 ], rdx
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox r11, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0x98 ]
mov r12, [ rsp + 0x58 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx r15, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0x50 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x178 ], r12
mov [ rsp + 0x180 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
adox r12, rbp
mov rdx, 0xffffffff 
mov [ rsp + 0x188 ], r15
mulx r15, rbp, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x190 ], r12
mov [ rsp + 0x198 ], r9
mulx r9, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], rcx
mov [ rsp + 0x1a8 ], r11
mulx r11, rcx, [ rax + 0x28 ]
mov rdx, [ rsp + 0x70 ]
adcx rdx, [ rsp + 0x48 ]
mov byte [ rsp + 0x1b0 ], r10b
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1b8 ], r11
mov [ rsp + 0x1c0 ], rbp
mulx rbp, r11, [ rsi + 0x18 ]
adcx r12, [ rsp + 0x68 ]
adcx r9, [ rsp + 0x40 ]
mov rdx, [ rsp + 0x18 ]
mov [ rsp + 0x1c8 ], r9
mov r9, 0x0 
adcx rdx, r9
mov r9, [ rsp + 0x38 ]
clc
mov [ rsp + 0x1d0 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r9, [ rsp + 0x10 ]
mov r14, [ rsp - 0x18 ]
adcx r14, [ rsp + 0x30 ]
mov rdx, 0x0 
adox rdi, rdx
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r11, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x8 ]
setc bl
clc
adcx r15, [ rsp + 0x138 ]
seto dl
mov [ rsp + 0x1d8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rcx, [ rsp - 0x38 ]
setc bl
clc
adcx r13, [ rsp + 0x1c0 ]
mov r13, [ rsp + 0x1b8 ]
mov r12, 0x0 
adox r13, r12
adcx r15, [ rsp + 0x128 ]
mov r12, [ rsp - 0x10 ]
mov [ rsp + 0x1e0 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rdx, dl
adox rdx, r10
adox r12, [ rsp + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1e8 ], r12
mulx r12, r10, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0x1f0 ], rbp
mov rbp, 0x0 
adox rdx, rbp
mov rbp, [ rsp + 0x118 ]
mov [ rsp + 0x1f8 ], rdx
movzx rdx, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x200 ], r11
mov r11, 0x0 
dec r11
adox rdx, r11
adox rbp, [ rsp + 0xe0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x208 ], r13
mulx r13, r11, r8
setc r8b
clc
adcx r15, [ rsp - 0x40 ]
mov rdx, 0x100000001 
mov [ rsp + 0x210 ], rcx
mov [ rsp + 0x218 ], r14
mulx r14, rcx, r15
adox r10, [ rsp + 0xd8 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x220 ], rdi
mulx rdi, r14, rcx
adox r12, [ rsp + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x228 ], r9
mov [ rsp + 0x230 ], rdi
mulx rdi, r9, rcx
mov rdx, [ rsp + 0x108 ]
mov [ rsp + 0x238 ], r14
setc r14b
clc
mov [ rsp + 0x240 ], rdi
mov rdi, -0x1 
movzx rbx, bl
adcx rbx, rdi
adcx rdx, [ rsp + 0x80 ]
mov rbx, r11
adcx rbx, [ rsp + 0x78 ]
seto dil
mov [ rsp + 0x248 ], r9
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox rbp, rdx
adox rbx, r10
seto r8b
inc r9
mov r10, -0x1 
movzx r14, r14b
adox r14, r10
adox rbp, [ rsp - 0x48 ]
mov r14, r11
adcx r14, r13
adcx r11, r13
mov rdx, 0xffffffff 
mulx r10, r9, rcx
mov rdx, 0x0 
adcx r13, rdx
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx r12, r14
mov r8, 0xfffffffffffffffe 
mov rdx, rcx
mulx r14, rcx, r8
adox rbx, [ rsp + 0xf8 ]
mov rdx, [ rsp + 0x0 ]
setc r8b
clc
mov [ rsp + 0x250 ], r13
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx rdx, [ rsp - 0x28 ]
adox r12, [ rsp + 0x1a8 ]
seto dil
inc r13
mov r13, -0x1 
movzx r8, r8b
adox r8, r13
adox rdx, r11
setc r11b
clc
movzx rdi, dil
adcx rdi, r13
adcx rdx, [ rsp + 0x1a0 ]
setc r8b
clc
adcx r10, [ rsp + 0x248 ]
adcx rcx, [ rsp + 0x240 ]
seto dil
inc r13
adox r9, r15
adcx r14, [ rsp + 0x238 ]
adox r10, rbp
adox rcx, rbx
seto r9b
mov r15, -0x3 
inc r15
adox r10, [ rsp + 0x130 ]
movzx rbp, r11b
mov rbx, [ rsp - 0x30 ]
lea rbp, [ rbp + rbx ]
mov rbx, 0x100000001 
xchg rdx, rbx
mulx r13, r11, r10
mov r13, 0xffffffff00000000 
mov rdx, r11
mulx r15, r11, r13
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0x258 ], r15
mov [ rsp + 0x260 ], r11
mulx r11, r15, r13
mov r13, [ rsp + 0x238 ]
mov [ rsp + 0x268 ], r11
mov r11, r13
adcx r11, [ rsp + 0x230 ]
adox rcx, [ rsp + 0x198 ]
adcx r13, [ rsp + 0x230 ]
mov [ rsp + 0x270 ], r15
setc r15b
clc
mov [ rsp + 0x278 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx rbp, [ rsp + 0x250 ]
movzx rdi, r15b
mov rcx, [ rsp + 0x230 ]
lea rdi, [ rdi + rcx ]
seto cl
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r9, r9b
adox r9, r15
adox r12, r14
adox r11, rbx
setc bl
clc
movzx rcx, cl
adcx rcx, r15
adcx r12, [ rsp + 0x150 ]
mov r14, 0xffffffffffffffff 
mulx rcx, r9, r14
adcx r11, [ rsp + 0x228 ]
setc r15b
clc
mov r14, -0x1 
movzx r8, r8b
adcx r8, r14
adcx rbp, [ rsp + 0x190 ]
movzx rbx, bl
movzx r8, bl
adcx r8, [ rsp + 0x220 ]
adox r13, rbp
mov rbx, 0xffffffff 
mulx r14, rbp, rbx
adox rdi, r8
seto dl
adc dl, 0x0
movzx rdx, dl
add r15b, 0x7F
adox r13, [ rsp + 0x218 ]
adox rdi, [ rsp + 0x210 ]
movzx rdx, dl
movzx r15, dl
adox r15, [ rsp + 0x208 ]
adcx r14, [ rsp + 0x260 ]
seto r8b
mov rdx, -0x2 
inc rdx
adox rbp, r10
adox r14, [ rsp + 0x278 ]
mov rbp, [ rsp + 0x258 ]
adcx rbp, [ rsp + 0x270 ]
mov r10, r9
adcx r10, [ rsp + 0x268 ]
adox rbp, r12
mov r12, r9
adcx r12, rcx
adox r10, r11
seto r11b
inc rdx
adox r14, [ rsp + 0x100 ]
mov rdx, 0x100000001 
mov byte [ rsp + 0x280 ], r8b
mulx r8, rbx, r14
setc r8b
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r13, r12
adox rbp, [ rsp + 0x110 ]
mov r12, 0xffffffffffffffff 
mov rdx, rbx
mulx r11, rbx, r12
adox r10, [ rsp + 0x120 ]
mov r12, rcx
mov [ rsp + 0x288 ], r10
setc r10b
clc
mov [ rsp + 0x290 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx r12, r9
adox r13, [ rsp + 0x200 ]
mov r9, 0xffffffff 
mulx rbp, r8, r9
mov r9, 0xffffffff00000000 
mov [ rsp + 0x298 ], r13
mov [ rsp + 0x2a0 ], r15
mulx r15, r13, r9
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x2a8 ], r11
mov [ rsp + 0x2b0 ], rbx
mulx rbx, r11, r9
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r8, r14
seto r8b
dec rdx
movzx r10, r10b
adox r10, rdx
adox rdi, r12
setc r14b
clc
adcx r13, rbp
adcx r11, r15
adcx rbx, [ rsp + 0x2b0 ]
mov r10, [ rsp + 0x2a8 ]
mov r12, r10
adcx r12, [ rsp + 0x2b0 ]
adox rcx, [ rsp + 0x2a0 ]
mov rbp, r10
adcx rbp, [ rsp + 0x2b0 ]
mov r15, 0x0 
adcx r10, r15
movzx r15, byte [ rsp + 0x280 ]
mov rdx, 0x0 
adox r15, rdx
add r14b, 0xFF
adcx r13, [ rsp + 0x290 ]
adox r13, [ rsp + 0xc8 ]
mov r14, 0x100000001 
mov rdx, r14
mulx r9, r14, r13
adcx r11, [ rsp + 0x288 ]
mov r9, 0xffffffff 
mov rdx, r14
mov [ rsp + 0x2b8 ], r10
mulx r10, r14, r9
adcx rbx, [ rsp + 0x298 ]
mov r9, 0xffffffff00000000 
mov [ rsp + 0x2c0 ], rbx
mov [ rsp + 0x2c8 ], rbp
mulx rbp, rbx, r9
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x2d0 ], r12
mov [ rsp + 0x2d8 ], r11
mulx r11, r12, r9
setc r9b
clc
adcx rbx, r10
seto r10b
mov byte [ rsp + 0x2e0 ], r9b
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox rdi, [ rsp + 0x1f0 ]
mov r8, 0xfffffffffffffffe 
mov [ rsp + 0x2e8 ], rdi
mulx rdi, r9, r8
adox rcx, [ rsp + 0x1e8 ]
seto dl
mov r8, -0x2 
inc r8
adox r14, r13
adcx r9, rbp
mov r14, r12
adcx r14, rdi
seto r13b
inc r8
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r15, [ rsp + 0x1f8 ]
mov rdi, [ rsp + 0x2d8 ]
seto dl
dec r8
movzx r10, r10b
adox r10, r8
adox rdi, [ rsp + 0x188 ]
seto bpl
inc r8
mov r10, -0x1 
movzx r13, r13b
adox r13, r10
adox rdi, rbx
mov rbx, r12
adcx rbx, r11
adcx r12, r11
mov r13, [ rsp + 0x2e8 ]
seto r8b
movzx r10, byte [ rsp + 0x2e0 ]
mov [ rsp + 0x2f0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r10, r12
adox r13, [ rsp + 0x2d0 ]
adox rcx, [ rsp + 0x2c8 ]
adox r15, [ rsp + 0x2b8 ]
setc r10b
clc
adcx rdi, [ rsp + 0x140 ]
movzx r12, r10b
lea r12, [ r12 + r11 ]
mov r11, [ rsp + 0x2c0 ]
seto r10b
mov [ rsp + 0x2f8 ], r12
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox r11, [ rsp + 0x180 ]
setc bpl
clc
movzx r8, r8b
adcx r8, r12
adcx r11, r9
movzx r9, r10b
movzx rdx, dl
lea r9, [ r9 + rdx ]
adox r13, [ rsp + 0x1e0 ]
mov rdx, 0x100000001 
mulx r10, r8, rdi
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r12, r10, r8
adcx r14, r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp + 0x300 ], r12
mulx r12, r13, r8
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x308 ], r10
mov [ rsp + 0x310 ], r14
mulx r14, r10, r8
adox rcx, [ rsp + 0x1d8 ]
adcx rbx, rcx
setc cl
clc
adcx r10, r12
adox r15, [ rsp + 0x1c8 ]
adox r9, [ rsp + 0x1d0 ]
mov r12, 0xfffffffffffffffe 
mov rdx, r8
mov [ rsp + 0x318 ], r10
mulx r10, r8, r12
seto dl
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox r11, [ rsp + 0x148 ]
seto bpl
inc r12
adox r13, rdi
adcx r8, r14
mov r13, [ rsp + 0x310 ]
seto dil
dec r12
movzx rbp, bpl
adox rbp, r12
adox r13, [ rsp + 0x170 ]
seto r14b
inc r12
mov rbp, -0x1 
movzx rcx, cl
adox rcx, rbp
adox r15, [ rsp + 0x2f0 ]
adox r9, [ rsp + 0x2f8 ]
seto cl
inc rbp
mov r12, -0x1 
movzx r14, r14b
adox r14, r12
adox rbx, [ rsp + 0x168 ]
seto r14b
dec rbp
movzx rdi, dil
adox rdi, rbp
adox r11, [ rsp + 0x318 ]
adcx r10, [ rsp + 0x308 ]
mov r12, [ rsp + 0x308 ]
mov rdi, r12
adcx rdi, [ rsp + 0x300 ]
adox r8, r13
adox r10, rbx
seto r13b
inc rbp
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox r15, [ rsp + 0x158 ]
adox r9, [ rsp + 0x160 ]
movzx r14, cl
movzx rdx, dl
lea r14, [ r14 + rdx ]
adcx r12, [ rsp + 0x300 ]
adox r14, [ rsp + 0x178 ]
setc dl
seto cl
mov rbx, r11
mov [ rsp + 0x320 ], r10
mov r10, 0xffffffff 
sub rbx, r10
dec rbp
movzx r13, r13b
adox r13, rbp
adox r15, rdi
adox r12, r9
movzx rdi, dl
mov r13, [ rsp + 0x300 ]
lea rdi, [ rdi + r13 ]
adox rdi, r14
seto r13b
mov r9, r8
mov rdx, 0xffffffff00000000 
sbb r9, rdx
movzx r14, r13b
movzx rcx, cl
lea r14, [ r14 + rcx ]
mov rcx, [ rsp + 0x320 ]
mov r13, 0xfffffffffffffffe 
sbb rcx, r13
mov rbp, r15
mov r13, 0xffffffffffffffff 
sbb rbp, r13
mov rdx, r12
sbb rdx, r13
mov r10, rdi
sbb r10, r13
sbb r14, 0x00000000
cmovc rdx, r12
cmovc r9, r8
cmovc r10, rdi
cmovc rcx, [ rsp + 0x320 ]
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], rcx
cmovc rbp, r15
mov [ r14 + 0x18 ], rbp
mov [ r14 + 0x28 ], r10
mov [ r14 + 0x20 ], rdx
cmovc rbx, r11
mov [ r14 + 0x8 ], r9
mov [ r14 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 936
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2345
; seed 3233498345420058 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 30749 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=70, initial num_batches=31): 788 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.025626849653647272
; number reverted permutation / tried permutation: 312 / 504 =61.905%
; number reverted decision / tried decision: 302 / 495 =61.010%
; validated in 24.611s
