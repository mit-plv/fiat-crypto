SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 904
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r10
mulx r10, r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rax
mov [ rsp - 0x8 ], r15
mulx r15, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], rcx
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], r11
mov [ rsp + 0x38 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], rcx
mov [ rsp + 0x48 ], r11
mulx r11, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], rcx
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r14
mov [ rsp + 0x78 ], r10
mulx r10, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], r10
mov [ rsp + 0x88 ], r14
mulx r14, r10, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r14
mov [ rsp + 0x98 ], r10
mulx r10, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], r10
mov [ rsp + 0xa8 ], r14
mulx r14, r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], r13
mulx r13, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r13
mov [ rsp + 0xc8 ], r10
mulx r10, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r10
mov [ rsp + 0xd8 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
xor rdx, rdx
adox rcx, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], rcx
mulx rcx, r14, [ rsi + 0x0 ]
adox rax, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], rax
mulx rax, r11, [ rsi + 0x20 ]
adox r14, r15
adcx r13, rbp
adox r11, rcx
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
adox r12, rax
setc dl
clc
adcx rbp, r13
mov al, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], rbp
mulx rbp, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r12
mulx r12, r13, [ rsi + 0x18 ]
adcx r8, r15
setc dl
clc
adcx rdi, r9
mov r9, [ rsp + 0xd8 ]
adcx r9, [ rsp + 0xb8 ]
mov r15, [ rsp + 0x78 ]
adcx r15, [ rsp + 0xc8 ]
mov [ rsp + 0x110 ], r15
mov r15, [ rsp + 0x70 ]
adcx r15, [ rsp + 0xc0 ]
mov [ rsp + 0x118 ], r15
seto r15b
mov [ rsp + 0x120 ], r9
mov r9, -0x2 
inc r9
adox r13, rbp
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], r13
mulx r13, r9, [ rsi + 0x0 ]
adox r12, [ rsp + 0x68 ]
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x130 ], r12
setc r12b
clc
mov [ rsp + 0x138 ], r9
mov r9, -0x1 
movzx rax, al
adcx rax, r9
adcx rdx, [ rsp + 0xd0 ]
mov rax, [ rsp + 0x0 ]
adcx rax, [ rsp + 0x88 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], rax
mov [ rsp + 0x148 ], rdi
mulx rdi, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r9
mov [ rsp + 0x158 ], r8
mulx r8, r9, [ rsi + 0x20 ]
adcx r9, [ rsp + 0x80 ]
adcx rax, r8
mov rdx, [ rsp + 0x28 ]
adox rdx, [ rsp + 0x60 ]
mov r8, [ rsp + 0x38 ]
adox r8, [ rsp + 0x20 ]
mov [ rsp + 0x160 ], rax
mov rax, [ rsp + 0x30 ]
adox rax, [ rsp + 0xa8 ]
mov [ rsp + 0x168 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], rax
mov [ rsp + 0x178 ], r8
mulx r8, rax, [ rsi + 0x8 ]
mov rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x180 ], r9
mov r9, 0x0 
adox rdx, r9
dec r9
movzx rbp, bpl
adox rbp, r9
adox rax, [ rsp - 0x8 ]
adox r8, [ rsp + 0x58 ]
mov rbp, 0x0 
adcx rdi, rbp
mov rbp, [ rsp + 0x50 ]
adox rbp, [ rsp + 0x18 ]
clc
adcx r13, [ rsp - 0x10 ]
mov r9, [ rsp + 0x48 ]
adcx r9, [ rsp - 0x18 ]
mov [ rsp + 0x188 ], rdi
mov rdi, 0x100000001 
xchg rdx, rdi
mov [ rsp + 0x190 ], rdi
mov [ rsp + 0x198 ], r9
mulx r9, rdi, [ rsp + 0xb0 ]
mov r9, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp + 0x1a0 ], r13
mulx r13, rdi, r9
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x1a8 ], rbp
mov [ rsp + 0x1b0 ], r8
mulx r8, rbp, r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b8 ], rax
mov [ rsp + 0x1c0 ], r11
mulx r11, rax, [ rsi + 0x10 ]
movzx rdx, r15b
mov [ rsp + 0x1c8 ], rcx
mov rcx, [ rsp - 0x28 ]
lea rdx, [ rdx + rcx ]
setc cl
clc
mov r15, -0x1 
movzx r12, r12b
adcx r12, r15
adcx rax, [ rsp - 0x20 ]
setc r12b
clc
movzx rcx, cl
adcx rcx, r15
adcx r10, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x98 ]
mov rcx, [ rsp - 0x30 ]
adcx rcx, [ rsp + 0x90 ]
mov r15, 0xffffffff 
xchg rdx, r15
mov [ rsp + 0x1d0 ], rcx
mov [ rsp + 0x1d8 ], rbx
mulx rbx, rcx, r9
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0x1e0 ], r10
mov r10, 0x0 
adox rdx, r10
mov [ rsp + 0x1e8 ], rax
mov rax, -0x3 
inc rax
adox rdi, rbx
mov rbx, [ rsp - 0x38 ]
adcx rbx, r10
mov r10, 0xfffffffffffffffe 
xchg rdx, r9
mov [ rsp + 0x1f0 ], rbx
mulx rbx, rax, r10
movzx rdx, r12b
lea rdx, [ rdx + r11 ]
clc
adcx rcx, [ rsp + 0xb0 ]
adcx rdi, [ rsp + 0xe0 ]
adox rax, r13
adcx rax, [ rsp + 0xe8 ]
mov rcx, rbp
adox rcx, rbx
mov r13, rbp
adox r13, r8
adox rbp, r8
mov r11, 0x0 
adox r8, r11
adcx rcx, r14
mov r14, -0x3 
inc r14
adox rdi, [ rsp + 0x1c8 ]
adcx r13, [ rsp + 0x1c0 ]
mov r12, 0x100000001 
xchg rdx, r12
mulx r11, rbx, rdi
adcx rbp, [ rsp + 0x108 ]
adcx r8, r15
adox rax, [ rsp + 0xf8 ]
adox rcx, [ rsp + 0x158 ]
mov r11, 0xffffffff 
mov rdx, rbx
mulx r15, rbx, r11
adox r13, [ rsp + 0x1b8 ]
adox rbp, [ rsp + 0x1b0 ]
mov r14, 0xffffffffffffffff 
mulx r11, r10, r14
adox r8, [ rsp + 0x1a8 ]
mov r14, 0xffffffff00000000 
mov [ rsp + 0x1f8 ], r12
mov [ rsp + 0x200 ], r8
mulx r8, r12, r14
seto r14b
mov [ rsp + 0x208 ], rbp
mov rbp, -0x2 
inc rbp
adox rbx, rdi
movzx rbx, r14b
adcx rbx, r9
setc r9b
clc
adcx r12, r15
adox r12, rax
seto dil
inc rbp
adox r12, [ rsp - 0x40 ]
mov rax, 0x100000001 
xchg rdx, r12
mulx r14, r15, rax
mov r14, 0xfffffffffffffffe 
xchg rdx, r12
mulx rax, rbp, r14
adcx rbp, r8
mov rdx, 0xffffffffffffffff 
mulx r14, r8, r15
mov rdx, 0xfffffffffffffffe 
mov byte [ rsp + 0x210 ], r9b
mov [ rsp + 0x218 ], rbx
mulx rbx, r9, r15
mov rdx, 0xffffffff 
mov [ rsp + 0x220 ], r13
mov [ rsp + 0x228 ], r14
mulx r14, r13, r15
seto dl
mov [ rsp + 0x230 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox rcx, rbp
setc dil
clc
movzx rdx, dl
adcx rdx, r13
adcx rcx, [ rsp + 0x148 ]
mov rdx, 0xffffffff00000000 
mulx r13, rbp, r15
seto r15b
mov rdx, -0x2 
inc rdx
adox rbp, r14
seto r14b
inc rdx
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox rax, r10
setc dil
clc
movzx r14, r14b
adcx r14, rdx
adcx r13, r9
mov r9, r8
adcx r9, rbx
mov rbx, r10
adox rbx, r11
mov r14, r8
adcx r14, [ rsp + 0x228 ]
adcx r8, [ rsp + 0x228 ]
adox r10, r11
setc dl
clc
adcx r12, [ rsp + 0x230 ]
adcx rbp, rcx
setc r12b
clc
adcx rbp, [ rsp + 0x100 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mov [ rsp + 0x238 ], r8
mov [ rsp + 0x240 ], r14
mulx r14, r8, rbp
mov r14, 0x0 
adox r11, r14
movzx r14, cl
mov rdx, [ rsp + 0x228 ]
lea r14, [ r14 + rdx ]
mov rdx, -0x1 
inc rdx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox rax, [ rsp + 0x220 ]
mov r15, 0xffffffffffffffff 
mov rdx, r8
mulx rcx, r8, r15
mov r15, 0xffffffff 
mov [ rsp + 0x248 ], r14
mov [ rsp + 0x250 ], r9
mulx r9, r14, r15
setc r15b
clc
mov [ rsp + 0x258 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx rax, [ rsp + 0x120 ]
seto dil
inc rcx
mov rcx, -0x1 
movzx r12, r12b
adox r12, rcx
adox rax, r13
setc r13b
clc
adcx r14, rbp
mov r14, 0xffffffff00000000 
mulx rbp, r12, r14
setc cl
clc
mov r14, -0x1 
movzx rdi, dil
adcx rdi, r14
adcx rbx, [ rsp + 0x208 ]
seto dil
inc r14
adox r12, r9
adcx r10, [ rsp + 0x200 ]
adcx r11, [ rsp + 0x218 ]
movzx r9, byte [ rsp + 0x210 ]
adcx r9, r14
mov r14, 0xfffffffffffffffe 
mov byte [ rsp + 0x260 ], dil
mov [ rsp + 0x268 ], r9
mulx r9, rdi, r14
adox rdi, rbp
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx rbx, [ rsp + 0x110 ]
adcx r10, [ rsp + 0x118 ]
adcx r11, [ rsp + 0x1e8 ]
setc r13b
clc
movzx r15, r15b
adcx r15, rdx
adcx rax, [ rsp + 0x128 ]
mov r15, r8
adox r15, r9
setc bpl
clc
movzx rcx, cl
adcx rcx, rdx
adcx rax, r12
setc cl
clc
adcx rax, [ rsp + 0x138 ]
mov r12, 0x100000001 
mov rdx, r12
mulx r9, r12, rax
mov r9, [ rsp + 0x268 ]
setc r14b
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r9, [ rsp + 0x1f8 ]
mov r13, 0xffffffff00000000 
mov rdx, r13
mov byte [ rsp + 0x270 ], r14b
mulx r14, r13, r12
mov rdx, r8
adox rdx, [ rsp + 0x258 ]
mov [ rsp + 0x278 ], rdx
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x280 ], r15
mov [ rsp + 0x288 ], rdi
mulx rdi, r15, r12
adox r8, [ rsp + 0x258 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x290 ], r8
mov [ rsp + 0x298 ], rdi
mulx rdi, r8, r12
seto dl
mov byte [ rsp + 0x2a0 ], cl
mov rcx, -0x2 
inc rcx
adox r8, rax
seto r8b
inc rcx
adox r13, rdi
setc al
movzx rdi, byte [ rsp + 0x260 ]
clc
mov rcx, -0x1 
adcx rdi, rcx
adcx rbx, [ rsp + 0x250 ]
adcx r10, [ rsp + 0x240 ]
setc dil
clc
movzx rbp, bpl
adcx rbp, rcx
adcx rbx, [ rsp + 0x130 ]
adcx r10, [ rsp + 0x180 ]
seto bpl
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox r11, [ rsp + 0x238 ]
adcx r11, [ rsp + 0x178 ]
adox r9, [ rsp + 0x248 ]
movzx rdi, dl
mov rcx, [ rsp + 0x258 ]
lea rdi, [ rdi + rcx ]
movzx rcx, al
mov rdx, 0x0 
adox rcx, rdx
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r14, r15
setc al
movzx r15, byte [ rsp + 0x2a0 ]
clc
adcx r15, rdx
adcx rbx, [ rsp + 0x288 ]
adcx r10, [ rsp + 0x280 ]
mov r15, 0xffffffffffffffff 
mov rdx, r12
mulx rbp, r12, r15
adcx r11, [ rsp + 0x278 ]
mov rdx, r12
adox rdx, [ rsp + 0x298 ]
mov r15, r12
adox r15, rbp
mov [ rsp + 0x2a8 ], r15
setc r15b
mov [ rsp + 0x2b0 ], rdi
movzx rdi, byte [ rsp + 0x270 ]
clc
mov [ rsp + 0x2b8 ], rdx
mov rdx, -0x1 
adcx rdi, rdx
adcx rbx, [ rsp + 0x1a0 ]
adox r12, rbp
adcx r10, [ rsp + 0x198 ]
setc dil
clc
movzx rax, al
adcx rax, rdx
adcx r9, [ rsp + 0x170 ]
adcx rcx, [ rsp + 0x190 ]
setc al
clc
movzx r15, r15b
adcx r15, rdx
adcx r9, [ rsp + 0x290 ]
setc r15b
clc
movzx r8, r8b
adcx r8, rdx
adcx rbx, r13
adcx r14, r10
seto r8b
inc rdx
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox r11, [ rsp + 0x1e0 ]
seto dil
mov r10, -0x3 
inc r10
adox rbx, [ rsp - 0x48 ]
adox r14, [ rsp + 0xf0 ]
mov rdx, 0x100000001 
mulx r13, r10, rbx
mov r13, 0xffffffff 
mov rdx, r10
mov [ rsp + 0x2c0 ], r12
mulx r12, r10, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x2c8 ], r8b
mov [ rsp + 0x2d0 ], r9
mulx r9, r8, r13
mov r13, 0xffffffff00000000 
mov byte [ rsp + 0x2d8 ], dil
mov [ rsp + 0x2e0 ], r9
mulx r9, rdi, r13
seto r13b
mov byte [ rsp + 0x2e8 ], al
mov rax, -0x2 
inc rax
adox r10, rbx
mov r10, 0xfffffffffffffffe 
mulx rax, rbx, r10
adcx r11, [ rsp + 0x2b8 ]
setc dl
clc
adcx rdi, r12
setc r12b
clc
mov r10, -0x1 
movzx r13, r13b
adcx r13, r10
adcx r11, [ rsp + 0x150 ]
setc r13b
clc
movzx r15, r15b
adcx r15, r10
adcx rcx, [ rsp + 0x2b0 ]
adox rdi, r14
setc r15b
clc
movzx r12, r12b
adcx r12, r10
adcx r9, rbx
mov r14, r8
adcx r14, rax
movzx rbx, r15b
movzx rax, byte [ rsp + 0x2e8 ]
lea rbx, [ rbx + rax ]
mov rax, r8
adcx rax, [ rsp + 0x2e0 ]
setc r12b
seto r15b
mov r10, rdi
mov [ rsp + 0x2f0 ], rax
mov rax, 0xffffffff 
sub r10, rax
mov rax, 0x0 
dec rax
movzx r12, r12b
adox r12, rax
adox r8, [ rsp + 0x2e0 ]
mov r12, [ rsp + 0x2d0 ]
seto al
mov [ rsp + 0x2f8 ], r10
movzx r10, byte [ rsp + 0x2d8 ]
mov [ rsp + 0x300 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r10, r8
adox r12, [ rsp + 0x1d8 ]
setc r10b
clc
movzx rdx, dl
adcx rdx, r8
adcx r12, [ rsp + 0x2a8 ]
setc dl
clc
movzx r15, r15b
adcx r15, r8
adcx r11, r9
adox rcx, [ rsp + 0x1d0 ]
setc r15b
clc
movzx r13, r13b
adcx r13, r8
adcx r12, [ rsp + 0x140 ]
movzx r13, byte [ rsp + 0x2c8 ]
lea rbp, [ rbp + r13 ]
adox rbx, [ rsp + 0x1f0 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, r8
adcx rcx, [ rsp + 0x2c0 ]
seto r9b
inc r8
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox rcx, [ rsp + 0x168 ]
adcx rbp, rbx
adox rbp, [ rsp + 0x160 ]
movzx r13, r9b
adcx r13, r8
clc
movzx r15, r15b
adcx r15, rdx
adcx r12, r14
adox r13, [ rsp + 0x188 ]
adcx rcx, [ rsp + 0x2f0 ]
adcx rbp, [ rsp + 0x300 ]
setc r14b
seto r15b
movzx r9, r10b
add r9, -0x1
mov r10, r11
mov r9, 0xffffffff00000000 
sbb r10, r9
mov rbx, r12
mov r8, 0xfffffffffffffffe 
sbb rbx, r8
mov rdx, rcx
mov r8, 0xffffffffffffffff 
sbb rdx, r8
movzx r8, al
mov r9, [ rsp + 0x2e0 ]
lea r8, [ r8 + r9 ]
mov r9, 0x0 
dec r9
movzx r14, r14b
adox r14, r9
adox r13, r8
movzx rax, r15b
mov r14, 0x0 
adox rax, r14
mov r15, rbp
mov r8, 0xffffffffffffffff 
sbb r15, r8
mov r14, r13
sbb r14, r8
sbb rax, 0x00000000
cmovc rdx, rcx
mov rax, [ rsp + 0x2f8 ]
cmovc rax, rdi
cmovc r15, rbp
cmovc r10, r11
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x18 ], rdx
cmovc rbx, r12
cmovc r14, r13
mov [ rdi + 0x10 ], rbx
mov [ rdi + 0x28 ], r14
mov [ rdi + 0x20 ], r15
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 904
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1143
; seed 4498055012211125 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 25943 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=90, initial num_batches=31): 764 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02944917704197664
; number reverted permutation / tried permutation: 276 / 482 =57.261%
; number reverted decision / tried decision: 303 / 517 =58.607%
; validated in 19.341s
