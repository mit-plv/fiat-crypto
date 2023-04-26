SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 872
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], rcx
mulx rcx, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], rax
mulx rax, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], rbp
mulx rbp, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r11
mulx r11, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], rbp
mulx rbp, r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r11
mulx r11, rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], r13
mulx r13, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], r13
mulx r13, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], rdi
mulx rdi, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], rbx
mulx rbx, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], rcx
mov [ rsp + 0x98 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r11
mov [ rsp + 0xa8 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r11
mov [ rsp + 0xb8 ], rbp
mulx rbp, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rbp
mov [ rsp + 0xc8 ], r11
mulx r11, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], r11
mov [ rsp + 0xd8 ], rbp
mulx rbp, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox rdi, r10
adox r11, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, rdx
adox r8, rbp
adcx r12, rcx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], r8
mulx r8, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r11
mov [ rsp + 0xf8 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
adcx r12, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r12
mulx r12, rbx, rdx
adcx r14, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], r14
mulx r14, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], r11
mov [ rsp + 0x118 ], r14
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], r8
mulx r8, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], rbp
mov [ rsp + 0x138 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
setc dl
clc
adcx r15, rdi
adox rbx, r9
adcx rax, [ rsp + 0xb8 ]
seto r9b
mov rdi, -0x2 
inc rdi
adox r10, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0x80 ]
adox r13, [ rsp + 0x98 ]
adcx rcx, [ rsp + 0x78 ]
mov dil, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], rbx
mov [ rsp + 0x148 ], rcx
mulx rcx, rbx, rdx
mov rdx, 0x100000001 
mov [ rsp + 0x150 ], rbp
mov [ rsp + 0x158 ], rax
mulx rax, rbp, rbx
mov rax, [ rsp + 0x90 ]
adox rax, [ rsp + 0x70 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x160 ], r15
mov [ rsp + 0x168 ], rax
mulx rax, r15, rbp
setc dl
clc
mov [ rsp + 0x170 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx r12, [ rsp + 0x58 ]
mov r9, [ rsp + 0xa8 ]
adox r9, [ rsp + 0x28 ]
mov r13, 0xffffffffffffffff 
xchg rdx, rbp
mov [ rsp + 0x178 ], r12
mov [ rsp + 0x180 ], r9
mulx r9, r12, r13
seto r13b
mov [ rsp + 0x188 ], r10
mov r10, -0x2 
inc r10
adox rcx, [ rsp + 0x48 ]
mov r10, 0xffffffff00000000 
mov [ rsp + 0x190 ], r9
mov byte [ rsp + 0x198 ], r13b
mulx r13, r9, r10
mov r10, [ rsp + 0x40 ]
adox r10, [ rsp + 0x20 ]
mov [ rsp + 0x1a0 ], r10
mov r10, [ rsp - 0x20 ]
mov [ rsp + 0x1a8 ], rcx
setc cl
clc
mov byte [ rsp + 0x1b0 ], dil
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r10, [ rsp - 0x18 ]
seto bpl
inc rdi
adox r11, r14
mov r14, 0xffffffff 
mov byte [ rsp + 0x1b8 ], cl
mulx rcx, rdi, r14
setc dl
clc
adcx r9, rcx
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], r11
mulx r11, r14, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x1c8 ], r10
mov r10, -0x2 
inc r10
adox rdi, rbx
adcx r15, r13
seto dil
inc r10
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox r8, [ rsp + 0xc8 ]
mov r13, r12
adcx r13, rax
mov rax, [ rsp + 0x18 ]
adox rax, [ rsp + 0xc0 ]
mov rdx, [ rsp + 0x8 ]
setc r10b
movzx rbx, byte [ rsp + 0x1b0 ]
clc
mov [ rsp + 0x1d0 ], rax
mov rax, -0x1 
adcx rbx, rax
adcx rdx, [ rsp + 0x50 ]
mov rbx, [ rsp + 0x10 ]
adox rbx, [ rsp + 0x138 ]
seto al
mov [ rsp + 0x1d8 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox r9, [ rsp + 0x1a8 ]
setc dil
clc
adcx r9, [ rsp - 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1e0 ], rbx
mov [ rsp + 0x1e8 ], r8
mulx r8, rbx, r9
mov r8, [ rsp + 0x0 ]
setc dl
clc
mov byte [ rsp + 0x1f0 ], cl
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx r8, [ rsp + 0x38 ]
mov rdi, [ rsp + 0x30 ]
mov rcx, 0x0 
adcx rdi, rcx
mov rcx, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x1f8 ], rdi
mov [ rsp + 0x200 ], r8
mulx r8, rdi, rcx
mov rcx, [ rsp + 0x130 ]
clc
mov [ rsp + 0x208 ], r8
mov r8, -0x1 
movzx rax, al
adcx rax, r8
adcx rcx, [ rsp - 0x8 ]
mov rax, [ rsp - 0x10 ]
mov r8, 0x0 
adcx rax, r8
movzx r8, byte [ rsp + 0x198 ]
clc
mov [ rsp + 0x210 ], rax
mov rax, -0x1 
adcx r8, rax
adcx r14, [ rsp + 0xa0 ]
adox r15, [ rsp + 0x1a0 ]
mov r8, 0x0 
adcx r11, r8
mov r8, r12
clc
movzx r10, r10b
adcx r10, rax
adcx r8, [ rsp + 0x190 ]
adcx r12, [ rsp + 0x190 ]
mov r10, [ rsp - 0x30 ]
setc al
clc
mov [ rsp + 0x218 ], rcx
mov rcx, -0x1 
movzx rbp, bpl
adcx rbp, rcx
adcx r10, [ rsp + 0xd8 ]
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0x220 ], r11
mulx r11, rcx, rbp
mov rbp, [ rsp + 0xd0 ]
adcx rbp, [ rsp + 0x128 ]
mov [ rsp + 0x228 ], r14
mov r14, [ rsp + 0x68 ]
adcx r14, [ rsp + 0x118 ]
mov [ rsp + 0x230 ], rdi
mov rdi, 0xffffffff 
mov [ rsp + 0x238 ], r11
mov [ rsp + 0x240 ], r12
mulx r12, r11, rdi
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x248 ], r14
mov [ rsp + 0x250 ], rcx
mulx rcx, r14, rdi
mov rdx, [ rsp + 0x60 ]
mov rdi, 0x0 
adcx rdx, rdi
movzx rdi, al
mov [ rsp + 0x258 ], rdx
mov rdx, [ rsp + 0x190 ]
lea rdi, [ rdi + rdx ]
clc
adcx r14, r12
adox r13, r10
seto dl
mov rax, 0x0 
dec rax
movzx rbx, bl
adox rbx, rax
adox r15, [ rsp + 0x188 ]
setc bl
clc
adcx r11, r9
setc r11b
clc
movzx rdx, dl
adcx rdx, rax
adcx rbp, r8
adox r13, [ rsp + 0x170 ]
setc r9b
clc
movzx r11, r11b
adcx r11, rax
adcx r15, r14
adox rbp, [ rsp + 0x168 ]
seto r8b
inc rax
adox r15, [ rsp + 0x110 ]
setc r10b
clc
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx rcx, [ rsp + 0x250 ]
mov r14, [ rsp + 0x240 ]
setc bl
clc
movzx r9, r9b
adcx r9, r12
adcx r14, [ rsp + 0x248 ]
mov rdx, [ rsp + 0x238 ]
setc r11b
clc
movzx rbx, bl
adcx rbx, r12
adcx rdx, [ rsp + 0x230 ]
mov r9, [ rsp + 0x208 ]
mov rbx, r9
adcx rbx, [ rsp + 0x230 ]
setc al
clc
movzx r10, r10b
adcx r10, r12
adcx r13, rcx
adox r13, [ rsp + 0x160 ]
seto r10b
inc r12
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox r14, [ rsp + 0x180 ]
setc r8b
clc
movzx r11, r11b
adcx r11, rcx
adcx rdi, [ rsp + 0x258 ]
adox rdi, [ rsp + 0x228 ]
mov r11, r9
seto r12b
inc rcx
mov rcx, -0x1 
movzx rax, al
adox rax, rcx
adox r11, [ rsp + 0x230 ]
movzx r12, r12b
movzx rax, r12b
adcx rax, [ rsp + 0x220 ]
setc r12b
clc
movzx r8, r8b
adcx r8, rcx
adcx rbp, rdx
seto dl
inc rcx
mov r8, -0x1 
movzx r10, r10b
adox r10, r8
adox rbp, [ rsp + 0x158 ]
adcx rbx, r14
adcx r11, rdi
adox rbx, [ rsp + 0x150 ]
movzx r10, dl
lea r10, [ r10 + r9 ]
adcx r10, rax
movzx r9, r12b
adcx r9, rcx
mov r14, 0x100000001 
mov rdx, r14
mulx rdi, r14, r15
mov rdi, 0xffffffff 
mov rdx, r14
mulx r12, r14, rdi
mov rax, 0xffffffffffffffff 
mulx r8, rcx, rax
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x260 ], r9
mulx r9, rax, rdi
clc
adcx rax, r12
adox r11, [ rsp + 0x148 ]
setc r12b
clc
adcx r14, r15
mov r14, 0xfffffffffffffffe 
mulx rdi, r15, r14
adcx rax, r13
setc r13b
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx r9, r15
movzx r12, byte [ rsp + 0x1f0 ]
mov r15, [ rsp - 0x38 ]
lea r12, [ r12 + r15 ]
mov r15, rcx
adcx r15, rdi
setc dil
clc
movzx r13, r13b
adcx r13, rdx
adcx rbp, r9
adcx r15, rbx
adox r10, [ rsp + 0x1c8 ]
seto bl
inc rdx
adox rax, [ rsp + 0x120 ]
mov r13, 0x100000001 
mov rdx, r13
mulx r9, r13, rax
adox rbp, [ rsp + 0x1c0 ]
mov r9, 0xffffffff 
mov rdx, r9
mulx r14, r9, r13
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x268 ], r12
mov byte [ rsp + 0x270 ], bl
mulx rbx, r12, r13
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x278 ], rbx
mov [ rsp + 0x280 ], r10
mulx r10, rbx, r13
seto dl
mov [ rsp + 0x288 ], r11
mov r11, -0x2 
inc r11
adox rbx, r14
setc r14b
clc
adcx r9, rax
adcx rbx, rbp
mov r9, r8
setc al
clc
movzx rdi, dil
adcx rdi, r11
adcx r9, rcx
adox r12, r10
seto dil
inc r11
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r15, [ rsp + 0x1e8 ]
adcx rcx, r8
adcx r8, r11
clc
movzx r14, r14b
adcx r14, rbp
adcx r9, [ rsp + 0x288 ]
adox r9, [ rsp + 0x1d0 ]
adcx rcx, [ rsp + 0x280 ]
adox rcx, [ rsp + 0x1e0 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r10, r14, r13
mov r13, [ rsp + 0x268 ]
setc r11b
movzx rbp, byte [ rsp + 0x270 ]
clc
mov rdx, -0x1 
adcx rbp, rdx
adcx r13, [ rsp + 0x260 ]
seto bpl
inc rdx
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox r15, r12
setc al
clc
movzx r11, r11b
adcx r11, rdx
adcx r13, r8
movzx r12, al
mov r8, 0x0 
adcx r12, r8
mov r11, r14
clc
movzx rdi, dil
adcx rdi, rdx
adcx r11, [ rsp + 0x278 ]
adox r11, r9
mov rdi, r14
adcx rdi, r10
adox rdi, rcx
adcx r14, r10
setc r9b
clc
movzx rbp, bpl
adcx rbp, rdx
adcx r13, [ rsp + 0x218 ]
movzx rbp, r9b
lea rbp, [ rbp + r10 ]
adox r14, r13
adcx r12, [ rsp + 0x210 ]
adox rbp, r12
setc cl
clc
adcx rbx, [ rsp - 0x48 ]
adcx r15, [ rsp + 0xf8 ]
mov r10, 0x100000001 
mov rdx, r10
mulx rax, r10, rbx
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx r9, rax, r10
movzx r13, cl
adox r13, r8
mov rcx, 0xffffffff 
mov rdx, rcx
mulx r12, rcx, r10
mov r8, 0xffffffff00000000 
mov rdx, r8
mov [ rsp + 0x290 ], r13
mulx r13, r8, r10
adcx r11, [ rsp + 0xf0 ]
mov rdx, -0x2 
inc rdx
adox rcx, rbx
setc cl
clc
adcx r8, r12
adox r8, r15
seto bl
inc rdx
adox r8, [ rsp + 0xb0 ]
mov r15, 0x100000001 
mov rdx, r15
mulx r12, r15, r8
mov r12, 0xfffffffffffffffe 
mov rdx, r15
mov [ rsp + 0x298 ], r11
mulx r11, r15, r12
xchg rdx, r12
mov byte [ rsp + 0x2a0 ], bl
mov [ rsp + 0x2a8 ], rbp
mulx rbp, rbx, r10
mov r10, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp + 0x2b0 ], r11
mulx r11, r10, r12
seto dl
mov [ rsp + 0x2b8 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox rdi, [ rsp + 0xe8 ]
adcx rbx, r13
adox r14, [ rsp + 0x140 ]
mov r13, 0xffffffff00000000 
xchg rdx, r13
mulx r11, rcx, r12
mov rdx, 0xffffffff 
mov [ rsp + 0x2c0 ], r14
mov byte [ rsp + 0x2c8 ], r13b
mulx r13, r14, r12
mov r12, rax
adcx r12, rbp
mov rbp, rax
adcx rbp, r9
seto dl
mov [ rsp + 0x2d0 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, r13
setc r13b
clc
adcx r14, r8
adox r15, r11
mov r14, r10
adox r14, [ rsp + 0x2b0 ]
movzx r8, byte [ rsp + 0x1b8 ]
mov r11, [ rsp - 0x40 ]
lea r8, [ r8 + r11 ]
mov r11, r9
setc bpl
clc
mov [ rsp + 0x2d8 ], r14
mov r14, -0x1 
movzx r13, r13b
adcx r13, r14
adcx r11, rax
mov rax, 0x0 
adcx r9, rax
mov r13, [ rsp + 0x178 ]
clc
movzx rdx, dl
adcx rdx, r14
adcx r13, [ rsp + 0x2a8 ]
mov rdx, r10
adox rdx, [ rsp + 0x2b8 ]
adcx r8, [ rsp + 0x290 ]
adox r10, [ rsp + 0x2b8 ]
seto al
movzx r14, byte [ rsp + 0x2a0 ]
mov [ rsp + 0x2e0 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r14, r10
adox rbx, [ rsp + 0x298 ]
adox r12, rdi
setc r14b
movzx rdi, byte [ rsp + 0x2c8 ]
clc
adcx rdi, r10
adcx rbx, [ rsp + 0xe0 ]
adcx r12, [ rsp + 0x100 ]
mov rdi, [ rsp + 0x2d0 ]
adox rdi, [ rsp + 0x2c0 ]
adox r11, r13
adox r9, r8
movzx r13, r14b
mov r8, 0x0 
adox r13, r8
adcx rdi, [ rsp + 0x108 ]
adcx r11, [ rsp + 0x1d8 ]
dec r8
movzx rbp, bpl
adox rbp, r8
adox rbx, rcx
adcx r9, [ rsp + 0x200 ]
adox r15, r12
adox rdi, [ rsp + 0x2d8 ]
adox rdx, r11
adox r9, [ rsp + 0x2e0 ]
movzx r10, al
mov rcx, [ rsp + 0x2b8 ]
lea r10, [ r10 + rcx ]
setc cl
seto bpl
mov r14, rbx
mov rax, 0xffffffff 
sub r14, rax
mov r12, r15
mov r11, 0xffffffff00000000 
sbb r12, r11
mov r8, rdi
mov rax, 0xfffffffffffffffe 
sbb r8, rax
mov r11, rdx
mov rax, 0xffffffffffffffff 
sbb r11, rax
mov rax, 0x0 
dec rax
movzx rcx, cl
adox rcx, rax
adox r13, [ rsp + 0x1f8 ]
seto cl
inc rax
mov rax, -0x1 
movzx rbp, bpl
adox rbp, rax
adox r13, r10
movzx rbp, cl
mov r10, 0x0 
adox rbp, r10
mov rcx, r9
mov r10, 0xffffffffffffffff 
sbb rcx, r10
mov rax, r13
sbb rax, r10
sbb rbp, 0x00000000
cmovc r14, rbx
cmovc r12, r15
cmovc r8, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r12
cmovc rcx, r9
cmovc r11, rdx
mov [ rbp + 0x0 ], r14
mov [ rbp + 0x18 ], r11
cmovc rax, r13
mov [ rbp + 0x10 ], r8
mov [ rbp + 0x20 ], rcx
mov [ rbp + 0x28 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 872
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.1476
; seed 3541244842395196 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 25383 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=89, initial num_batches=31): 758 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.029862506401922548
; number reverted permutation / tried permutation: 319 / 495 =64.444%
; number reverted decision / tried decision: 319 / 504 =63.294%
; validated in 18.858s
