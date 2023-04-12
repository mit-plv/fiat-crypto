SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 864
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rcx
mulx rcx, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], rax
mov [ rsp - 0x18 ], rbp
mulx rbp, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], rax
mulx rax, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r13
mulx r13, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], r12
mulx r12, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rcx
mulx rcx, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r11
mov [ rsp + 0x48 ], r15
mulx r15, r11, [ rsi + 0x20 ]
test al, al
adox rcx, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], rcx
mulx rcx, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], r15
mulx r15, r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x68 ], r15
mov [ rsp + 0x70 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], r15
mulx r15, r12, r10
mov r15, 0xfffffffffffffffe 
mov rdx, r12
mov [ rsp + 0x88 ], r11
mulx r11, r12, r15
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], r11
mov [ rsp + 0x98 ], r12
mulx r12, r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r14
mov [ rsp + 0xa8 ], r9
mulx r9, r14, [ rsi + 0x18 ]
adcx r11, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r9
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r11
mulx r11, r14, [ rsi + 0x18 ]
adcx rdi, r12
setc dl
clc
adcx rbp, r13
mov r13, 0xffffffff 
xchg rdx, r13
mov [ rsp + 0xc8 ], rdi
mulx rdi, r12, r15
adox r8, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
adcx rcx, rax
mov rdx, [ rsp + 0xa0 ]
adox rdx, [ rsp + 0xa8 ]
adcx rbx, r9
mov rax, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0xd8 ], r15
mulx r15, r9, rax
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], r15
mulx r15, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], r9
mulx r9, r15, [ rsi + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x110 ], rdi
mov byte [ rsp + 0x118 ], r13b
mulx r13, rdi, rax
adox rbp, [ rsp + 0x48 ]
adcx rbx, r8
seto al
mov r8, -0x2 
inc r8
adox r12, r10
adcx r15, rcx
mov rdx, [ rsi + 0x0 ]
mulx r10, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, 0x0 
adcx r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r12
mov [ rsp + 0x128 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
clc
adcx r10, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r12
mulx r12, r10, rdx
mov rdx, [ rsp + 0x28 ]
mov [ rsp + 0x140 ], r9
setc r9b
clc
adcx rdx, [ rsp + 0x18 ]
mov [ rsp + 0x148 ], rdx
seto dl
mov [ rsp + 0x150 ], r15
mov r15, -0x2 
inc r15
adox rbp, [ rsp + 0x10 ]
adcx r10, [ rsp + 0x8 ]
adcx r14, r12
mov r12b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], rbp
mulx rbp, r15, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x0 ]
adox rdx, [ rsp + 0x38 ]
adcx r11, [ rsp + 0x88 ]
mov [ rsp + 0x160 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], r14
mov [ rsp + 0x170 ], r10
mulx r10, r14, [ rsi + 0x28 ]
adcx r14, [ rsp + 0x60 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x178 ], r14
setc r14b
mov [ rsp + 0x180 ], r11
movzx r11, byte [ rsp + 0x118 ]
clc
mov [ rsp + 0x188 ], rbx
mov rbx, -0x1 
adcx r11, rbx
adcx rdx, [ rsp - 0x20 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r8
mulx r8, rbx, [ rsi + 0x28 ]
adcx r15, [ rsp - 0x28 ]
adcx rbx, rbp
mov rdx, [ rsp + 0x80 ]
setc bpl
clc
mov [ rsp + 0x198 ], rbx
mov rbx, -0x1 
movzx r9, r9b
adcx r9, rbx
adcx rdx, [ rsp - 0x38 ]
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a0 ], r15
mulx r15, rbx, rdx
setc dl
clc
adcx rdi, [ rsp + 0x110 ]
adcx r13, [ rsp + 0x98 ]
mov [ rsp + 0x1a8 ], r9
mov r9b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b0 ], r11
mov [ rsp + 0x1b8 ], r10
mulx r10, r11, [ rsi + 0x18 ]
adox rbx, [ rsp + 0x30 ]
adox r11, r15
movzx rdx, bpl
lea rdx, [ rdx + r8 ]
mov r8, [ rsp + 0x108 ]
mov rbp, r8
adcx rbp, [ rsp + 0x90 ]
mov r15, r8
adcx r15, [ rsp + 0xf8 ]
mov [ rsp + 0x1c0 ], r11
seto r11b
mov [ rsp + 0x1c8 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r12, r12b
adox r12, rbx
adox rdi, [ rsp + 0xf0 ]
setc r12b
clc
movzx r11, r11b
adcx r11, rbx
adcx r10, rcx
mov rcx, [ rsp + 0x100 ]
setc r11b
clc
movzx rax, al
adcx rax, rbx
adcx rcx, [ rsp - 0x8 ]
adox r13, [ rsp + 0xe8 ]
movzx rax, r14b
mov rbx, [ rsp + 0x1b8 ]
lea rax, [ rax + rbx ]
adox rbp, [ rsp + 0xe0 ]
movzx rbx, r11b
mov r14, [ rsp + 0x190 ]
lea rbx, [ rbx + r14 ]
mov r14, [ rsp - 0x10 ]
mov r11, 0x0 
adcx r14, r11
clc
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx r8, [ rsp + 0xf8 ]
mov r12, [ rsp + 0xf8 ]
mov r11, 0x0 
adcx r12, r11
clc
adcx rdi, [ rsp + 0x58 ]
mov r11, 0x100000001 
xchg rdx, rdi
mov [ rsp + 0x1d0 ], r14
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r14, r11
mov rcx, 0xfffffffffffffffe 
xchg rdx, rcx
mov [ rsp + 0x1e0 ], rbx
mulx rbx, r11, r14
adcx r13, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0xc8 ]
adox r15, [ rsp + 0x188 ]
adcx r15, [ rsp + 0x1b0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1e8 ], r10
mov [ rsp + 0x1f0 ], rax
mulx rax, r10, r14
adox r8, [ rsp + 0x150 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1f8 ], r15
mov [ rsp + 0x200 ], rdi
mulx rdi, r15, r14
adcx r8, [ rsp + 0x1a0 ]
adox r12, [ rsp + 0x140 ]
adcx r12, [ rsp + 0x198 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x208 ], r12
mov [ rsp + 0x210 ], r8
mulx r8, r12, r14
seto r14b
mov rdx, -0x2 
inc rdx
adox r10, rcx
seto r10b
inc rdx
adox r12, rax
mov rcx, [ rsp + 0xb8 ]
setc al
clc
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx rcx, [ rsp + 0x78 ]
setc r9b
clc
movzx r10, r10b
adcx r10, rdx
adcx r13, r12
adox r11, r8
mov r8, r15
adox r8, rbx
seto bl
inc rdx
adox r13, [ rsp - 0x30 ]
adcx r11, rbp
movzx rbp, r14b
setc r10b
clc
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx rbp, [ rsp + 0x200 ]
setc r14b
clc
movzx r10, r10b
adcx r10, r12
adcx r8, [ rsp + 0x1f8 ]
mov rax, [ rsp - 0x40 ]
seto r10b
dec rdx
movzx r9, r9b
adox r9, rdx
adox rax, [ rsp + 0xb0 ]
mov r12, 0x100000001 
mov rdx, r13
mulx r9, r13, r12
mov r9, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x218 ], rax
mulx rax, r12, r9
mov r9, [ rsp - 0x48 ]
adox r9, [ rsp + 0x70 ]
mov [ rsp + 0x220 ], r9
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x228 ], rcx
mov byte [ rsp + 0x230 ], r14b
mulx r14, rcx, r9
seto r9b
mov [ rsp + 0x238 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r10, r10b
adox r10, r8
adox r11, [ rsp + 0x148 ]
mov r10, rdi
seto r8b
mov byte [ rsp + 0x240 ], r9b
mov r9, 0x0 
dec r9
movzx rbx, bl
adox rbx, r9
adox r10, r15
adcx r10, [ rsp + 0x210 ]
mov rbx, 0xffffffff 
mov [ rsp + 0x248 ], r10
mulx r10, r9, rbx
mov rbx, 0xffffffff00000000 
mov byte [ rsp + 0x250 ], r8b
mov [ rsp + 0x258 ], rax
mulx rax, r8, rbx
setc dl
clc
adcx r8, r10
seto r10b
mov rbx, -0x2 
inc rbx
adox r9, r13
adcx rcx, rax
adox r8, r11
mov r9, rdi
seto r13b
inc rbx
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox r9, r15
setc r15b
clc
movzx rdx, dl
adcx rdx, r11
adcx r9, [ rsp + 0x208 ]
adox rdi, rbx
adcx rdi, rbp
inc r11
mov rbx, -0x1 
movzx r15, r15b
adox r15, rbx
adox r14, r12
mov rbp, r12
adox rbp, [ rsp + 0x258 ]
seto r10b
mov rdx, -0x3 
inc rdx
adox r8, [ rsp + 0x138 ]
seto al
inc rbx
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox r12, [ rsp + 0x258 ]
mov r15, 0x100000001 
mov rdx, r8
mulx r10, r8, r15
mov r10, 0xffffffff00000000 
xchg rdx, r8
mulx r11, rbx, r10
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x260 ], r12
mulx r12, r10, r15
mov r15, 0xffffffff 
mov [ rsp + 0x268 ], rbp
mov [ rsp + 0x270 ], rdi
mulx rdi, rbp, r15
setc r15b
clc
adcx rbx, rdi
mov rdi, [ rsp + 0x258 ]
mov [ rsp + 0x278 ], rbx
mov rbx, 0x0 
adox rdi, rbx
mov rbx, [ rsp + 0x238 ]
mov [ rsp + 0x280 ], rbp
movzx rbp, byte [ rsp + 0x250 ]
mov [ rsp + 0x288 ], rdi
mov rdi, 0x0 
dec rdi
adox rbp, rdi
adox rbx, [ rsp + 0x170 ]
setc bpl
clc
movzx r13, r13b
adcx r13, rdi
adcx rbx, rcx
mov rcx, [ rsp + 0x248 ]
adox rcx, [ rsp + 0x168 ]
adox r9, [ rsp + 0x160 ]
adcx r14, rcx
mov r13, 0xfffffffffffffffe 
mulx rdi, rcx, r13
setc dl
clc
mov r13, -0x1 
movzx rbp, bpl
adcx rbp, r13
adcx r11, rcx
mov rbp, r10
adcx rbp, rdi
mov rcx, r10
adcx rcx, r12
adcx r10, r12
setc dil
clc
movzx rax, al
adcx rax, r13
adcx rbx, [ rsp + 0x158 ]
adcx r14, [ rsp + 0x180 ]
mov rax, [ rsp + 0x270 ]
adox rax, [ rsp + 0x178 ]
seto r13b
mov [ rsp + 0x290 ], r10
mov r10, 0x0 
dec r10
movzx rdx, dl
adox rdx, r10
adox r9, [ rsp + 0x268 ]
movzx rdx, r15b
movzx r10, byte [ rsp + 0x230 ]
lea rdx, [ rdx + r10 ]
adox rax, [ rsp + 0x260 ]
movzx r10, dil
lea r10, [ r10 + r12 ]
seto r15b
mov r12, 0x0 
dec r12
movzx r13, r13b
adox r13, r12
adox rdx, [ rsp + 0x1f0 ]
setc dil
clc
movzx r15, r15b
adcx r15, r12
adcx rdx, [ rsp + 0x288 ]
setc r13b
clc
adcx r8, [ rsp + 0x280 ]
adcx rbx, [ rsp + 0x278 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, r12
adcx r9, [ rsp + 0x1c8 ]
adcx rax, [ rsp + 0x1c0 ]
movzx rdi, r13b
mov r15, 0x0 
adox rdi, r15
dec r15
movzx r8, r8b
adox r8, r15
adox r14, r11
adcx rdx, [ rsp + 0x1e8 ]
adox rbp, r9
adcx rdi, [ rsp + 0x1e0 ]
setc r12b
clc
adcx rbx, [ rsp + 0x20 ]
mov r11, 0x100000001 
xchg rdx, rbx
mulx r8, r13, r11
adox rcx, rax
adcx r14, [ rsp + 0x50 ]
mov r8, 0xfffffffffffffffe 
xchg rdx, r8
mulx rax, r9, r13
adcx rbp, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0xd8 ]
adox rbx, [ rsp + 0x290 ]
mov r15, 0xffffffffffffffff 
mov rdx, r13
mulx r11, r13, r15
mov r15, 0xffffffff 
mov [ rsp + 0x298 ], r11
mov [ rsp + 0x2a0 ], rcx
mulx rcx, r11, r15
setc r15b
clc
adcx r11, r8
mov r11, 0xffffffff00000000 
mov [ rsp + 0x2a8 ], rbp
mulx rbp, r8, r11
adox r10, rdi
movzx rdi, r12b
mov rdx, 0x0 
adox rdi, rdx
mov r12, -0x3 
inc r12
adox r8, rcx
adox r9, rbp
setc cl
clc
mov rbp, -0x1 
movzx r15, r15b
adcx r15, rbp
adcx rbx, [ rsp + 0x128 ]
mov r15, r13
adox r15, rax
setc al
clc
movzx rcx, cl
adcx rcx, rbp
adcx r14, r8
adcx r9, [ rsp + 0x2a8 ]
setc cl
clc
adcx r14, [ rsp + 0x120 ]
setc r8b
clc
movzx rcx, cl
adcx rcx, rbp
adcx r15, [ rsp + 0x2a0 ]
mov rcx, 0x100000001 
mov rdx, r14
mulx rbp, r14, rcx
setc bpl
clc
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx r10, [ rsp + 0x1d8 ]
setc al
clc
movzx r8, r8b
adcx r8, r12
adcx r9, [ rsp + 0x130 ]
mov r8, r13
adox r8, [ rsp + 0x298 ]
adox r13, [ rsp + 0x298 ]
adcx r15, [ rsp + 0x1a8 ]
mov r12, 0xfffffffffffffffe 
xchg rdx, r12
mulx r11, rcx, r14
setc dl
clc
mov [ rsp + 0x2b0 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx rbx, r8
adcx r13, r10
mov rbp, 0xffffffff 
xchg rdx, r14
mulx r8, r10, rbp
setc r15b
clc
adcx r10, r12
mov r10, 0xffffffff00000000 
mulx rbp, r12, r10
setc r10b
clc
adcx r12, r8
mov r8, [ rsp + 0x298 ]
mov byte [ rsp + 0x2b8 ], r15b
mov r15, 0x0 
adox r8, r15
adcx rcx, rbp
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x2c0 ], r8
mulx r8, r15, rbp
mov rdx, r15
adcx rdx, r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox r9, r12
setc r10b
seto r12b
mov r11, r9
mov rbp, 0xffffffff 
sub r11, rbp
mov rbp, 0x0 
dec rbp
movzx r14, r14b
adox r14, rbp
adox rbx, [ rsp + 0x228 ]
adox r13, [ rsp + 0x218 ]
mov r14, r8
seto bpl
mov [ rsp + 0x2c8 ], r11
mov r11, 0x0 
dec r11
movzx r10, r10b
adox r10, r11
adox r14, r15
setc r10b
clc
movzx rax, al
adcx rax, r11
adcx rdi, [ rsp + 0x1d0 ]
adox r15, r8
seto al
inc r11
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox rcx, [ rsp + 0x2b0 ]
adox rdx, rbx
adox r14, r13
setc r12b
seto bl
movzx r13, r10b
add r13, -0x1
mov r10, rcx
mov r13, 0xffffffff00000000 
sbb r10, r13
movzx r11, byte [ rsp + 0x2b8 ]
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r11, r13
adox rdi, [ rsp + 0x2c0 ]
movzx r11, byte [ rsp + 0x240 ]
mov r13, [ rsp + 0x68 ]
lea r11, [ r11 + r13 ]
seto r13b
mov [ rsp + 0x2d0 ], r10
mov r10, rdx
mov [ rsp + 0x2d8 ], r14
mov r14, 0xfffffffffffffffe 
sbb r10, r14
movzx r14, r13b
movzx r12, r12b
lea r14, [ r14 + r12 ]
movzx r12, al
lea r12, [ r12 + r8 ]
mov r8, -0x1 
inc r8
mov rax, -0x1 
movzx rbp, bpl
adox rbp, rax
adox rdi, [ rsp + 0x220 ]
adox r11, r14
setc bpl
clc
movzx rbx, bl
adcx rbx, rax
adcx rdi, r15
adcx r12, r11
setc r15b
seto bl
movzx r13, bpl
add r13, -0x1
mov rbp, [ rsp + 0x2d8 ]
mov r13, 0xffffffffffffffff 
sbb rbp, r13
mov r14, rdi
sbb r14, r13
movzx r11, r15b
movzx rbx, bl
lea r11, [ r11 + rbx ]
mov rbx, r12
sbb rbx, r13
sbb r11, 0x00000000
mov r11, [ rsp + 0x2d0 ]
cmovc r11, rcx
cmovc rbp, [ rsp + 0x2d8 ]
cmovc r14, rdi
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x20 ], r14
cmovc r10, rdx
mov [ rcx + 0x8 ], r11
mov rdx, [ rsp + 0x2c8 ]
cmovc rdx, r9
cmovc rbx, r12
mov [ rcx + 0x28 ], rbx
mov [ rcx + 0x0 ], rdx
mov [ rcx + 0x18 ], rbp
mov [ rcx + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 864
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0115
; seed 4200472859088944 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 60939 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 1374 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.022547137301235663
; number reverted permutation / tried permutation: 328 / 517 =63.443%
; number reverted decision / tried decision: 256 / 482 =53.112%
; validated in 42.362s
