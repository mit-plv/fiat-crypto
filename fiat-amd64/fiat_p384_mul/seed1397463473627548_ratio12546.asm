SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 880
mov rax, rdx
mov rdx, [ rdx + 0x28 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r11
mulx r11, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], rbp
mulx rbp, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rbp
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r11
mulx r11, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r14
mulx r14, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], rdi
mov [ rsp + 0x50 ], r14
mulx r14, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r14
mulx r14, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
adox rcx, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], rbx
mulx rbx, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r13
mulx r13, rbx, [ rsi + 0x28 ]
adox r8, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r8
mulx r8, r10, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], rbx
mulx rbx, r13, [ rax + 0x8 ]
adcx r12, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r12
mulx r12, rdi, [ rax + 0x10 ]
adcx rdi, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], r10
mulx r10, r8, [ rsi + 0x10 ]
adcx r8, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r8
mulx r8, r12, [ rax + 0x0 ]
adox r15, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe8 ], r12
mulx r12, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], rcx
mov [ rsp + 0xf8 ], r15
mulx r15, rcx, [ rax + 0x28 ]
setc dl
clc
adcx r13, rdi
adcx rbp, rbx
adcx r9, r11
mov r11, [ rsp + 0x90 ]
adcx r11, [ rsp + 0x88 ]
setc bl
clc
adcx r12, [ rsp + 0x78 ]
mov rdi, 0x100000001 
xchg rdx, r14
mov [ rsp + 0x100 ], r12
mov [ rsp + 0x108 ], r11
mulx r11, r12, rdi
mov r11, 0xfffffffffffffffe 
xchg rdx, r12
mov [ rsp + 0x110 ], r9
mulx r9, rdi, r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r13
mulx r13, rbp, [ rax + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x128 ], r9
mov [ rsp + 0x130 ], rdi
mulx rdi, r9, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x138 ], rdi
mov [ rsp + 0x140 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r9
mulx r9, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x158 ], r9
mov [ rsp + 0x160 ], r8
mulx r8, r9, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x168 ], r15
mov r15, -0x2 
inc r15
adox rbp, [ rsp + 0x50 ]
mov r15b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], rbp
mov byte [ rsp + 0x178 ], bl
mulx rbx, rbp, [ rax + 0x28 ]
adox r13, [ rsp + 0xa0 ]
seto dl
mov [ rsp + 0x180 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox r10, r9
adox rcx, r8
seto r14b
inc r13
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox rdi, [ rsp + 0x98 ]
setc r8b
clc
movzx r15, r15b
adcx r15, r9
adcx rbp, [ rsp + 0x30 ]
mov r15, [ rsp + 0xd8 ]
setc dl
movzx r13, byte [ rsp + 0x178 ]
clc
adcx r13, r9
adcx r15, [ rsp + 0x28 ]
mov r13, 0xffffffff00000000 
xchg rdx, r11
mov [ rsp + 0x188 ], rdi
mulx rdi, r9, r13
mov r13, [ rsp + 0xd0 ]
mov [ rsp + 0x190 ], rcx
mov rcx, 0x0 
adcx r13, rcx
mov rcx, [ rsp + 0xb8 ]
adox rcx, [ rsp + 0x168 ]
mov [ rsp + 0x198 ], rcx
mov rcx, [ rsp + 0x20 ]
clc
adcx rcx, [ rsp + 0x160 ]
mov [ rsp + 0x1a0 ], rcx
seto cl
mov [ rsp + 0x1a8 ], r10
mov r10, -0x2 
inc r10
adox r12, [ rsp + 0x150 ]
movzx r12, r14b
mov r10, [ rsp + 0x158 ]
lea r12, [ r12 + r10 ]
mov r10, [ rsp + 0xb0 ]
seto r14b
mov [ rsp + 0x1b0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox r10, [ rsp + 0x0 ]
mov rcx, [ rsp - 0x8 ]
adcx rcx, [ rsp + 0x60 ]
mov r12, [ rsp + 0x18 ]
mov [ rsp + 0x1b8 ], r10
seto r10b
mov [ rsp + 0x1c0 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox r12, [ rsp - 0x20 ]
mov r8, [ rsp - 0x28 ]
adox r8, [ rsp + 0x40 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1c8 ], r8
mov [ rsp + 0x1d0 ], r12
mulx r12, r8, [ rax + 0x18 ]
movzx rdx, r11b
lea rdx, [ rdx + rbx ]
adcx r8, [ rsp + 0x58 ]
mov rbx, [ rsp - 0x10 ]
adox rbx, [ rsp + 0x38 ]
adcx r12, [ rsp - 0x30 ]
mov r11, [ rsp + 0x10 ]
adcx r11, [ rsp - 0x38 ]
mov [ rsp + 0x1d8 ], rbx
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x1e0 ], r11
mov [ rsp + 0x1e8 ], r12
mulx r12, r11, rcx
mov rcx, [ rsp + 0x8 ]
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsp - 0x18 ]
adox rdx, [ rsp + 0x148 ]
mov [ rsp + 0x1f0 ], rdx
movzx rdx, r10b
mov [ rsp + 0x1f8 ], rcx
mov rcx, [ rsp - 0x40 ]
lea rdx, [ rdx + rcx ]
mov rcx, [ rsp + 0x140 ]
mov r10, 0x0 
adox rcx, r10
test al, al
adox r9, [ rsp + 0x138 ]
adox rdi, [ rsp + 0x130 ]
mov r10, r11
adox r10, [ rsp + 0x128 ]
mov [ rsp + 0x200 ], rdx
mov rdx, r11
adox rdx, r12
adox r11, r12
mov [ rsp + 0x208 ], rcx
mov rcx, -0x1 
movzx r14, r14b
adcx r14, rcx
adcx r9, [ rsp + 0x120 ]
seto r14b
inc rcx
adox r9, [ rsp - 0x48 ]
adcx rdi, [ rsp + 0x118 ]
adcx r10, [ rsp + 0x110 ]
adcx rdx, [ rsp + 0x108 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mov [ rsp + 0x210 ], r8
mov [ rsp + 0x218 ], rbx
mulx rbx, r8, r9
mov rbx, 0xffffffff 
mov rdx, rbx
mov [ rsp + 0x220 ], rbp
mulx rbp, rbx, r8
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x228 ], rcx
mov [ rsp + 0x230 ], r10
mulx r10, rcx, r8
movzx rdx, r14b
lea rdx, [ rdx + r12 ]
seto r12b
mov r14, -0x2 
inc r14
adox rcx, rbp
adcx r11, r15
seto r15b
inc r14
mov rbp, -0x1 
movzx r12, r12b
adox r12, rbp
adox rdi, [ rsp + 0x70 ]
adcx rdx, r13
setc r13b
clc
adcx rbx, r9
mov rbx, [ rsp + 0x230 ]
adox rbx, [ rsp + 0x80 ]
mov r9, [ rsp + 0xa8 ]
adox r9, [ rsp + 0x228 ]
adox r11, [ rsp + 0xf8 ]
adcx rcx, rdi
setc r12b
clc
adcx rcx, [ rsp + 0x68 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx rbp, r14, rcx
mov rbp, 0xfffffffffffffffe 
mov rdx, rbp
mov [ rsp + 0x238 ], r11
mulx r11, rbp, r14
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x240 ], r9
mov [ rsp + 0x248 ], rbx
mulx rbx, r9, r14
adox rdi, [ rsp + 0x220 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x250 ], rdi
mov byte [ rsp + 0x258 ], r12b
mulx r12, rdi, r14
setc dl
clc
adcx r9, r12
movzx r13, r13b
movzx r12, r13b
adox r12, [ rsp + 0x218 ]
seto r13b
mov [ rsp + 0x260 ], r12
mov r12, -0x2 
inc r12
adox rdi, rcx
mov rdi, 0xfffffffffffffffe 
xchg rdx, r8
mulx r12, rcx, rdi
mov rdi, 0xffffffffffffffff 
xchg rdx, r14
mov byte [ rsp + 0x268 ], r13b
mov [ rsp + 0x270 ], r9
mulx r9, r13, rdi
adcx rbp, rbx
mov rdx, r13
adcx rdx, r11
seto r11b
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r15, r15b
adox r15, rbx
adox r10, rcx
mov r15, r13
adcx r15, r9
adcx r13, r9
mov rcx, 0x0 
adcx r9, rcx
xchg rdx, r14
mulx rbx, rcx, rdi
movzx rdx, byte [ rsp + 0x258 ]
clc
mov rdi, -0x1 
adcx rdx, rdi
adcx r10, [ rsp + 0x248 ]
mov rdx, rcx
adox rdx, r12
seto r12b
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox r10, [ rsp + 0xc0 ]
adcx rdx, [ rsp + 0x240 ]
adox rdx, [ rsp + 0xc8 ]
mov r8, rbx
seto dil
mov [ rsp + 0x278 ], r9
mov r9, 0x0 
dec r9
movzx r12, r12b
adox r12, r9
adox r8, rcx
adox rcx, rbx
adcx r8, [ rsp + 0x238 ]
mov r12, 0x0 
adox rbx, r12
inc r9
mov r12, -0x1 
movzx rdi, dil
adox rdi, r12
adox r8, [ rsp + 0xe0 ]
seto dil
dec r9
movzx r11, r11b
adox r11, r9
adox r10, [ rsp + 0x270 ]
adcx rcx, [ rsp + 0x250 ]
adox rbp, rdx
adcx rbx, [ rsp + 0x260 ]
setc r12b
clc
movzx rdi, dil
adcx rdi, r9
adcx rcx, [ rsp + 0x1a8 ]
movzx r11, r12b
movzx rdx, byte [ rsp + 0x268 ]
lea r11, [ r11 + rdx ]
adcx rbx, [ rsp + 0x190 ]
adcx r11, [ rsp + 0x1b0 ]
adox r14, r8
adox r15, rcx
adox r13, rbx
adox r11, [ rsp + 0x278 ]
setc dl
clc
adcx r10, [ rsp + 0xe8 ]
adcx rbp, [ rsp + 0x1a0 ]
adcx r14, [ rsp + 0x1c0 ]
movzx r8, dl
mov rdi, 0x0 
adox r8, rdi
adcx r15, [ rsp + 0x210 ]
mov r12, 0x100000001 
mov rdx, r12
mulx rcx, r12, r10
mov rcx, 0xffffffff 
mov rdx, rcx
mulx rbx, rcx, r12
mov rdi, 0xffffffff00000000 
mov rdx, rdi
mulx r9, rdi, r12
mov rdx, -0x2 
inc rdx
adox rdi, rbx
adcx r13, [ rsp + 0x1e8 ]
mov rbx, 0xfffffffffffffffe 
mov rdx, rbx
mov [ rsp + 0x280 ], r13
mulx r13, rbx, r12
adox rbx, r9
adcx r11, [ rsp + 0x1e0 ]
adcx r8, [ rsp + 0x1f8 ]
seto r9b
mov rdx, -0x2 
inc rdx
adox rcx, r10
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r10, rcx, r12
adox rdi, rbp
setc bpl
clc
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx r13, rcx
mov r9, rcx
adcx r9, r10
adcx rcx, r10
adox rbx, r14
adox r13, r15
adox r9, [ rsp + 0x280 ]
adox rcx, r11
setc r14b
clc
adcx rdi, [ rsp + 0xf0 ]
mov r15, 0x100000001 
mov rdx, r15
mulx r11, r15, rdi
adcx rbx, [ rsp + 0x100 ]
adcx r13, [ rsp + 0x1d0 ]
mov r11, 0xffffffff 
mov rdx, r15
mulx r12, r15, r11
mov r11, 0xffffffff00000000 
mov byte [ rsp + 0x288 ], bpl
mov [ rsp + 0x290 ], r8
mulx r8, rbp, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x298 ], r13
mov [ rsp + 0x2a0 ], rbx
mulx rbx, r13, r11
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x2a8 ], rbx
mov [ rsp + 0x2b0 ], r15
mulx r15, rbx, r11
adcx r9, [ rsp + 0x1c8 ]
adcx rcx, [ rsp + 0x1d8 ]
movzx rdx, r14b
lea rdx, [ rdx + r10 ]
seto r10b
mov r14, -0x2 
inc r14
adox rbp, r12
adox rbx, r8
mov r12, r13
adox r12, r15
seto r8b
inc r14
adox rdi, [ rsp + 0x2b0 ]
adox rbp, [ rsp + 0x2a0 ]
adox rbx, [ rsp + 0x298 ]
adox r12, r9
seto dil
dec r14
movzx r10, r10b
adox r10, r14
adox rdx, [ rsp + 0x290 ]
adcx rdx, [ rsp + 0x1f0 ]
seto r10b
inc r14
adox rbp, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x170 ]
movzx r15, r10b
movzx r9, byte [ rsp + 0x288 ]
lea r15, [ r15 + r9 ]
adox r12, [ rsp + 0x180 ]
adcx r15, [ rsp + 0x208 ]
mov r9, r13
setc r10b
clc
mov r14, -0x1 
movzx r8, r8b
adcx r8, r14
adcx r9, [ rsp + 0x2a8 ]
adcx r13, [ rsp + 0x2a8 ]
mov r8, 0x100000001 
xchg rdx, r8
mulx r11, r14, rbp
mov r11, 0xffffffff 
mov rdx, r14
mov byte [ rsp + 0x2b8 ], r10b
mulx r10, r14, r11
seto r11b
mov [ rsp + 0x2c0 ], r15
mov r15, 0x0 
dec r15
movzx rdi, dil
adox rdi, r15
adox rcx, r9
setc dil
clc
movzx r11, r11b
adcx r11, r15
adcx rcx, [ rsp + 0x188 ]
mov r11, 0xffffffff00000000 
mulx r15, r9, r11
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x2c8 ], rcx
mov [ rsp + 0x2d0 ], r13
mulx r13, rcx, r11
seto r11b
mov [ rsp + 0x2d8 ], r13
mov r13, -0x2 
inc r13
adox r9, r10
adox rcx, r15
setc r10b
clc
adcx r14, rbp
adcx r9, rbx
adcx rcx, r12
setc r14b
seto bpl
mov rbx, r9
mov r12, 0xffffffff 
sub rbx, r12
movzx r15, dil
mov r13, [ rsp + 0x2a8 ]
lea r15, [ r15 + r13 ]
mov r13, rcx
mov rdi, 0xffffffff00000000 
sbb r13, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x2e0 ], r13
mulx r13, r12, rdi
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox r8, [ rsp + 0x2d0 ]
seto r11b
inc rdx
mov rdx, -0x1 
movzx r10, r10b
adox r10, rdx
adox r8, [ rsp + 0x198 ]
mov r10, r12
setc dl
clc
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r10, [ rsp + 0x2d8 ]
mov rbp, r12
adcx rbp, r13
seto dil
mov [ rsp + 0x2e8 ], rbx
mov rbx, 0x0 
dec rbx
movzx r14, r14b
adox r14, rbx
adox r10, [ rsp + 0x2c8 ]
adox rbp, r8
adcx r12, r13
mov r14, 0x0 
adcx r13, r14
seto r8b
movzx r14, dl
add r14, -0x1
mov rdx, r10
mov r14, 0xfffffffffffffffe 
sbb rdx, r14
mov rbx, rbp
mov r14, 0xffffffffffffffff 
sbb rbx, r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox r15, [ rsp + 0x2c0 ]
setc r11b
clc
movzx rdi, dil
adcx rdi, r14
adcx r15, [ rsp + 0x1b8 ]
seto dil
inc r14
mov r14, -0x1 
movzx r8, r8b
adox r8, r14
adox r15, r12
movzx r8, dil
movzx r12, byte [ rsp + 0x2b8 ]
lea r8, [ r8 + r12 ]
adcx r8, [ rsp + 0x200 ]
setc r12b
seto dil
movzx r14, r11b
add r14, -0x1
mov r11, r15
mov r14, 0xffffffffffffffff 
sbb r11, r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox r8, r13
movzx r13, r12b
mov rdi, 0x0 
adox r13, rdi
mov r12, r8
mov rdi, 0xffffffffffffffff 
sbb r12, rdi
sbb r13, 0x00000000
mov r13, [ rsp + 0x2e8 ]
cmovc r13, r9
cmovc r11, r15
cmovc rbx, rbp
cmovc rdx, r10
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x20 ], r11
mov [ r9 + 0x0 ], r13
cmovc r12, r8
mov [ r9 + 0x28 ], r12
mov r10, [ rsp + 0x2e0 ]
cmovc r10, rcx
mov [ r9 + 0x10 ], rdx
mov [ r9 + 0x8 ], r10
mov [ r9 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 880
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2546
; seed 1397463473627548 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 26124 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=83, initial num_batches=31): 736 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.028173327208696985
; number reverted permutation / tried permutation: 307 / 505 =60.792%
; number reverted decision / tried decision: 306 / 494 =61.943%
; validated in 21.961s
