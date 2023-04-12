SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 864
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r9
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r8
mulx r8, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rdi
mulx rdi, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], r10
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r15
mulx r15, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], r10
mulx r10, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], rdi
mulx rdi, rcx, [ rsi + 0x28 ]
add r15, rbx
mov rdx, -0x2 
inc rdx
adox rbp, r11
mov rdx, [ rax + 0x18 ]
mulx rbx, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x68 ], r15
mov [ rsp + 0x70 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adcx r15, r10
adox r13, r12
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], rcx
mulx rcx, r15, [ rax + 0x0 ]
adox r9, r14
seto dl
mov r14, -0x2 
inc r14
adox r8, rcx
mov rcx, [ rsp + 0x58 ]
adox rcx, [ rsp + 0x60 ]
mov r14, 0x100000001 
mov [ rsp + 0x88 ], rcx
mov cl, dl
mov rdx, [ rsp + 0x30 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r15
mulx r15, r8, r14
mov r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], rbx
mulx rbx, r14, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r11
mulx r11, r14, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb8 ], r9
mov [ rsp + 0xc0 ], r13
mulx r13, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r13
mov [ rsp + 0xd0 ], rbp
mulx rbp, r13, [ rax + 0x18 ]
seto dl
mov [ rsp + 0xd8 ], rbp
mov rbp, -0x2 
inc rbp
adox r14, r15
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbp, r15, [ rax + 0x18 ]
seto dl
mov byte [ rsp + 0xe0 ], r14b
mov r14, -0x2 
inc r14
adox r9, rbx
mov bl, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xe8 ], r9
mulx r9, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf0 ], r9
mov [ rsp + 0xf8 ], r14
mulx r14, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x100 ], r9
mov byte [ rsp + 0x108 ], bl
mulx rbx, r9, [ rax + 0x20 ]
adcx r15, rdi
adcx r9, rbp
mov rdx, 0xffffffffffffffff 
mulx rbp, rdi, r8
adcx rbx, [ rsp + 0x28 ]
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0x110 ], rbx
mov rbx, 0x0 
adcx rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r9
mov [ rsp + 0x120 ], r15
mulx r15, r9, [ rax + 0x18 ]
mov rdx, [ rsp + 0x18 ]
clc
mov [ rsp + 0x128 ], rbx
mov rbx, -0x1 
movzx rcx, cl
adcx rcx, rbx
adcx rdx, [ rsp - 0x10 ]
mov rcx, [ rsp - 0x18 ]
adcx rcx, [ rsp + 0x40 ]
mov rbx, [ rsp + 0x38 ]
mov [ rsp + 0x130 ], rcx
mov rcx, 0x0 
adcx rbx, rcx
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x138 ], rbx
mov [ rsp + 0x140 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r15
mulx r15, rcx, [ rsi + 0x10 ]
clc
adcx rbx, [ rsp + 0x0 ]
setc dl
clc
adcx r12, r14
mov r14b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x158 ], rbx
mov [ rsp + 0x160 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
adcx r10, [ rsp + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rcx
mulx rcx, r10, r8
seto dl
mov [ rsp + 0x178 ], r9
mov r9, -0x2 
inc r9
adox r10, r11
adcx r13, [ rsp + 0x8 ]
mov r11b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x180 ], r13
mulx r13, r9, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x188 ], r15
movzx r15, byte [ rsp + 0x108 ]
mov [ rsp + 0x190 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r15, r12
adox r10, [ rsp + 0xd0 ]
seto r15b
movzx r12, byte [ rsp + 0xe0 ]
mov [ rsp + 0x198 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r12, rdi
adox r9, [ rsp - 0x40 ]
setc r12b
clc
movzx r14, r14b
adcx r14, rdi
adcx rbp, rbx
adox r13, [ rsp + 0x50 ]
mov r14, 0xfffffffffffffffe 
xchg rdx, r14
mulx rdi, rbx, r8
setc r8b
clc
adcx r10, [ rsp + 0x100 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1a0 ], r13
mov [ rsp + 0x1a8 ], r9
mulx r9, r13, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b0 ], rbp
mulx rbp, r9, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x48 ]
adox rdx, [ rsp - 0x20 ]
mov [ rsp + 0x1b8 ], rdx
seto dl
mov byte [ rsp + 0x1c0 ], r8b
mov r8, 0x0 
dec r8
movzx r14, r14b
adox r14, r8
adox rcx, rbx
seto r14b
inc r8
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r9, [ rsp + 0xc8 ]
setc r11b
clc
movzx r15, r15b
adcx r15, rbx
adcx rcx, [ rsp + 0xc0 ]
seto r15b
inc rbx
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rdi, [ rsp + 0x198 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r13
mulx r8, rbx, r14
mov r14, 0xfffffffffffffffe 
mov [ rsp + 0x1c8 ], r9
mov [ rsp + 0x1d0 ], r8
mulx r8, r9, r14
seto r14b
mov [ rsp + 0x1d8 ], rbx
mov rbx, 0x0 
dec rbx
movzx r11, r11b
adox r11, rbx
adox rcx, [ rsp + 0x190 ]
adcx rdi, [ rsp + 0xb8 ]
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1e0 ], rcx
mulx rcx, rbx, [ rax + 0x20 ]
movzx rdx, r13b
mov [ rsp + 0x1e8 ], r8
mov r8, [ rsp - 0x28 ]
lea rdx, [ rdx + r8 ]
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1f0 ], r9
mulx r9, r13, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x1f8 ], r8
mov r8, 0x0 
dec r8
movzx r15, r15b
adox r15, r8
adox rbp, [ rsp + 0xb0 ]
mov r15, [ rsp + 0xf8 ]
setc r8b
clc
mov [ rsp + 0x200 ], rbp
mov rbp, -0x1 
movzx r12, r12b
adcx r12, rbp
adcx r15, [ rsp + 0xd8 ]
mov r12, [ rsp + 0x188 ]
setc bpl
mov [ rsp + 0x208 ], r15
movzx r15, byte [ rsp + 0x1c0 ]
clc
mov byte [ rsp + 0x210 ], r8b
mov r8, -0x1 
adcx r15, r8
adcx r12, [ rsp + 0x178 ]
adox rbx, [ rsp + 0xa0 ]
adcx r13, [ rsp + 0x150 ]
adcx r9, [ rsp + 0x170 ]
adox rcx, [ rsp + 0x80 ]
mov r15, [ rsp + 0xf0 ]
setc r8b
clc
mov [ rsp + 0x218 ], rcx
mov rcx, -0x1 
movzx rbp, bpl
adcx rbp, rcx
adcx r15, [ rsp - 0x30 ]
movzx rbp, r8b
mov rcx, [ rsp + 0x160 ]
lea rbp, [ rbp + rcx ]
seto cl
mov r8, 0x0 
dec r8
movzx rdx, dl
adox rdx, r8
adox rdi, [ rsp + 0x168 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x220 ], rbx
mulx rbx, r8, r11
mov rdx, [ rsp + 0x198 ]
mov [ rsp + 0x228 ], rbp
mov rbp, rdx
mov [ rsp + 0x230 ], r9
seto r9b
mov [ rsp + 0x238 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox rbp, [ rsp + 0x140 ]
adox rdx, [ rsp + 0x140 ]
setc r14b
movzx r13, byte [ rsp + 0x210 ]
clc
mov [ rsp + 0x240 ], r12
mov r12, -0x1 
adcx r13, r12
adcx rbp, [ rsp + 0x148 ]
movzx r13, cl
mov r12, [ rsp + 0x70 ]
lea r13, [ r13 + r12 ]
mov r12, [ rsp + 0x140 ]
mov rcx, 0x0 
adox r12, rcx
mov rcx, 0xffffffff00000000 
xchg rdx, r11
mov [ rsp + 0x248 ], r13
mov byte [ rsp + 0x250 ], r14b
mulx r14, r13, rcx
mov rdx, -0x2 
inc rdx
adox r13, rbx
adox r14, [ rsp + 0x1f0 ]
mov rbx, [ rsp + 0x1e8 ]
adox rbx, [ rsp + 0x1d8 ]
adcx r11, [ rsp + 0x130 ]
mov rdx, [ rsp + 0x1d0 ]
mov rcx, rdx
adox rcx, [ rsp + 0x1d8 ]
mov [ rsp + 0x258 ], rcx
seto cl
mov [ rsp + 0x260 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r9, r9b
adox r9, rbx
adox rbp, [ rsp + 0x180 ]
seto r9b
inc rbx
adox r8, r10
seto r8b
dec rbx
movzx r9, r9b
adox r9, rbx
adox r11, [ rsp + 0x208 ]
seto r10b
inc rbx
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox r13, [ rsp + 0x1e0 ]
adox r14, rdi
seto dil
mov r8, -0x3 
inc r8
adox r13, [ rsp - 0x8 ]
adcx r12, [ rsp + 0x138 ]
setc bl
clc
movzx r10, r10b
adcx r10, r9
adcx r12, r15
adox r14, [ rsp + 0x158 ]
movzx r15, byte [ rsp + 0x250 ]
mov r10, [ rsp - 0x38 ]
lea r15, [ r15 + r10 ]
seto r10b
inc r9
mov r9, -0x1 
movzx rdi, dil
adox rdi, r9
adox rbp, [ rsp + 0x260 ]
movzx rdi, bl
adcx rdi, r15
mov rbx, rdx
setc r15b
clc
movzx rcx, cl
adcx rcx, r9
adcx rbx, [ rsp + 0x1d8 ]
adox r11, [ rsp + 0x258 ]
mov rcx, 0x100000001 
xchg rdx, rcx
mulx r8, r9, r13
mov r8, 0xffffffff00000000 
mov rdx, r8
mov [ rsp + 0x268 ], r14
mulx r14, r8, r9
mov rdx, 0xffffffff 
mov [ rsp + 0x270 ], r14
mov byte [ rsp + 0x278 ], r15b
mulx r15, r14, r9
adox rbx, r12
mov r12, 0x0 
adcx rcx, r12
adox rcx, rdi
clc
mov rdi, -0x1 
movzx r10, r10b
adcx r10, rdi
adcx rbp, [ rsp + 0x1b0 ]
adcx r11, [ rsp + 0x240 ]
seto r10b
mov rdi, -0x3 
inc rdi
adox r8, r15
movzx r15, r10b
movzx r12, byte [ rsp + 0x278 ]
lea r15, [ r15 + r12 ]
mov r12, 0xfffffffffffffffe 
mov rdx, r12
mulx r10, r12, r9
adox r12, [ rsp + 0x270 ]
setc dil
clc
adcx r14, r13
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx r13, r9, r14
mov rdx, r9
adox rdx, r10
adcx r8, [ rsp + 0x268 ]
mov r10, r9
adox r10, r13
adcx r12, rbp
adox r9, r13
mov rbp, 0x0 
adox r13, rbp
mov r14, -0x3 
inc r14
adox r8, [ rsp - 0x48 ]
mov rbp, 0x100000001 
xchg rdx, r8
mov [ rsp + 0x280 ], r13
mulx r13, r14, rbp
seto r13b
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rdi, dil
adox rdi, rbp
adox rbx, [ rsp + 0x238 ]
adox rcx, [ rsp + 0x230 ]
mov rdi, 0xfffffffffffffffe 
xchg rdx, rdi
mov [ rsp + 0x288 ], r12
mulx r12, rbp, r14
mov rdx, 0xffffffff 
mov [ rsp + 0x290 ], r12
mov [ rsp + 0x298 ], rbp
mulx rbp, r12, r14
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x2a0 ], r12
mov byte [ rsp + 0x2a8 ], r13b
mulx r13, r12, r14
setc dl
clc
adcx r12, rbp
seto bpl
mov [ rsp + 0x2b0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rdx, dl
adox rdx, r13
adox r11, r8
seto r8b
inc r13
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox r15, [ rsp + 0x228 ]
seto bpl
dec r13
movzx r8, r8b
adox r8, r13
adox rbx, r10
adox r9, rcx
mov rdx, [ rsp + 0x288 ]
setc r10b
movzx rcx, byte [ rsp + 0x2a8 ]
clc
adcx rcx, r13
adcx rdx, [ rsp + 0x68 ]
adox r15, [ rsp + 0x280 ]
movzx rcx, bpl
mov r8, 0x0 
adox rcx, r8
adcx r11, [ rsp + 0x78 ]
adcx rbx, [ rsp + 0x120 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mulx r13, r8, r14
adcx r9, [ rsp + 0x118 ]
adcx r15, [ rsp + 0x110 ]
mov r14, -0x2 
inc r14
adox rdi, [ rsp + 0x2a0 ]
adcx rcx, [ rsp + 0x128 ]
adox r12, rbp
mov rdi, [ rsp + 0x2b0 ]
setc bpl
clc
movzx r10, r10b
adcx r10, r14
adcx rdi, [ rsp + 0x298 ]
mov r10, r8
adcx r10, [ rsp + 0x290 ]
adox rdi, r11
mov r11, r8
adcx r11, r13
adox r10, rbx
adcx r8, r13
adox r11, r9
setc bl
clc
adcx r12, [ rsp + 0x98 ]
adcx rdi, [ rsp + 0x90 ]
adox r8, r15
movzx r9, bl
lea r9, [ r9 + r13 ]
mov r13, 0x100000001 
mov rdx, r13
mulx r15, r13, r12
adcx r10, [ rsp + 0x88 ]
mov r15, 0xffffffff 
mov rdx, r15
mulx rbx, r15, r13
adox r9, rcx
movzx rcx, bpl
mov r14, 0x0 
adox rcx, r14
adcx r11, [ rsp + 0x1a8 ]
adcx r8, [ rsp + 0x1a0 ]
adcx r9, [ rsp + 0x1b8 ]
adcx rcx, [ rsp + 0x1f8 ]
mov rbp, 0xffffffff00000000 
mov rdx, r13
mulx r14, r13, rbp
mov rbp, -0x2 
inc rbp
adox r13, rbx
mov rbx, 0xfffffffffffffffe 
mov [ rsp + 0x2b8 ], rcx
mulx rcx, rbp, rbx
setc bl
clc
adcx r15, r12
adcx r13, rdi
adox rbp, r14
mov r15, 0xffffffffffffffff 
mulx rdi, r12, r15
mov rdx, r12
adox rdx, rcx
adcx rbp, r10
mov r10, r12
adox r10, rdi
adcx rdx, r11
adcx r10, r8
adox r12, rdi
seto r11b
mov r8, -0x2 
inc r8
adox r13, [ rsp + 0xa8 ]
mov r14, 0x100000001 
xchg rdx, r13
mulx r8, rcx, r14
mov r8, 0xffffffff 
xchg rdx, rcx
mulx r15, r14, r8
adcx r12, r9
adox rbp, [ rsp + 0xe8 ]
adox r13, [ rsp + 0x1c8 ]
adox r10, [ rsp + 0x200 ]
mov r9, 0xffffffff00000000 
mov [ rsp + 0x2c0 ], r10
mulx r10, r8, r9
movzx r9, r11b
lea r9, [ r9 + rdi ]
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x2c8 ], r13
mulx r13, r11, rdi
adcx r9, [ rsp + 0x2b8 ]
adox r12, [ rsp + 0x220 ]
movzx rdi, bl
mov [ rsp + 0x2d0 ], r12
mov r12, 0x0 
adcx rdi, r12
adox r9, [ rsp + 0x218 ]
adox rdi, [ rsp + 0x248 ]
clc
adcx r8, r15
mov rbx, 0xffffffffffffffff 
mulx r12, r15, rbx
adcx r11, r10
seto dl
mov r10, -0x2 
inc r10
adox r14, rcx
adox r8, rbp
setc r14b
seto cl
mov rbp, r8
mov r10, 0xffffffff 
sub rbp, r10
mov r10, 0x0 
dec r10
movzx r14, r14b
adox r14, r10
adox r13, r15
mov r14, r15
adox r14, r12
adox r15, r12
mov r10, 0x0 
adox r12, r10
dec r10
movzx rcx, cl
adox rcx, r10
adox r11, [ rsp + 0x2c8 ]
seto cl
mov r10, r11
mov rbx, 0xffffffff00000000 
sbb r10, rbx
mov rbx, 0x0 
dec rbx
movzx rcx, cl
adox rcx, rbx
adox r13, [ rsp + 0x2c0 ]
adox r14, [ rsp + 0x2d0 ]
adox r15, r9
adox r12, rdi
seto r9b
mov rdi, r13
mov rcx, 0xfffffffffffffffe 
sbb rdi, rcx
mov rbx, r14
mov rcx, 0xffffffffffffffff 
sbb rbx, rcx
mov [ rsp + 0x2d8 ], rbx
mov rbx, r15
sbb rbx, rcx
movzx rcx, r9b
movzx rdx, dl
lea rcx, [ rcx + rdx ]
mov rdx, r12
mov r9, 0xffffffffffffffff 
sbb rdx, r9
sbb rcx, 0x00000000
cmovc r10, r11
cmovc rbx, r15
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r10
cmovc rbp, r8
cmovc rdx, r12
cmovc rdi, r13
mov r8, [ rsp + 0x2d8 ]
cmovc r8, r14
mov [ rcx + 0x28 ], rdx
mov [ rcx + 0x18 ], r8
mov [ rcx + 0x20 ], rbx
mov [ rcx + 0x0 ], rbp
mov [ rcx + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 864
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0547
; seed 0459603057367015 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 60577 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 1501 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02477838123380161
; number reverted permutation / tried permutation: 302 / 527 =57.306%
; number reverted decision / tried decision: 205 / 472 =43.432%
; validated in 46.388s
