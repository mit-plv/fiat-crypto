SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 840
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r14
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], rdi
mulx rdi, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r13
mulx r13, r14, [ rax + 0x18 ]
add r15, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], r15
mulx r15, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], r13
mulx r13, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x40 ], rcx
mov [ rsp + 0x48 ], r14
mulx r14, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], rcx
mulx rcx, r14, [ rsi + 0x8 ]
mov rdx, 0x100000001 
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], r12
mulx r12, rcx, r9
mov r12, -0x2 
inc r12
adox r14, rdi
mov rdx, [ rax + 0x8 ]
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x70 ], r14
mov [ rsp + 0x78 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r12
mov [ rsp + 0x88 ], rdi
mulx rdi, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r12
mulx r12, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], r14
mulx r14, rcx, [ rsi + 0x28 ]
setc dl
clc
adcx r8, r13
adcx rdi, r15
mov r15b, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb0 ], rcx
mulx rcx, r13, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0xb8 ], r13
mov r13, -0x2 
inc r13
adox r10, r14
adcx rbx, r12
mov r12b, dl
mov rdx, [ rax + 0x10 ]
mulx r13, r14, [ rsi + 0x8 ]
adox rbp, r11
mov rdx, [ rsp + 0x68 ]
adox rdx, [ rsp + 0x48 ]
seto r11b
mov [ rsp + 0xc0 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r12, r12b
adox r12, rdx
adox r14, [ rsp + 0x60 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xc8 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], r10
mov [ rsp + 0xd8 ], r14
mulx r14, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
adox rbx, r13
adox rdi, [ rsp + 0x40 ]
setc dl
clc
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx r10, [ rsp + 0x38 ]
adcx r14, [ rsp + 0x30 ]
mov r11b, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf0 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x10 ]
adox rdx, [ rsp + 0x10 ]
mov [ rsp + 0xf8 ], r10
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
setc dl
clc
adcx r14, [ rsp + 0xa8 ]
adcx r13, [ rsp + 0xa0 ]
mov byte [ rsp + 0x110 ], dl
mov rdx, [ rsp + 0x58 ]
mov [ rsp + 0x118 ], r13
setc r13b
clc
mov [ rsp + 0x120 ], r14
mov r14, -0x1 
movzx r15, r15b
adcx r15, r14
adcx rdx, [ rsp - 0x20 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x128 ], r10
mulx r10, r14, [ rax + 0x28 ]
mov rdx, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x18 ]
adcx r14, rbp
mov rbp, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x130 ], r14
mov [ rsp + 0x138 ], r12
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r10, rdx
clc
adcx rcx, [ rsp + 0x88 ]
seto dl
mov [ rsp + 0x140 ], r10
mov r10, 0x0 
dec r10
movzx r13, r13b
adox r13, r10
adox rdi, [ rsp - 0x28 ]
adox r14, [ rsp - 0x30 ]
mov r13b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x148 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], rcx
mulx rcx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], rdi
mulx rdi, r14, [ rax + 0x20 ]
adcx r10, [ rsp + 0x80 ]
adcx rbp, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], rbp
mov [ rsp + 0x178 ], r10
mulx r10, rbp, [ rax + 0x28 ]
mov rdx, 0xffffffff 
mov byte [ rsp + 0x180 ], r13b
mov [ rsp + 0x188 ], rcx
mulx rcx, r13, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x190 ], rbx
mov [ rsp + 0x198 ], r8
mulx r8, rbx, [ rax + 0x28 ]
adcx r14, [ rsp + 0x90 ]
adcx rbp, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1a0 ], rbp
mulx rbp, rdi, [ rsp + 0x78 ]
mov rdx, 0x0 
adcx r10, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1a8 ], r10
mov [ rsp + 0x1b0 ], r14
mulx r14, r10, [ rsp + 0x78 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1b8 ], r14
mov [ rsp + 0x1c0 ], r10
mulx r10, r14, [ rsp + 0x78 ]
adox rbx, r12
mov r12, 0x0 
adox r8, r12
add rdi, rcx
dec r12
movzx r11, r11b
adox r11, r12
adox r15, [ rsp - 0x38 ]
seto r11b
inc r12
adox r13, r9
adcx r14, rbp
adox rdi, [ rsp + 0x198 ]
adcx r10, [ rsp + 0x1c0 ]
mov r13, [ rsp + 0x1b8 ]
mov r9, r13
adcx r9, [ rsp + 0x1c0 ]
adox r14, [ rsp + 0xe8 ]
adox r10, [ rsp + 0xe0 ]
adox r9, r15
seto cl
mov rbp, -0x3 
inc rbp
adox rdi, [ rsp - 0x18 ]
mov r15, r13
adcx r15, [ rsp + 0x1c0 ]
mov r12, 0x100000001 
mov rdx, r12
mulx rbp, r12, rdi
adox r14, [ rsp + 0x70 ]
adox r10, [ rsp + 0xd8 ]
mov rbp, 0x0 
adcx r13, rbp
adox r9, [ rsp + 0x190 ]
mov rbp, [ rsp + 0x188 ]
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rbp, [ rsp + 0x0 ]
setc r11b
clc
movzx rcx, cl
adcx rcx, rdx
adcx rbp, r15
movzx rcx, r11b
mov r15, [ rsp - 0x8 ]
lea rcx, [ rcx + r15 ]
adcx r13, rcx
adox rbp, [ rsp + 0x108 ]
mov r15, 0xffffffff 
mov rdx, r12
mulx r11, r12, r15
mov rcx, 0xffffffff00000000 
mov [ rsp + 0x1c8 ], r8
mulx r8, r15, rcx
seto cl
mov [ rsp + 0x1d0 ], rbx
mov rbx, -0x2 
inc rbx
adox r15, r11
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x1d8 ], rbp
mulx rbp, rbx, r11
setc r11b
clc
adcx r12, rdi
adcx r15, r14
adox rbx, r8
seto r12b
mov rdi, -0x1 
inc rdi
mov r14, -0x1 
movzx rcx, cl
adox rcx, r14
adox r13, [ rsp + 0x128 ]
seto cl
mov r8, -0x3 
inc r8
adox r15, [ rsp + 0x100 ]
movzx rdi, byte [ rsp + 0x180 ]
mov r8, [ rsp + 0x8 ]
lea rdi, [ rdi + r8 ]
adcx rbx, r10
mov r8, 0xffffffffffffffff 
mulx r14, r10, r8
adox rbx, [ rsp + 0x120 ]
setc dl
clc
mov r8, -0x1 
movzx r12, r12b
adcx r12, r8
adcx rbp, r10
mov r12, r10
adcx r12, r14
setc r8b
clc
mov [ rsp + 0x1e0 ], rbx
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx r9, rbp
adox r9, [ rsp + 0x118 ]
adcx r12, [ rsp + 0x1d8 ]
adox r12, [ rsp + 0x168 ]
mov rdx, 0x100000001 
mulx rbx, rbp, r15
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mov [ rsp + 0x1e8 ], r12
mulx r12, rbx, rbp
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x1f0 ], r9
mov [ rsp + 0x1f8 ], r12
mulx r12, r9, rbp
mov rdx, r14
mov [ rsp + 0x200 ], rbx
seto bl
mov [ rsp + 0x208 ], r12
mov r12, 0x0 
dec r12
movzx r8, r8b
adox r8, r12
adox rdx, r10
adcx rdx, r13
mov r13, 0xffffffff 
xchg rdx, rbp
mulx r8, r10, r13
mov r12, 0x0 
adox r14, r12
mov r12, 0xffffffff00000000 
mov [ rsp + 0x210 ], r10
mulx r10, r13, r12
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r11, r11b
movzx rcx, cl
adox rcx, rdx
adox rdi, r11
setc r11b
clc
adcx r13, r8
adcx r9, r10
seto cl
inc rdx
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox rbp, [ rsp + 0x160 ]
setc bl
clc
movzx r11, r11b
adcx r11, r8
adcx rdi, r14
adox rdi, [ rsp + 0x1d0 ]
movzx r11, cl
adcx r11, rdx
clc
adcx r15, [ rsp + 0x210 ]
adcx r13, [ rsp + 0x1e0 ]
mov r15, [ rsp + 0x208 ]
seto r14b
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r15, [ rsp + 0x200 ]
mov r8, [ rsp + 0x1f8 ]
mov r10, r8
adox r10, [ rsp + 0x200 ]
adcx r9, [ rsp + 0x1f0 ]
seto cl
inc rdx
adox r13, [ rsp + 0xb8 ]
adox r9, [ rsp + 0x158 ]
adcx r15, [ rsp + 0x1e8 ]
adox r15, [ rsp + 0x178 ]
adcx r10, rbp
setc bl
clc
mov rbp, -0x1 
movzx r14, r14b
adcx r14, rbp
adcx r11, [ rsp + 0x1c8 ]
mov r14, 0x100000001 
mov rdx, r14
mulx rbp, r14, r13
mov rbp, 0xffffffffffffffff 
mov rdx, r14
mulx r12, r14, rbp
adox r10, [ rsp + 0x170 ]
mov rbp, 0xffffffff00000000 
mov [ rsp + 0x218 ], r10
mov [ rsp + 0x220 ], r15
mulx r15, r10, rbp
mov rbp, 0xffffffff 
mov [ rsp + 0x228 ], r9
mov [ rsp + 0x230 ], r12
mulx r12, r9, rbp
setc bpl
clc
adcx r10, r12
mov r12, 0xfffffffffffffffe 
mov byte [ rsp + 0x238 ], bpl
mov [ rsp + 0x240 ], r10
mulx r10, rbp, r12
adcx rbp, r15
mov rdx, r8
setc r15b
clc
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx rdx, [ rsp + 0x200 ]
seto cl
inc r12
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rdi, rdx
seto bl
inc r12
mov rdx, -0x1 
movzx rcx, cl
adox rcx, rdx
adox rdi, [ rsp + 0x1b0 ]
adcx r8, r12
clc
movzx r15, r15b
adcx r15, rdx
adcx r10, r14
seto cl
inc rdx
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox r11, r8
mov r15, r14
adcx r15, [ rsp + 0x230 ]
adcx r14, [ rsp + 0x230 ]
seto bl
mov r8, -0x3 
inc r8
adox r9, r13
mov r9, [ rsp + 0x230 ]
adcx r9, rdx
mov r13, [ rsp + 0x240 ]
adox r13, [ rsp + 0x228 ]
clc
adcx r13, [ rsp - 0x40 ]
mov rdx, 0x100000001 
mulx r12, r8, r13
adox rbp, [ rsp + 0x220 ]
adox r10, [ rsp + 0x218 ]
mov r12, 0xffffffff00000000 
mov rdx, r12
mov [ rsp + 0x248 ], r9
mulx r9, r12, r8
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x250 ], r9
mov [ rsp + 0x258 ], r14
mulx r14, r9, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x260 ], r14
mov [ rsp + 0x268 ], r9
mulx r9, r14, r8
adcx rbp, [ rsp + 0x28 ]
adox r15, rdi
movzx rdi, bl
movzx rdx, byte [ rsp + 0x238 ]
lea rdi, [ rdi + rdx ]
mov rdx, 0xffffffff 
mov [ rsp + 0x270 ], r9
mulx r9, rbx, r8
seto r8b
mov rdx, -0x2 
inc rdx
adox rbx, r13
seto bl
inc rdx
mov r13, -0x1 
movzx rcx, cl
adox rcx, r13
adox r11, [ rsp + 0x1a0 ]
adox rdi, [ rsp + 0x1a8 ]
seto cl
mov r13, -0x3 
inc r13
adox r12, r9
seto r9b
dec rdx
movzx rbx, bl
adox rbx, rdx
adox rbp, r12
adcx r10, [ rsp + 0x150 ]
adcx r15, [ rsp + 0x148 ]
seto bl
inc rdx
mov r12, -0x1 
movzx r8, r8b
adox r8, r12
adox r11, [ rsp + 0x258 ]
adox rdi, [ rsp + 0x248 ]
adcx r11, [ rsp + 0x138 ]
adcx rdi, [ rsp + 0x130 ]
mov r8, [ rsp + 0x250 ]
setc dl
clc
movzx r9, r9b
adcx r9, r12
adcx r8, [ rsp + 0x268 ]
setc r9b
clc
adcx rbp, [ rsp + 0xb0 ]
mov r12, 0x100000001 
xchg rdx, rbp
mov [ rsp + 0x278 ], rdi
mulx rdi, r13, r12
movzx rdi, cl
mov r12, 0x0 
adox rdi, r12
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x280 ], r11
mulx r11, r12, r13
mov rdx, 0x0 
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox rdi, [ rsp + 0x140 ]
mov rbp, 0xfffffffffffffffe 
mov rdx, rbp
mov [ rsp + 0x288 ], r11
mulx r11, rbp, r13
mov rdx, r14
mov [ rsp + 0x290 ], rdi
seto dil
mov [ rsp + 0x298 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox rdx, [ rsp + 0x260 ]
mov r9, 0xffffffff00000000 
xchg rdx, r9
mov byte [ rsp + 0x2a0 ], dil
mulx rdi, r12, r13
mov rdx, 0xffffffff 
mov [ rsp + 0x2a8 ], r11
mov [ rsp + 0x2b0 ], rbp
mulx rbp, r11, r13
mov r13, r14
adox r13, [ rsp + 0x270 ]
adox r14, [ rsp + 0x270 ]
setc dl
clc
mov [ rsp + 0x2b8 ], rdi
mov rdi, -0x1 
movzx rbx, bl
adcx rbx, rdi
adcx r10, r8
mov rbx, [ rsp + 0x270 ]
mov r8, 0x0 
adox rbx, r8
adcx r9, r15
inc rdi
mov r8, -0x1 
movzx rdx, dl
adox rdx, r8
adox r10, [ rsp + 0xd0 ]
adcx r13, [ rsp + 0x280 ]
adcx r14, [ rsp + 0x278 ]
movzx r15, byte [ rsp + 0x110 ]
mov rdx, [ rsp - 0x48 ]
lea r15, [ r15 + rdx ]
adox r9, [ rsp + 0xc8 ]
setc dl
clc
adcx r11, rcx
adox r13, [ rsp + 0xc0 ]
setc r11b
clc
adcx r12, rbp
adox r14, [ rsp + 0xf8 ]
setc cl
clc
movzx r11, r11b
adcx r11, r8
adcx r10, r12
mov rbp, [ rsp + 0x2b0 ]
seto r11b
inc r8
mov rdi, -0x1 
movzx rcx, cl
adox rcx, rdi
adox rbp, [ rsp + 0x2b8 ]
mov r12, [ rsp + 0x2a8 ]
adox r12, [ rsp + 0x298 ]
adcx rbp, r9
adcx r12, r13
seto r9b
dec r8
movzx rdx, dl
adox rdx, r8
adox rbx, [ rsp + 0x290 ]
seto dil
inc r8
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox rbx, [ rsp + 0xf0 ]
movzx r13, dil
movzx rcx, byte [ rsp + 0x2a0 ]
lea r13, [ r13 + rcx ]
mov rcx, [ rsp + 0x288 ]
mov r11, rcx
seto dil
dec r8
movzx r9, r9b
adox r9, r8
adox r11, [ rsp + 0x298 ]
mov rdx, rcx
adox rdx, [ rsp + 0x298 ]
mov r9, 0x0 
adox rcx, r9
adcx r11, r14
adcx rdx, rbx
setc r14b
mov rbx, r10
mov r8, 0xffffffff 
sub rbx, r8
mov r9, rbp
mov r8, 0xffffffff00000000 
sbb r9, r8
mov r8, 0x0 
dec r8
movzx rdi, dil
adox rdi, r8
adox r13, r15
seto r15b
mov rdi, r12
mov r8, 0xfffffffffffffffe 
sbb rdi, r8
mov r8, r11
mov [ rsp + 0x2c0 ], rdi
mov rdi, 0xffffffffffffffff 
sbb r8, rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r14, r14b
adox r14, rdi
adox r13, rcx
movzx rcx, r15b
mov r14, 0x0 
adox rcx, r14
mov r15, rdx
mov r14, 0xffffffffffffffff 
sbb r15, r14
mov rdi, r13
sbb rdi, r14
sbb rcx, 0x00000000
cmovc rbx, r10
cmovc r15, rdx
cmovc r8, r11
cmovc r9, rbp
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x20 ], r15
mov r10, [ rsp + 0x2c0 ]
cmovc r10, r12
mov [ rcx + 0x8 ], r9
mov [ rcx + 0x10 ], r10
cmovc rdi, r13
mov [ rcx + 0x0 ], rbx
mov [ rcx + 0x28 ], rdi
mov [ rcx + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 840
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2457
; seed 4121940181461344 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 29558 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=71, initial num_batches=31): 808 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02733608498545233
; number reverted permutation / tried permutation: 310 / 508 =61.024%
; number reverted decision / tried decision: 292 / 491 =59.470%
; validated in 24.276s
