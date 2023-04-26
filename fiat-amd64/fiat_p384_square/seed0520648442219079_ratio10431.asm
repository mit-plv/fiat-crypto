SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 872
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r10
mulx r10, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rdi
mulx rdi, r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r10
mulx r10, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rax
mov [ rsp - 0x8 ], r10
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rax
mov [ rsp + 0x8 ], r10
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], rax
mulx rax, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], r11
mulx r11, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], rax
mulx rax, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rax
mov [ rsp + 0x48 ], r10
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], r9
mulx r9, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], r14
mulx r14, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], r15
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r15
mov [ rsp + 0x88 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r13
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r13
mov [ rsp + 0xa8 ], r8
mulx r8, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r13
mulx r13, r8, rdx
test al, al
adox r8, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r14
mov [ rsp + 0xd0 ], r10
mulx r10, r14, [ rsi + 0x10 ]
adcx rbx, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], rbx
mulx rbx, r8, [ rsi + 0x20 ]
adcx r12, rbp
setc dl
clc
adcx r15, rcx
adox rdi, r13
mov cl, dl
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
adcx r14, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], r14
mulx r14, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], r14
mulx r14, r15, [ rsi + 0x0 ]
adox r12, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r12
mulx r12, r11, [ rsi + 0x8 ]
adcx r15, r10
adcx rax, r14
adcx r9, [ rsp + 0xd0 ]
adox r11, rdi
mov rdx, [ rsp + 0x98 ]
setc r10b
clc
mov rdi, -0x1 
movzx rcx, cl
adcx rcx, rdi
adcx rdx, [ rsp + 0x90 ]
mov rcx, [ rsp + 0x58 ]
seto r14b
inc rdi
adox rcx, [ rsp + 0x78 ]
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rcx
mov [ rsp + 0x118 ], r11
mulx r11, rcx, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x50 ]
mov [ rsp + 0x120 ], rdi
seto dil
mov [ rsp + 0x128 ], r9
mov r9, -0x2 
inc r9
adox rdx, [ rsp + 0x48 ]
adox rbp, [ rsp + 0x38 ]
adox rcx, r13
adcx r8, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0xb8 ]
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, 0x100000001 
mov [ rsp + 0x138 ], r8
mov [ rsp + 0x140 ], rcx
mulx rcx, r8, [ rsp + 0x28 ]
movzx rcx, r10b
mov rdx, [ rsp + 0x100 ]
lea rcx, [ rcx + rdx ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x148 ], rbp
mulx rbp, r10, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x150 ], r13
mov [ rsp + 0x158 ], rcx
mulx rcx, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x160 ], rax
mov [ rsp + 0x168 ], r15
mulx r15, rax, r8
adox r11, [ rsp + 0x20 ]
mov rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x170 ], r11
mov r11, 0x0 
adcx rdx, r11
mov r11, [ rsp - 0x8 ]
adox r11, [ rsp - 0x10 ]
mov [ rsp + 0x178 ], rdx
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0x180 ], r11
mov r11, 0x0 
adox rdx, r11
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], r10
mulx r10, rbp, [ rsi + 0x28 ]
add dil, 0xFF
adcx r9, [ rsp + 0x40 ]
mov rdx, -0x1 
movzx r14, r14b
adox r14, rdx
adox r12, [ rsp - 0x28 ]
adcx rbx, [ rsp + 0x88 ]
mov r14, [ rsp - 0x18 ]
adcx r14, [ rsp + 0x80 ]
adcx rbp, [ rsp - 0x20 ]
setc dil
clc
adcx r13, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0xa8 ]
mov rdx, [ rsp - 0x30 ]
mov [ rsp + 0x198 ], rbp
mov rbp, 0x0 
adox rdx, rbp
movzx rbp, dil
lea rbp, [ rbp + r10 ]
mov r10, -0x2 
inc r10
adox rax, [ rsp + 0x28 ]
setc al
clc
adcx r15, [ rsp + 0x190 ]
adox r15, [ rsp + 0xf8 ]
mov rdi, 0xfffffffffffffffe 
xchg rdx, r8
mov [ rsp + 0x1a0 ], rbp
mulx rbp, r10, rdi
adcx r10, [ rsp + 0x188 ]
setc dil
clc
adcx r15, [ rsp + 0x70 ]
mov [ rsp + 0x1a8 ], r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], r9
mulx r9, rbx, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, 0x100000001 
mov [ rsp + 0x1c8 ], r13
mov [ rsp + 0x1d0 ], r11
mulx r11, r13, r15
mov r11, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp + 0x1d8 ], r8
mulx r8, r13, r11
mov r11, 0xfffffffffffffffe 
mov [ rsp + 0x1e0 ], r12
mov [ rsp + 0x1e8 ], rcx
mulx rcx, r12, r11
setc r11b
clc
mov [ rsp + 0x1f0 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx rbp, rbx
adox r10, [ rsp + 0xf0 ]
mov rdi, [ rsp + 0x18 ]
seto r8b
mov [ rsp + 0x1f8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rax, al
adox rax, r13
adox rdi, [ rsp + 0xa0 ]
setc al
clc
movzx r11, r11b
adcx r11, r13
adcx r10, [ rsp + 0xc0 ]
mov r11, [ rsp + 0x68 ]
adox r11, [ rsp + 0x10 ]
mov r13, r9
mov [ rsp + 0x200 ], r11
seto r11b
mov [ rsp + 0x208 ], rdi
mov rdi, 0x0 
dec rdi
movzx rax, al
adox rax, rdi
adox r13, rbx
adox rbx, r9
mov rax, 0xffffffff00000000 
mov [ rsp + 0x210 ], r10
mulx r10, rdi, rax
seto al
mov [ rsp + 0x218 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r8, r8b
adox r8, rbx
adox rbp, [ rsp + 0x168 ]
adcx rbp, [ rsp + 0xe8 ]
adox r13, [ rsp + 0x160 ]
seto r8b
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r14, [ rsp + 0x60 ]
mov r11, 0xffffffff 
mov [ rsp + 0x220 ], r14
mulx r14, rbx, r11
seto dl
mov r11, -0x2 
inc r11
adox rdi, r14
adox r12, r10
adcx r13, [ rsp + 0x108 ]
adox rcx, [ rsp + 0x1f8 ]
mov r10, [ rsp + 0x1f0 ]
mov r14, r10
adox r14, [ rsp + 0x1f8 ]
mov r11, r10
adox r11, [ rsp + 0x1f8 ]
mov [ rsp + 0x228 ], r11
movzx r11, dl
mov [ rsp + 0x230 ], r14
mov r14, [ rsp + 0x1e8 ]
lea r11, [ r11 + r14 ]
movzx r14, al
lea r14, [ r14 + r9 ]
mov r9, [ rsp + 0x128 ]
seto al
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r9, [ rsp + 0x218 ]
adox r14, [ rsp + 0x158 ]
adcx r9, [ rsp + 0x118 ]
adcx r14, [ rsp + 0x1e0 ]
seto r8b
inc rdx
adox rbx, r15
adox rdi, [ rsp + 0x210 ]
movzx r8, r8b
movzx rbx, r8b
adcx rbx, [ rsp + 0x1d8 ]
setc r15b
clc
adcx rdi, [ rsp - 0x40 ]
movzx r8, al
lea r8, [ r8 + r10 ]
adox r12, rbp
adox rcx, r13
adcx r12, [ rsp + 0x150 ]
mov r10, 0x100000001 
mov rdx, rdi
mulx rbp, rdi, r10
mov rbp, 0xffffffff00000000 
xchg rdx, rdi
mulx rax, r13, rbp
adox r9, [ rsp + 0x230 ]
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0x238 ], r11
mulx r11, r10, rbp
adox r14, [ rsp + 0x228 ]
adcx rcx, [ rsp + 0x148 ]
adox r8, rbx
adcx r9, [ rsp + 0x140 ]
mov rbx, 0xffffffff 
mov [ rsp + 0x240 ], r9
mulx r9, rbp, rbx
adcx r14, [ rsp + 0x170 ]
seto bl
mov [ rsp + 0x248 ], r14
mov r14, -0x2 
inc r14
adox r13, r9
movzx r9, bl
movzx r15, r15b
lea r9, [ r9 + r15 ]
setc r15b
clc
adcx rbp, rdi
adcx r13, r12
adox r10, rax
mov rbp, 0xffffffffffffffff 
mulx r12, rdi, rbp
setc dl
clc
adcx r13, [ rsp + 0x0 ]
mov rax, rdi
adox rax, r11
mov r11, rdi
adox r11, r12
setc bl
clc
movzx r15, r15b
adcx r15, r14
adcx r8, [ rsp + 0x180 ]
mov r15, 0x100000001 
xchg rdx, r13
mulx rbp, r14, r15
mov rbp, 0xffffffff 
xchg rdx, r14
mov [ rsp + 0x250 ], r8
mulx r8, r15, rbp
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0x258 ], r11
mov byte [ rsp + 0x260 ], bl
mulx rbx, r11, rbp
adox rdi, r12
mov rbp, 0xffffffff00000000 
mov [ rsp + 0x268 ], rdi
mov [ rsp + 0x270 ], rbx
mulx rbx, rdi, rbp
seto bpl
mov [ rsp + 0x278 ], r11
mov r11, -0x2 
inc r11
adox r15, r14
seto r15b
inc r11
adox rdi, r8
adcx r9, [ rsp + 0x1d0 ]
mov r14, 0xffffffffffffffff 
mulx r11, r8, r14
seto dl
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r13, r13b
adox r13, r14
adox rcx, r10
adox rax, [ rsp + 0x240 ]
movzx r13, bpl
lea r13, [ r13 + r12 ]
seto r10b
inc r14
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox rbx, [ rsp + 0x278 ]
mov rbp, r8
adox rbp, [ rsp + 0x270 ]
mov rdx, r8
adox rdx, r11
setc r14b
movzx r12, byte [ rsp + 0x260 ]
clc
mov [ rsp + 0x280 ], rdx
mov rdx, -0x1 
adcx r12, rdx
adcx rcx, [ rsp + 0x1c8 ]
adox r8, r11
mov r12, 0x0 
adox r11, r12
mov r12, [ rsp + 0x248 ]
inc rdx
mov rdx, -0x1 
movzx r10, r10b
adox r10, rdx
adox r12, [ rsp + 0x258 ]
adcx rax, [ rsp + 0x1c0 ]
adcx r12, [ rsp + 0x208 ]
seto r10b
inc rdx
mov rdx, -0x1 
movzx r15, r15b
adox r15, rdx
adox rcx, rdi
mov r15, [ rsp + 0x268 ]
setc dil
clc
movzx r10, r10b
adcx r10, rdx
adcx r15, [ rsp + 0x250 ]
seto r10b
inc rdx
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox r15, [ rsp + 0x200 ]
seto dil
inc rdx
mov rdx, -0x1 
movzx r10, r10b
adox r10, rdx
adox rax, rbx
adcx r13, r9
setc r9b
clc
adcx rcx, [ rsp - 0x48 ]
setc bl
clc
movzx rdi, dil
adcx rdi, rdx
adcx r13, [ rsp + 0x220 ]
mov r10, 0x100000001 
mov rdx, r10
mulx rdi, r10, rcx
mov rdi, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp + 0x288 ], r11
mulx r11, r10, rdi
mov rdi, 0xffffffff 
mov [ rsp + 0x290 ], r11
mov [ rsp + 0x298 ], r10
mulx r10, r11, rdi
adox rbp, r12
adox r15, [ rsp + 0x280 ]
adox r8, r13
seto r12b
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox rax, [ rsp + 0x110 ]
movzx rbx, r9b
movzx r14, r14b
lea rbx, [ rbx + r14 ]
adox rbp, [ rsp + 0x1b8 ]
adcx rbx, [ rsp + 0x238 ]
mov r14, 0xffffffff00000000 
mulx r13, r9, r14
setc dil
clc
adcx r9, r10
mov r10, 0xfffffffffffffffe 
mov byte [ rsp + 0x2a0 ], dil
mulx rdi, r14, r10
adox r15, [ rsp + 0x1b0 ]
adox r8, [ rsp + 0x1a8 ]
adcx r14, r13
seto dl
mov r13, -0x2 
inc r13
adox r11, rcx
adox r9, rax
seto r11b
inc r13
adox r9, [ rsp + 0xc8 ]
seto cl
dec r13
movzx r11, r11b
adox r11, r13
adox rbp, r14
mov rax, 0x100000001 
xchg rdx, r9
mulx r11, r14, rax
adcx rdi, [ rsp + 0x298 ]
mov r11, 0xffffffff 
xchg rdx, r14
mulx r10, r13, r11
seto r11b
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx rcx, cl
adox rcx, rax
adox rbp, [ rsp + 0xd8 ]
seto cl
inc rax
adox r13, r14
mov r13, 0xffffffff00000000 
mulx rax, r14, r13
seto r13b
mov byte [ rsp + 0x2a8 ], cl
mov rcx, -0x2 
inc rcx
adox r14, r10
mov r10, 0xffffffffffffffff 
mov byte [ rsp + 0x2b0 ], r9b
mulx r9, rcx, r10
mov r10, [ rsp + 0x290 ]
mov [ rsp + 0x2b8 ], r9
mov r9, r10
adcx r9, [ rsp + 0x298 ]
mov [ rsp + 0x2c0 ], r9
mov r9, r10
adcx r9, [ rsp + 0x298 ]
mov [ rsp + 0x2c8 ], r9
mov r9, 0xfffffffffffffffe 
mov [ rsp + 0x2d0 ], r8
mov [ rsp + 0x2d8 ], r14
mulx r14, r8, r9
mov rdx, 0x0 
adcx r10, rdx
adox r8, rax
clc
mov rax, -0x1 
movzx r11, r11b
adcx r11, rax
adcx r15, rdi
mov r11, rcx
adox r11, r14
setc dil
clc
movzx r12, r12b
adcx r12, rax
adcx rbx, [ rsp + 0x288 ]
seto r12b
inc rax
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox rbp, [ rsp + 0x2d8 ]
movzx r13, byte [ rsp + 0x2a0 ]
adcx r13, rax
seto r14b
mov rdx, rbp
mov r9, 0xffffffff 
sub rdx, r9
mov rax, [ rsp + 0x2d0 ]
mov r9, 0x0 
dec r9
movzx rdi, dil
adox rdi, r9
adox rax, [ rsp + 0x2c0 ]
seto dil
movzx r9, byte [ rsp + 0x2b0 ]
mov [ rsp + 0x2e0 ], rdx
mov rdx, 0x0 
dec rdx
adox r9, rdx
adox rbx, [ rsp + 0x198 ]
setc r9b
clc
movzx rdi, dil
adcx rdi, rdx
adcx rbx, [ rsp + 0x2c8 ]
adox r13, [ rsp + 0x1a0 ]
adcx r10, r13
seto dil
adc dil, 0x0
movzx rdi, dil
add byte [ rsp + 0x2a8 ], 0x7F
adox r15, [ rsp + 0xe0 ]
mov r13, rcx
movzx r12, r12b
adcx r12, rdx
adcx r13, [ rsp + 0x2b8 ]
adcx rcx, [ rsp + 0x2b8 ]
setc r12b
clc
movzx r14, r14b
adcx r14, rdx
adcx r15, r8
adox rax, [ rsp + 0x120 ]
adcx r11, rax
adox rbx, [ rsp + 0x138 ]
adcx r13, rbx
adox r10, [ rsp + 0x130 ]
movzx rdi, dil
movzx r8, dil
adox r8, [ rsp + 0x178 ]
setc r14b
seto dil
movzx rax, r9b
add rax, -0x1
mov rax, r15
mov r9, 0xffffffff00000000 
sbb rax, r9
inc rdx
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox r10, rcx
seto cl
mov r14, r11
mov rdx, 0xfffffffffffffffe 
sbb r14, rdx
movzx rbx, r12b
mov rdx, [ rsp + 0x2b8 ]
lea rbx, [ rbx + rdx ]
mov rdx, -0x1 
inc rdx
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox r8, rbx
seto cl
mov rbx, r13
mov rdx, 0xffffffffffffffff 
sbb rbx, rdx
movzx r12, cl
movzx rdi, dil
lea r12, [ r12 + rdi ]
mov rdi, r10
sbb rdi, rdx
mov rcx, r8
sbb rcx, rdx
sbb r12, 0x00000000
cmovc rcx, r8
cmovc r14, r11
cmovc rbx, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], rbx
mov r11, [ rsp + 0x2e0 ]
cmovc r11, rbp
mov [ r12 + 0x0 ], r11
mov [ r12 + 0x10 ], r14
cmovc rdi, r10
cmovc rax, r15
mov [ r12 + 0x20 ], rdi
mov [ r12 + 0x28 ], rcx
mov [ r12 + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 872
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0431
; seed 0520648442219079 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 60208 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 1438 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.02388386925325538
; number reverted permutation / tried permutation: 332 / 495 =67.071%
; number reverted decision / tried decision: 269 / 504 =53.373%
; validated in 39.996s
