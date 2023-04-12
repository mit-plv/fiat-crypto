SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1744
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r12
mulx r12, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], rbx
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r11
mulx r11, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], rbx
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r11
mulx r11, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r9
mulx r9, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r10
mulx r10, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], rbp
mulx rbp, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r10
mulx r10, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], rbp
mulx rbp, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa8 ], r10
mov [ rsp + 0xb0 ], r15
mulx r15, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r10
mov [ rsp + 0xc0 ], r14
mulx r14, r10, [ rax + 0x0 ]
test al, al
adox rbx, r14
adox r12, r11
mov rdx, [ rax + 0x20 ]
mulx r14, r11, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc8 ], r12
mov [ rsp + 0xd0 ], rbx
mulx rbx, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r11
mulx r11, r14, [ rax + 0x8 ]
adcx r14, r15
seto dl
mov r15, -0x2 
inc r15
adox rdi, rbp
mov bpl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xf0 ], r14
mov [ rsp + 0xf8 ], rdi
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
seto dl
mov [ rsp + 0x110 ], rdi
mov rdi, -0x2 
inc rdi
adox r8, r9
adox r13, rcx
mov cl, dl
mov rdx, [ rax + 0x20 ]
mulx rdi, r9, [ rsi + 0x8 ]
adox r15, [ rsp + 0xc0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], r15
mov [ rsp + 0x120 ], r13
mulx r13, r15, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x70 ]
mov [ rsp + 0x128 ], r15
seto r15b
mov [ rsp + 0x130 ], r8
mov r8, 0x0 
dec r8
movzx rcx, cl
adox rcx, r8
adox rdx, [ rsp + 0xb0 ]
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x138 ], r15b
mulx r15, r8, [ rsi + 0x10 ]
adox r14, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], r14
mov [ rsp + 0x148 ], rcx
mulx rcx, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x160 ], rdi
mov [ rsp + 0x168 ], r10
mulx r10, rdi, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x170 ], r9
mov [ rsp + 0x178 ], r10
mulx r10, r9, rdi
adcx r14, r11
setc r11b
clc
adcx r8, rcx
mov rcx, 0x2341f27177344 
mov rdx, rdi
mov [ rsp + 0x180 ], r14
mulx r14, rdi, rcx
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], rdi
mulx rdi, r14, rcx
adcx r15, [ rsp + 0x40 ]
seto cl
mov [ rsp + 0x198 ], rdi
mov rdi, -0x2 
inc rdi
adox r12, r13
mov r13, [ rsp + 0x38 ]
seto dil
mov [ rsp + 0x1a0 ], r12
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox r13, [ rsp + 0x68 ]
mov rbp, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
setc r12b
clc
mov [ rsp + 0x1a8 ], rbp
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx rbx, [ rsp + 0xa0 ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1b0 ], rbx
mulx rbx, rbp, [ rax + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1b8 ], r15
mov [ rsp + 0x1c0 ], r8
mulx r8, r15, rdi
adcx rbp, [ rsp + 0x98 ]
mov rdx, [ rsp + 0x60 ]
mov [ rsp + 0x1c8 ], rbp
seto bpl
mov [ rsp + 0x1d0 ], r13
mov r13, -0x2 
inc r13
adox rdx, [ rsp + 0x178 ]
mov r13, [ rsp - 0x10 ]
mov [ rsp + 0x1d8 ], r14
seto r14b
mov [ rsp + 0x1e0 ], r8
mov r8, 0x0 
dec r8
movzx rbp, bpl
adox rbp, r8
adox r13, [ rsp + 0x170 ]
mov rbp, r9
setc r8b
clc
adcx rbp, rdi
mov rbp, r9
mov [ rsp + 0x1e8 ], r13
setc r13b
clc
adcx rbp, r10
adcx r9, r10
mov [ rsp + 0x1f0 ], r15
setc r15b
clc
mov [ rsp + 0x1f8 ], rbx
mov rbx, -0x1 
movzx r13, r13b
adcx r13, rbx
adcx rdx, rbp
setc r13b
clc
adcx rdx, [ rsp + 0x168 ]
mov rbp, rdx
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x200 ], r15b
mulx r15, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x208 ], r8b
mov byte [ rsp + 0x210 ], cl
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0x218 ], rcx
setc cl
clc
mov [ rsp + 0x220 ], r8
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx rdx, [ rsp + 0x58 ]
adcx rbx, [ rsp + 0x18 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x228 ], rbx
mulx rbx, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x230 ], rbx
mov byte [ rsp + 0x238 ], cl
mulx rcx, rbx, [ rsi + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x240 ], r9
mov [ rsp + 0x248 ], r14
mulx r14, r9, rbp
adcx r15, [ rsp - 0x18 ]
seto dl
mov [ rsp + 0x250 ], r14
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox rbx, [ rsp + 0x158 ]
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mov [ rsp + 0x258 ], rbx
mulx rbx, r14, rbp
adox rcx, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x260 ], rcx
mov [ rsp + 0x268 ], r9
mulx r9, rcx, [ rax + 0x30 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x270 ], r9
mov [ rsp + 0x278 ], rcx
mulx rcx, r9, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x280 ], rcx
mov [ rsp + 0x288 ], r9
mulx r9, rcx, [ rax + 0x28 ]
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x290 ], r9
seto r9b
mov [ rsp + 0x298 ], r15
mov r15, 0x0 
dec r15
movzx r12, r12b
adox r12, r15
adox rdx, [ rsp - 0x28 ]
setc r12b
clc
movzx r11, r11b
adcx r11, r15
adcx r8, [ rsp + 0x150 ]
mov r11, [ rsp + 0x240 ]
setc r15b
clc
mov [ rsp + 0x2a0 ], rdx
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r11, [ rsp + 0x248 ]
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x2a8 ], r15b
mulx r15, r13, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x110 ]
mov [ rsp + 0x2b0 ], r8
setc r8b
mov [ rsp + 0x2b8 ], rbx
movzx rbx, byte [ rsp + 0x138 ]
clc
mov [ rsp + 0x2c0 ], r11
mov r11, -0x1 
adcx rbx, r11
adcx rdx, [ rsp + 0x10 ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, rbx
mov [ rsp + 0x2c8 ], rbx
mulx rbx, r11, rbp
mov rdx, [ rsp + 0x88 ]
adox rdx, [ rsp + 0x30 ]
adcx r13, [ rsp + 0x8 ]
mov [ rsp + 0x2d0 ], r13
mov r13, [ rsp + 0x220 ]
adox r13, [ rsp + 0x28 ]
mov [ rsp + 0x2d8 ], r13
mov r13, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2e0 ], rbx
mov [ rsp + 0x2e8 ], r11
mulx r11, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2f0 ], r13
mov byte [ rsp + 0x2f8 ], r8b
mulx r8, r13, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x300 ], r8
mov [ rsp + 0x308 ], r14
mulx r14, r8, [ rsi + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x310 ], r14
mov [ rsp + 0x318 ], r13
mulx r13, r14, rbp
mov rdx, [ rsp + 0xe0 ]
mov [ rsp + 0x320 ], r13
setc r13b
mov [ rsp + 0x328 ], r14
movzx r14, byte [ rsp + 0x210 ]
clc
mov [ rsp + 0x330 ], r8
mov r8, -0x1 
adcx r14, r8
adcx rdx, [ rsp + 0x108 ]
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x338 ], rdi
mulx rdi, r8, r14
mov rdx, [ rsp + 0xd8 ]
adcx rdx, [ rsp + 0x80 ]
mov r14, [ rsp + 0x218 ]
mov [ rsp + 0x340 ], rdx
mov rdx, 0x0 
adox r14, rdx
adcx rbx, [ rsp + 0x78 ]
dec rdx
movzx r9, r9b
adox r9, rdx
adox rcx, [ rsp - 0x30 ]
mov r9, [ rsp + 0x100 ]
setc dl
clc
mov [ rsp + 0x348 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r9, [ rsp - 0x38 ]
movzx r12, dl
lea r12, [ r12 + r11 ]
seto r11b
inc rbx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox r15, [ rsp + 0x330 ]
mov r13, [ rsp + 0x1f8 ]
setc bl
movzx rdx, byte [ rsp + 0x208 ]
clc
mov [ rsp + 0x350 ], r12
mov r12, -0x1 
adcx rdx, r12
adcx r13, [ rsp + 0x318 ]
mov rdx, [ rsp + 0xf8 ]
setc r12b
clc
mov [ rsp + 0x358 ], r13
mov r13, -0x1 
movzx rbx, bl
adcx rbx, r13
adcx rdx, [ rsp - 0x40 ]
mov rbx, [ rsp - 0x48 ]
mov r13, 0x0 
adcx rbx, r13
clc
adcx rbp, [ rsp + 0x308 ]
mov rbp, [ rsp + 0x2c0 ]
seto r13b
mov [ rsp + 0x360 ], r15
movzx r15, byte [ rsp + 0x238 ]
mov [ rsp + 0x368 ], rcx
mov rcx, 0x0 
dec rcx
adox r15, rcx
adox rbp, [ rsp + 0xd0 ]
setc r15b
movzx rcx, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x370 ], r14
mov r14, -0x1 
adcx rcx, r14
adcx r10, r8
adcx rdi, [ rsp + 0x1f0 ]
mov rcx, [ rsp + 0x1e0 ]
adcx rcx, [ rsp + 0x1d8 ]
mov r8, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x378 ], rbx
mulx rbx, r14, [ rsi + 0x30 ]
movzx rdx, r13b
mov [ rsp + 0x380 ], r8
mov r8, [ rsp + 0x310 ]
lea rdx, [ rdx + r8 ]
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x388 ], r11b
mulx r11, r13, [ rax + 0x30 ]
mov rdx, [ rsp + 0x2b8 ]
mov [ rsp + 0x390 ], r8
mov r8, rdx
mov [ rsp + 0x398 ], rcx
setc cl
clc
adcx r8, [ rsp + 0x308 ]
mov byte [ rsp + 0x3a0 ], cl
seto cl
mov [ rsp + 0x3a8 ], r9
mov r9, 0x0 
dec r9
movzx r12, r12b
adox r12, r9
adox r14, [ rsp + 0x300 ]
mov r12, rdx
adcx r12, [ rsp + 0x308 ]
adox r13, rbx
seto bl
movzx r9, byte [ rsp + 0x2f8 ]
mov [ rsp + 0x3b0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r9, r13
adox r10, [ rsp + 0x228 ]
setc r9b
clc
movzx r15, r15b
adcx r15, r13
adcx rbp, r8
seto r15b
inc r13
adox rbp, [ rsp + 0x160 ]
seto r8b
dec r13
movzx rcx, cl
adox rcx, r13
adox r10, [ rsp + 0xc8 ]
movzx rcx, bl
lea rcx, [ rcx + r11 ]
mov r11, rdx
mov rdx, [ rax + 0x30 ]
mulx r13, rbx, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x3b8 ], rcx
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rdi, [ rsp + 0x298 ]
mov r15, [ rsp + 0x3a8 ]
adcx r15, [ rsp + 0x398 ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x3c0 ], r14
mov byte [ rsp + 0x3c8 ], r8b
mulx r8, r14, rbp
seto dl
mov [ rsp + 0x3d0 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r9, r9b
adox r9, r8
adox r11, [ rsp + 0x328 ]
setc r9b
movzx r8, byte [ rsp + 0x388 ]
clc
mov [ rsp + 0x3d8 ], r14
mov r14, -0x1 
adcx r8, r14
adcx rbx, [ rsp + 0x290 ]
mov r8, 0x0 
adcx r13, r8
mov r8, [ rsp + 0x288 ]
adox r8, [ rsp + 0x320 ]
mov r14, [ rsp + 0x280 ]
adox r14, [ rsp + 0x2e8 ]
mov [ rsp + 0x3e0 ], r13
mov r13, [ rsp + 0x268 ]
adox r13, [ rsp + 0x2e0 ]
mov [ rsp + 0x3e8 ], rbx
mov rbx, [ rsp + 0x250 ]
mov [ rsp + 0x3f0 ], r13
mov r13, 0x0 
adox rbx, r13
mov r13, 0x7bc65c783158aea3 
xchg rdx, rbp
mov [ rsp + 0x3f8 ], rbx
mov [ rsp + 0x400 ], r14
mulx r14, rbx, r13
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x408 ], r14
mov [ rsp + 0x410 ], rbx
mulx rbx, r14, r13
mov r13, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x418 ], r9b
mov [ rsp + 0x420 ], r8
mulx r8, r9, r13
mov r13, r14
test al, al
adox r13, rdx
mov r13, r14
adcx r13, rbx
mov [ rsp + 0x428 ], r8
seto r8b
mov [ rsp + 0x430 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx rbp, bpl
adox rbp, r9
adox rdi, [ rsp + 0x1d0 ]
adox r15, [ rsp + 0x1e8 ]
seto bpl
inc r9
mov r9, -0x1 
movzx rcx, cl
adox rcx, r9
adox r10, r12
adox r11, rdi
adox r15, [ rsp + 0x420 ]
setc r12b
movzx rcx, byte [ rsp + 0x3c8 ]
clc
adcx rcx, r9
adcx r10, [ rsp + 0x1c0 ]
adcx r11, [ rsp + 0x1b8 ]
seto cl
inc r9
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox r10, r13
seto r8b
mov r13, -0x3 
inc r13
adox r10, [ rsp + 0xb8 ]
adcx r15, [ rsp + 0x1a8 ]
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mulx rdi, r13, r10
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x438 ], r15
mov [ rsp + 0x440 ], r11
mulx r11, r15, r10
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x448 ], r11
mov byte [ rsp + 0x450 ], r8b
mulx r8, r11, r10
mov rdx, [ rsp + 0x198 ]
mov [ rsp + 0x458 ], r8
setc r8b
mov [ rsp + 0x460 ], r11
movzx r11, byte [ rsp + 0x3a0 ]
clc
mov [ rsp + 0x468 ], r15
mov r15, -0x1 
adcx r11, r15
adcx rdx, [ rsp + 0x190 ]
seto r11b
movzx r15, byte [ rsp + 0x418 ]
mov byte [ rsp + 0x470 ], r8b
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r15, r8
adox rdx, [ rsp + 0x380 ]
mov r15, [ rsp + 0x188 ]
mov r8, 0x0 
adcx r15, r8
mov byte [ rsp + 0x478 ], r11b
mov r11, r13
clc
adcx r11, rdi
mov r8, r13
adcx r8, rdi
mov [ rsp + 0x480 ], r8
seto r8b
mov [ rsp + 0x488 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rbp, bpl
adox rbp, r11
adox rdx, [ rsp + 0x2b0 ]
seto bpl
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox rdx, [ rsp + 0x400 ]
mov rcx, rbx
seto r11b
mov [ rsp + 0x490 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r12, r12b
adox r12, rdx
adox rcx, r14
adox rbx, [ rsp + 0x430 ]
mov r14, [ rsp + 0x410 ]
adox r14, [ rsp + 0x428 ]
adcx rdi, [ rsp + 0x468 ]
mov r12, [ rsp + 0x408 ]
adox r12, [ rsp + 0x3d8 ]
mov rdx, [ rsp + 0x278 ]
mov [ rsp + 0x498 ], rdi
seto dil
mov [ rsp + 0x4a0 ], r12
movzx r12, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x4a8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r12, r14
adox rdx, [ rsp + 0x230 ]
mov r12, 0x2341f27177344 
xchg rdx, r12
mov byte [ rsp + 0x4b0 ], dil
mulx rdi, r14, r10
setc dl
clc
mov [ rsp + 0x4b8 ], rdi
mov rdi, -0x1 
movzx r8, r8b
adcx r8, rdi
adcx r15, [ rsp + 0x378 ]
seto r8b
inc rdi
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox r15, r12
movzx rbp, r8b
mov r12, [ rsp + 0x270 ]
lea rbp, [ rbp + r12 ]
seto r12b
movzx r8, byte [ rsp + 0x450 ]
inc rdi
mov rdi, -0x1 
adox r8, rdi
adox rcx, [ rsp + 0x440 ]
mov r8, 0x2341f27177344 
xchg rdx, r8
mov [ rsp + 0x4c0 ], r14
mulx r14, rdi, r9
movzx r9, r12b
adcx r9, rbp
setc r12b
clc
mov rbp, -0x1 
movzx r11, r11b
adcx r11, rbp
adcx r15, [ rsp + 0x3f0 ]
adcx r9, [ rsp + 0x3f8 ]
movzx r11, r12b
mov rbp, 0x0 
adcx r11, rbp
adox rbx, [ rsp + 0x438 ]
mov r12, 0x7bc65c783158aea3 
mov rdx, r10
mulx rbp, r10, r12
movzx r12, byte [ rsp + 0x4b0 ]
clc
mov [ rsp + 0x4c8 ], r11
mov r11, -0x1 
adcx r12, r11
adcx rdi, [ rsp + 0x3d0 ]
seto r12b
inc r11
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox r10, [ rsp + 0x448 ]
mov r8, 0x0 
adcx r14, r8
adox rbp, [ rsp + 0x460 ]
movzx r8, byte [ rsp + 0x478 ]
clc
adcx r8, r11
adcx rcx, [ rsp + 0xf0 ]
seto r8b
inc r11
adox r13, rdx
adcx rbx, [ rsp + 0x180 ]
adox rcx, [ rsp + 0x488 ]
mov r13, [ rsp + 0x490 ]
seto dl
movzx r11, byte [ rsp + 0x470 ]
mov [ rsp + 0x4d0 ], rbp
mov rbp, 0x0 
dec rbp
adox r11, rbp
adox r13, [ rsp + 0x2a0 ]
adox r15, [ rsp + 0x2f0 ]
adox r9, [ rsp + 0x2d8 ]
setc r11b
clc
adcx rcx, [ rsp + 0x48 ]
mov rbp, 0x2341f27177344 
xchg rdx, rcx
mov [ rsp + 0x4d8 ], r10
mov [ rsp + 0x4e0 ], r14
mulx r14, r10, rbp
mov rbp, 0x6cfc5fd681c52056 
mov [ rsp + 0x4e8 ], r14
mov [ rsp + 0x4f0 ], r10
mulx r10, r14, rbp
mov rbp, [ rsp + 0x4c8 ]
adox rbp, [ rsp + 0x370 ]
mov [ rsp + 0x4f8 ], r10
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x500 ], r14
mov [ rsp + 0x508 ], rbp
mulx rbp, r14, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x510 ], rbp
mov [ rsp + 0x518 ], r14
mulx r14, rbp, r10
setc r10b
clc
mov [ rsp + 0x520 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r13, [ rsp + 0x4a8 ]
mov r12, rbp
seto bl
mov byte [ rsp + 0x528 ], r10b
mov r10, -0x2 
inc r10
adox r12, rdx
adcx r15, [ rsp + 0x4a0 ]
mov r12, rbp
setc r10b
clc
adcx r12, r14
mov byte [ rsp + 0x530 ], bl
seto bl
mov [ rsp + 0x538 ], r12
mov r12, 0x0 
dec r12
movzx r11, r11b
adox r11, r12
adox r13, [ rsp + 0x258 ]
setc r11b
clc
movzx r10, r10b
adcx r10, r12
adcx r9, rdi
mov rdi, [ rsp + 0x4c0 ]
setc r10b
clc
movzx r8, r8b
adcx r8, r12
adcx rdi, [ rsp + 0x458 ]
mov r8, r14
seto r12b
mov [ rsp + 0x540 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r11, r11b
adox r11, rdi
adox r8, rbp
seto bpl
inc rdi
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox r15, [ rsp + 0x260 ]
adox r9, [ rsp + 0x368 ]
mov r12, [ rsp + 0x4b8 ]
adcx r12, rdi
mov rdi, 0xfdc1767ae2ffffff 
mov [ rsp + 0x548 ], r12
mulx r12, r11, rdi
clc
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx r14, r11
mov rbp, [ rsp + 0x520 ]
setc r11b
clc
movzx rcx, cl
adcx rcx, rdx
adcx rbp, [ rsp + 0x480 ]
adcx r13, [ rsp + 0x498 ]
seto cl
movzx rdx, byte [ rsp + 0x528 ]
mov rdi, 0x0 
dec rdi
adox rdx, rdi
adox rbp, [ rsp + 0x130 ]
adox r13, [ rsp + 0x120 ]
mov rdx, [ rsp + 0x508 ]
seto dil
mov [ rsp + 0x550 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r10, r10b
adox r10, r14
adox rdx, [ rsp + 0x4e0 ]
seto r10b
inc r14
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox r12, [ rsp + 0x518 ]
adcx r15, [ rsp + 0x4d8 ]
seto r11b
inc r14
mov r14, -0x1 
movzx rbx, bl
adox rbx, r14
adox rbp, [ rsp + 0x538 ]
adcx r9, [ rsp + 0x4d0 ]
setc bl
clc
adcx rbp, [ rsp + 0xa8 ]
mov r14, [ rsp + 0x500 ]
mov byte [ rsp + 0x558 ], bl
setc bl
clc
mov [ rsp + 0x560 ], r12
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r14, [ rsp + 0x510 ]
adox r8, r13
mov r13, [ rsp + 0x4f0 ]
adcx r13, [ rsp + 0x4f8 ]
setc r11b
clc
movzx rdi, dil
adcx rdi, r12
adcx r15, [ rsp + 0x118 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x568 ], r13
mulx r13, r12, rbp
adcx r9, [ rsp + 0x2c8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x570 ], r13
mov [ rsp + 0x578 ], r12
mulx r12, r13, rbp
movzx rdx, r10b
mov [ rsp + 0x580 ], r14
movzx r14, byte [ rsp + 0x530 ]
lea rdx, [ rdx + r14 ]
setc r14b
clc
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rdi, [ rsp + 0x3e8 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, rbp
mov byte [ rsp + 0x588 ], r11b
mulx r11, r10, rcx
adcx rbp, [ rsp + 0x3e0 ]
adox r15, [ rsp + 0x550 ]
setc cl
clc
mov [ rsp + 0x590 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r8, [ rsp + 0xe8 ]
adox r9, [ rsp + 0x560 ]
seto bl
movzx r11, byte [ rsp + 0x558 ]
mov [ rsp + 0x598 ], r10
mov r10, 0x0 
dec r10
adox r11, r10
adox rdi, [ rsp + 0x540 ]
adox rbp, [ rsp + 0x548 ]
mov r11, r13
seto r10b
mov byte [ rsp + 0x5a0 ], cl
mov rcx, -0x2 
inc rcx
adox r11, rdx
adcx r15, [ rsp + 0x148 ]
seto r11b
inc rcx
mov rcx, -0x1 
movzx r14, r14b
adox r14, rcx
adox rdi, [ rsp + 0x2d0 ]
adcx r9, [ rsp + 0x140 ]
adox rbp, [ rsp + 0x360 ]
mov r14, r13
setc cl
clc
adcx r14, r12
mov [ rsp + 0x5a8 ], r9
movzx r9, byte [ rsp + 0x588 ]
mov byte [ rsp + 0x5b0 ], cl
mov rcx, [ rsp + 0x4e8 ]
lea r9, [ r9 + rcx ]
adcx r13, r12
setc cl
clc
mov [ rsp + 0x5b8 ], r9
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx rdi, [ rsp + 0x580 ]
adcx rbp, [ rsp + 0x568 ]
setc bl
clc
movzx r11, r11b
adcx r11, r9
adcx r8, r14
movzx r11, r10b
movzx r14, byte [ rsp + 0x5a0 ]
lea r11, [ r11 + r14 ]
adcx r13, r15
adox r11, [ rsp + 0x390 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, r9
adcx r11, [ rsp + 0x5b8 ]
seto r10b
movzx r15, byte [ rsp + 0x5b0 ]
inc r9
mov rbx, -0x1 
adox r15, rbx
adox rdi, [ rsp + 0x338 ]
adox rbp, [ rsp + 0x340 ]
movzx r15, r10b
adcx r15, r9
clc
adcx r8, [ rsp + 0x128 ]
adcx r13, [ rsp + 0x1a0 ]
seto r10b
inc rbx
mov r9, -0x1 
movzx rcx, cl
adox rcx, r9
adox r12, [ rsp + 0x578 ]
mov rcx, [ rsp + 0x570 ]
adox rcx, [ rsp + 0x598 ]
seto bl
inc r9
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox r12, [ rsp + 0x5a8 ]
mov r14, 0x7bc65c783158aea3 
xchg rdx, r8
mov [ rsp + 0x5c0 ], r13
mulx r13, r9, r14
adox rcx, rdi
adcx r12, [ rsp + 0x1b0 ]
setc dil
clc
mov r14, -0x1 
movzx r10, r10b
adcx r10, r14
adcx r11, [ rsp + 0x348 ]
mov r10, 0x6cfc5fd681c52056 
mov [ rsp + 0x5c8 ], r13
mulx r13, r14, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x5d0 ], r13
mov [ rsp + 0x5d8 ], r14
mulx r14, r13, r10
adcx r15, [ rsp + 0x350 ]
mov r10, r13
mov [ rsp + 0x5e0 ], r12
setc r12b
clc
adcx r10, rdx
mov r10, r13
mov byte [ rsp + 0x5e8 ], r12b
setc r12b
clc
adcx r10, r14
mov [ rsp + 0x5f0 ], r10
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r8
mov byte [ rsp + 0x5f8 ], r12b
mov [ rsp + 0x600 ], r15
mulx r15, r12, r10
mov r10, 0x2341f27177344 
mov [ rsp + 0x608 ], rcx
mov byte [ rsp + 0x610 ], dil
mulx rdi, rcx, r10
seto dl
mov r10, 0x0 
dec r10
movzx rbx, bl
adox rbx, r10
adox r12, [ rsp + 0x590 ]
adox rcx, r15
adcx r13, r14
seto bl
inc r10
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox rbp, r12
mov rdx, 0xfdc1767ae2ffffff 
mulx r10, r12, r8
adcx r12, r14
adcx r9, r10
adox rcx, r11
movzx r11, bl
lea r11, [ r11 + rdi ]
mov r14, [ rsp + 0x608 ]
setc dil
movzx rbx, byte [ rsp + 0x610 ]
clc
adcx rbx, r15
adcx r14, [ rsp + 0x1c8 ]
adcx rbp, [ rsp + 0x358 ]
adox r11, [ rsp + 0x600 ]
movzx rbx, byte [ rsp + 0x5e8 ]
mov r10, 0x0 
adox rbx, r10
adcx rcx, [ rsp + 0x3c0 ]
mov r10, [ rsp + 0x5c0 ]
movzx r15, byte [ rsp + 0x5f8 ]
mov rdx, 0x0 
dec rdx
adox r15, rdx
adox r10, [ rsp + 0x5f0 ]
setc r15b
seto dl
mov [ rsp + 0x618 ], rcx
mov rcx, r10
mov [ rsp + 0x620 ], r9
mov r9, 0xffffffffffffffff 
sub rcx, r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox r13, [ rsp + 0x5e0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x628 ], rcx
mulx rcx, r9, r8
seto r8b
mov rdx, r13
mov [ rsp + 0x630 ], rcx
mov rcx, 0xffffffffffffffff 
sbb rdx, rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox r11, [ rsp + 0x3b0 ]
adox rbx, [ rsp + 0x3b8 ]
setc r15b
clc
movzx r8, r8b
adcx r8, rcx
adcx r14, r12
mov r12, [ rsp + 0x5c8 ]
seto r8b
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox r12, [ rsp + 0x5d8 ]
adcx rbp, [ rsp + 0x620 ]
adox r9, [ rsp + 0x5d0 ]
setc dil
seto cl
mov [ rsp + 0x638 ], rdx
movzx rdx, r15b
add rdx, -0x1
mov rdx, r14
mov r15, 0xffffffffffffffff 
sbb rdx, r15
movzx r15, cl
mov [ rsp + 0x640 ], rdx
mov rdx, [ rsp + 0x630 ]
lea r15, [ r15 + rdx ]
mov rdx, rbp
mov rcx, 0xfdc1767ae2ffffff 
sbb rdx, rcx
mov rcx, 0x0 
dec rcx
movzx rdi, dil
adox rdi, rcx
adox r12, [ rsp + 0x618 ]
adox r9, r11
adox r15, rbx
seto r11b
mov rbx, r12
mov rdi, 0x7bc65c783158aea3 
sbb rbx, rdi
mov rcx, r9
mov rdi, 0x6cfc5fd681c52056 
sbb rcx, rdi
mov rdi, r15
mov [ rsp + 0x648 ], rbx
mov rbx, 0x2341f27177344 
sbb rdi, rbx
movzx rbx, r11b
movzx r8, r8b
lea rbx, [ rbx + r8 ]
sbb rbx, 0x00000000
mov rbx, [ rsp + 0x638 ]
cmovc rbx, r13
cmovc rdi, r15
mov r13, [ rsp + 0x628 ]
cmovc r13, r10
cmovc rcx, r9
mov r10, [ rsp + 0x640 ]
cmovc r10, r14
cmovc rdx, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rbx
mov [ r8 + 0x10 ], r10
mov r14, [ rsp + 0x648 ]
cmovc r14, r12
mov [ r8 + 0x20 ], r14
mov [ r8 + 0x28 ], rcx
mov [ r8 + 0x18 ], rdx
mov [ r8 + 0x0 ], r13
mov [ r8 + 0x30 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1744
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3382
; seed 1533427187598446 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 81097 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=29, initial num_batches=31): 1162 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01432852016720717
; number reverted permutation / tried permutation: 251 / 495 =50.707%
; number reverted decision / tried decision: 226 / 504 =44.841%
; validated in 384.958s
