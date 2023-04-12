SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1792
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rdi
mulx rdi, r12, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r14
mulx r14, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r12
mulx r12, r14, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r14
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], rbp
mulx rbp, rbx, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], rbx
mulx rbx, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], rdi
mov [ rsp + 0x50 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r8
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], rcx
mulx rcx, rdi, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rdi
mulx rdi, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], rdi
mov [ rsp + 0xa0 ], rcx
mulx rcx, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], r15
mulx r15, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], rcx
mulx rcx, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xc8 ], rcx
mov [ rsp + 0xd0 ], r15
mulx r15, rcx, [ rsi + 0x30 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], rcx
mulx rcx, r15, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r15
mulx r15, rcx, rdi
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rbp
mulx rbp, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x108 ], rbp
mov [ rsp + 0x110 ], r8
mulx r8, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r8
mov [ rsp + 0x120 ], rbp
mulx rbp, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x128 ], r14
mov [ rsp + 0x130 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r12
mulx r12, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x148 ], r12
mov [ rsp + 0x150 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, rcx
test al, al
adox rdx, r15
adcx r8, r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x158 ], r8
mov [ rsp + 0x160 ], r12
mulx r12, r8, [ rax + 0x8 ]
mov rdx, rcx
adox rdx, r15
mov [ rsp + 0x168 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], r13
mulx r13, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x180 ], r8
mov [ rsp + 0x188 ], r13
mulx r13, r8, [ rsi + 0x10 ]
adcx r10, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x190 ], r10
mulx r10, rbp, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x198 ], r13
mov [ rsp + 0x1a0 ], r8
mulx r8, r13, [ rsi + 0x8 ]
adcx r9, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], r9
mulx r9, r11, [ rax + 0x0 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1b0 ], r11
mov [ rsp + 0x1b8 ], r10
mulx r10, r11, rdi
setc dl
clc
adcx r14, rbx
mov rbx, [ rsp + 0x140 ]
adcx rbx, [ rsp + 0x138 ]
mov [ rsp + 0x1c0 ], rbx
seto bl
mov [ rsp + 0x1c8 ], r14
mov r14, -0x2 
inc r14
adox r8, [ rsp + 0x130 ]
mov r14, [ rsp + 0x100 ]
adox r14, [ rsp + 0x128 ]
mov [ rsp + 0x1d0 ], r14
mov r14, [ rsp + 0xb0 ]
adox r14, [ rsp + 0xf8 ]
mov [ rsp + 0x1d8 ], r14
mov r14, [ rsp + 0x120 ]
mov [ rsp + 0x1e0 ], r8
setc r8b
clc
adcx r14, [ rsp + 0xa8 ]
mov [ rsp + 0x1e8 ], rbp
mov bpl, dl
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x1f0 ], r8b
mov [ rsp + 0x1f8 ], r12
mulx r12, r8, [ rsi + 0x18 ]
setc dl
clc
adcx rcx, rdi
adcx r14, [ rsp + 0x178 ]
setc cl
clc
adcx r8, r9
adcx r12, [ rsp + 0x70 ]
seto r9b
mov [ rsp + 0x200 ], r12
mov r12, -0x2 
inc r12
adox r13, r14
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r14
mov [ rsp + 0x208 ], r8
mulx r8, r12, r13
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x210 ], r8
mov [ rsp + 0x218 ], r12
mulx r12, r8, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x220 ], r12
mov [ rsp + 0x228 ], r8
mulx r8, r12, r13
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x230 ], r8
mov byte [ rsp + 0x238 ], bpl
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x68 ]
mov byte [ rsp + 0x240 ], cl
setc cl
clc
mov [ rsp + 0x248 ], rbp
mov rbp, -0x1 
movzx r14, r14b
adcx r14, rbp
adcx rdx, [ rsp + 0x118 ]
mov r14, [ rsp + 0x60 ]
adcx r14, [ rsp + 0x50 ]
mov rbp, r12
mov [ rsp + 0x250 ], r14
seto r14b
mov [ rsp + 0x258 ], rdx
mov rdx, -0x2 
inc rdx
adox rbp, r13
mov rbp, [ rsp + 0x40 ]
adcx rbp, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x260 ], r14b
mov [ rsp + 0x268 ], rbp
mulx rbp, r14, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x270 ], rbp
mov byte [ rsp + 0x278 ], cl
mulx rcx, rbp, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x280 ], rcx
mov rcx, 0x0 
dec rcx
movzx r9, r9b
adox r9, rcx
adox r8, [ rsp + 0x38 ]
setc r9b
clc
movzx rbx, bl
adcx rbx, rcx
adcx r15, r11
adcx r10, [ rsp + 0xf0 ]
adox r14, [ rsp + 0x248 ]
mov rbx, [ rsp + 0x58 ]
setc r11b
movzx rcx, byte [ rsp + 0x278 ]
clc
mov [ rsp + 0x288 ], r14
mov r14, -0x1 
adcx rcx, r14
adcx rbx, [ rsp + 0x80 ]
mov rcx, [ rsp + 0x258 ]
seto r14b
mov [ rsp + 0x290 ], rbx
movzx rbx, byte [ rsp + 0x240 ]
mov [ rsp + 0x298 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox rbx, r8
adox rcx, [ rsp + 0x1f8 ]
mov bl, dl
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x2a0 ], r11b
mulx r11, r8, [ rax + 0x28 ]
mov rdx, [ rsp + 0x78 ]
adcx rdx, [ rsp + 0x20 ]
adox r15, [ rsp + 0x250 ]
mov byte [ rsp + 0x2a8 ], bl
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x2b0 ], r14b
mov [ rsp + 0x2b8 ], r15
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2c0 ], rbx
mov [ rsp + 0x2c8 ], rcx
mulx rcx, rbx, [ rax + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2d0 ], r15
mov [ rsp + 0x2d8 ], r14
mulx r14, r15, r13
mov rdx, [ rsp + 0x188 ]
mov [ rsp + 0x2e0 ], r14
setc r14b
clc
adcx rdx, [ rsp + 0x170 ]
adox r10, [ rsp + 0x268 ]
mov [ rsp + 0x2e8 ], rdx
seto dl
mov [ rsp + 0x2f0 ], r10
movzx r10, byte [ rsp + 0x238 ]
mov [ rsp + 0x2f8 ], r15
mov r15, 0x0 
dec r15
adox r10, r15
adox rbx, [ rsp + 0x18 ]
seto r10b
movzx r15, byte [ rsp + 0x1f0 ]
mov [ rsp + 0x300 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r15, rbx
adox rbp, [ rsp - 0x10 ]
seto r15b
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rcx, [ rsp + 0x0 ]
seto r10b
inc rbx
mov rbx, -0x1 
movzx r9, r9b
adox r9, rbx
adox r8, [ rsp + 0x108 ]
adox r11, [ rsp + 0x1e8 ]
mov r9b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x308 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x310 ], rcx
mov byte [ rsp + 0x318 ], r10b
mulx r10, rcx, r13
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x320 ], r10
mulx r10, r13, [ rsi + 0x28 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x328 ], r13
seto r13b
mov [ rsp + 0x330 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox rdx, [ rsp + 0x280 ]
setc r15b
clc
adcx r10, [ rsp + 0x2d8 ]
mov rcx, [ rsp + 0x2d0 ]
adcx rcx, [ rsp - 0x30 ]
mov [ rsp + 0x338 ], rcx
mov rcx, [ rsp + 0x1e0 ]
mov [ rsp + 0x340 ], r10
seto r10b
mov [ rsp + 0x348 ], rdx
movzx rdx, byte [ rsp + 0x260 ]
mov byte [ rsp + 0x350 ], r14b
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rdx, r14
adox rcx, [ rsp + 0x2c8 ]
mov rdx, [ rsp + 0x1d0 ]
adox rdx, [ rsp + 0x2b8 ]
mov r14, [ rsp + 0x168 ]
mov [ rsp + 0x358 ], rdx
seto dl
mov [ rsp + 0x360 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox r14, [ rsp + 0xd0 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov [ rsp + 0x368 ], r14
mulx r14, rcx, r15
mov r15, r12
mov byte [ rsp + 0x370 ], dil
setc dil
clc
adcx r15, [ rsp + 0x230 ]
mov [ rsp + 0x378 ], r15
seto r15b
mov byte [ rsp + 0x380 ], r13b
movzx r13, byte [ rsp + 0x2b0 ]
mov byte [ rsp + 0x388 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r13, rdi
adox rbx, [ rsp + 0x270 ]
mov r13, 0x2341f27177344 
mov [ rsp + 0x390 ], rbx
mulx rbx, rdi, r13
seto dl
movzx r13, byte [ rsp + 0x2a0 ]
mov byte [ rsp + 0x398 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r13, r15
adox rcx, [ rsp + 0xe8 ]
movzx r13, dl
lea r13, [ r13 + rbp ]
adox rdi, r14
mov rbp, 0x0 
adox rbx, rbp
inc r15
mov rbp, -0x1 
movzx r9, r9b
adox r9, rbp
adox r8, rcx
adox rdi, r11
mov rdx, [ rsi + 0x28 ]
mulx r11, r9, [ rax + 0x20 ]
adcx r12, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x30 ]
mulx rcx, r14, [ rax + 0x28 ]
mov rdx, [ rsp + 0xa0 ]
setc r15b
clc
movzx r10, r10b
adcx r10, rbp
adcx rdx, [ rsp - 0x38 ]
mov r10, [ rsp + 0xc8 ]
seto bpl
mov [ rsp + 0x3a0 ], rdx
movzx rdx, byte [ rsp + 0x398 ]
mov [ rsp + 0x3a8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rdx, r13
adox r10, [ rsp - 0x20 ]
mov rdx, [ rsp + 0x10 ]
adox rdx, [ rsp - 0x28 ]
adox r14, [ rsp + 0x8 ]
mov r13, [ rsp - 0x40 ]
mov [ rsp + 0x3b0 ], r14
seto r14b
mov [ rsp + 0x3b8 ], rdx
movzx rdx, byte [ rsp + 0x388 ]
mov [ rsp + 0x3c0 ], r10
mov r10, 0x0 
dec r10
adox rdx, r10
adox r13, [ rsp + 0xc0 ]
seto dl
inc r10
mov r10, -0x1 
movzx r14, r14b
adox r14, r10
adox rcx, [ rsp + 0xe0 ]
mov r14, [ rsp + 0x98 ]
adcx r14, [ rsp + 0x150 ]
mov r10b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x3c8 ], rcx
mov [ rsp + 0x3d0 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0x380 ]
mov [ rsp + 0x3d8 ], r14
mov r14, [ rsp + 0x1b8 ]
lea rdx, [ rdx + r14 ]
seto r14b
mov [ rsp + 0x3e0 ], r11
movzx r11, byte [ rsp + 0x350 ]
mov [ rsp + 0x3e8 ], rdi
mov rdi, 0x0 
dec rdi
adox r11, rdi
adox rcx, [ rsp - 0x48 ]
adox r13, [ rsp + 0x30 ]
setc r11b
clc
movzx r10, r10b
adcx r10, rdi
adcx r9, [ rsp + 0xb8 ]
setc r10b
clc
movzx rbp, bpl
adcx rbp, rdi
adcx rdx, rbx
mov rbx, [ rsp + 0x2f8 ]
setc bpl
clc
movzx r15, r15b
adcx r15, rdi
adcx rbx, [ rsp + 0x230 ]
movzx r15, r11b
mov rdi, [ rsp + 0x148 ]
lea r15, [ r15 + rdi ]
mov rdi, [ rsp + 0x360 ]
setc r11b
mov [ rsp + 0x3f0 ], r9
movzx r9, byte [ rsp + 0x2a8 ]
clc
mov [ rsp + 0x3f8 ], r15
mov r15, -0x1 
adcx r9, r15
adcx rdi, [ rsp + 0x378 ]
seto r9b
inc r15
adox rdi, [ rsp + 0x160 ]
mov r15, [ rsp - 0x8 ]
mov [ rsp + 0x400 ], r13
seto r13b
mov [ rsp + 0x408 ], rcx
movzx rcx, byte [ rsp + 0x318 ]
mov byte [ rsp + 0x410 ], bpl
mov rbp, 0x0 
dec rbp
adox rcx, rbp
adox r15, [ rsp + 0x1a0 ]
mov rcx, [ rsp + 0x198 ]
mov rbp, 0x0 
adox rcx, rbp
movzx rbp, r14b
mov [ rsp + 0x418 ], rcx
mov rcx, [ rsp + 0xd8 ]
lea rbp, [ rbp + rcx ]
adcx r12, [ rsp + 0x358 ]
mov rcx, [ rsp + 0x228 ]
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox rcx, [ rsp + 0x2e0 ]
mov r11, [ rsp + 0x218 ]
adox r11, [ rsp + 0x220 ]
mov r14, [ rsp + 0x210 ]
adox r14, [ rsp + 0x330 ]
mov [ rsp + 0x420 ], rbp
mov rbp, [ rsp + 0x1d8 ]
mov [ rsp + 0x428 ], r15
seto r15b
mov [ rsp + 0x430 ], r14
movzx r14, byte [ rsp + 0x370 ]
mov [ rsp + 0x438 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r14, rdx
adox rbp, [ rsp + 0x2f0 ]
setc r14b
clc
movzx r13, r13b
adcx r13, rdx
adcx r12, [ rsp + 0x158 ]
movzx r13, r9b
mov rdx, [ rsp + 0x28 ]
lea r13, [ r13 + rdx ]
adox r8, [ rsp + 0x298 ]
mov rdx, [ rsp + 0x288 ]
adox rdx, [ rsp + 0x3e8 ]
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r9
mov [ rsp + 0x440 ], r13
mov [ rsp + 0x448 ], r12
mulx r12, r13, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x450 ], r12
mov [ rsp + 0x458 ], r13
mulx r13, r12, [ rax + 0x30 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x460 ], r13
mov [ rsp + 0x468 ], r11
mulx r11, r13, rdi
mov rdx, [ rsp + 0x3e0 ]
mov [ rsp + 0x470 ], r11
seto r11b
mov [ rsp + 0x478 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r10, r10b
adox r10, r13
adox rdx, [ rsp + 0x90 ]
movzx r10, r15b
mov r13, [ rsp + 0x320 ]
lea r10, [ r10 + r13 ]
mov r13, 0xffffffffffffffff 
xchg rdx, rdi
mov [ rsp + 0x480 ], rdi
mulx rdi, r15, r13
adox r12, [ rsp + 0x88 ]
seto r13b
mov [ rsp + 0x488 ], r12
mov r12, 0x0 
dec r12
movzx r14, r14b
adox r14, r12
adox rbp, rbx
adox rcx, r8
adox r9, [ rsp + 0x468 ]
adcx rbp, [ rsp + 0x190 ]
adcx rcx, [ rsp + 0x1a8 ]
movzx rbx, r13b
mov r14, [ rsp + 0x460 ]
lea rbx, [ rbx + r14 ]
mov r8, r15
seto r14b
inc r12
adox r8, rdi
mov r13, r15
adox r13, rdi
adcx r9, [ rsp + 0x300 ]
mov [ rsp + 0x490 ], rbx
setc bl
clc
adcx r15, rdx
mov r15, 0x2341f27177344 
mov [ rsp + 0x498 ], r9
mulx r9, r12, r15
adcx r8, [ rsp + 0x448 ]
mov r15, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4a0 ], r10
mov byte [ rsp + 0x4a8 ], bl
mulx rbx, r10, r15
seto dl
mov r15, -0x2 
inc r15
adox r8, [ rsp + 0x1b0 ]
mov r15, 0x2341f27177344 
xchg rdx, r15
mov byte [ rsp + 0x4b0 ], r14b
mov [ rsp + 0x4b8 ], r9
mulx r9, r14, r8
seto dl
mov [ rsp + 0x4c0 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r15, r15b
adox r15, r9
adox rdi, r10
adox rbx, [ rsp + 0x478 ]
mov r15, [ rsp + 0x458 ]
adox r15, [ rsp + 0x470 ]
adcx r13, rbp
adcx rdi, rcx
adox r12, [ rsp + 0x450 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, r8
mulx r10, rcx, rbp
mov r9, [ rsp + 0x438 ]
setc bpl
clc
mov [ rsp + 0x4c8 ], r14
mov r14, -0x1 
movzx r11, r11b
adcx r11, r14
adcx r9, [ rsp + 0x390 ]
setc r11b
clc
movzx r8, r8b
adcx r8, r14
adcx r13, [ rsp + 0x208 ]
mov r8, rcx
setc r14b
clc
adcx r8, rdx
mov r8, [ rsp + 0x4b8 ]
mov [ rsp + 0x4d0 ], r12
mov r12, 0x0 
adox r8, r12
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x4d8 ], r8
mov [ rsp + 0x4e0 ], r13
mulx r13, r8, r12
movzx r12, byte [ rsp + 0x410 ]
mov [ rsp + 0x4e8 ], r13
mov r13, 0x0 
dec r13
movzx r11, r11b
adox r11, r13
adox r12, [ rsp + 0x3a8 ]
setc r11b
movzx r13, byte [ rsp + 0x4b0 ]
clc
mov [ rsp + 0x4f0 ], r8
mov r8, -0x1 
adcx r13, r8
adcx r9, [ rsp + 0x430 ]
seto r13b
movzx r8, byte [ rsp + 0x4a8 ]
mov byte [ rsp + 0x4f8 ], r11b
mov r11, 0x0 
dec r11
adox r8, r11
adox r9, [ rsp + 0x310 ]
adcx r12, [ rsp + 0x4a0 ]
setc r8b
clc
movzx rbp, bpl
adcx rbp, r11
adcx rbx, [ rsp + 0x498 ]
movzx rbp, r8b
movzx r13, r13b
lea rbp, [ rbp + r13 ]
seto r13b
inc r11
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rdi, [ rsp + 0x200 ]
adcx r15, r9
adox rbx, [ rsp + 0x290 ]
mov r14, rcx
setc r9b
clc
adcx r14, r10
adcx rcx, r10
adox r15, [ rsp + 0x2c0 ]
seto r11b
inc r8
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox r12, [ rsp + 0x428 ]
mov r13, 0xfdc1767ae2ffffff 
mov [ rsp + 0x500 ], r15
mulx r15, r8, r13
adcx r8, r10
seto r10b
movzx r13, byte [ rsp + 0x4f8 ]
mov byte [ rsp + 0x508 ], r11b
mov r11, 0x0 
dec r11
adox r13, r11
adox r14, [ rsp + 0x4e0 ]
seto r13b
inc r11
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox r12, [ rsp + 0x4d0 ]
seto r9b
inc r11
adox r14, [ rsp + 0x48 ]
seto r11b
mov byte [ rsp + 0x510 ], r9b
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r13, r13b
adox r13, r9
adox rdi, rcx
setc cl
clc
movzx r11, r11b
adcx r11, r9
adcx rdi, [ rsp + 0x1c8 ]
adox r8, rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mulx r11, r13, r14
mov r9, 0xffffffffffffffff 
mov rdx, r9
mov [ rsp + 0x518 ], rdi
mulx rdi, r9, r14
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x520 ], r8
mov [ rsp + 0x528 ], r11
mulx r11, r8, rbx
mov rbx, r9
seto dl
mov [ rsp + 0x530 ], r11
mov r11, -0x2 
inc r11
adox rbx, rdi
setc r11b
clc
mov [ rsp + 0x538 ], rbx
mov rbx, -0x1 
movzx rcx, cl
adcx rcx, rbx
adcx r15, r8
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r14
mulx rbx, r8, rcx
setc cl
clc
mov byte [ rsp + 0x540 ], r11b
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rbp, [ rsp + 0x418 ]
setc r10b
movzx r11, byte [ rsp + 0x508 ]
clc
mov byte [ rsp + 0x548 ], cl
mov rcx, -0x1 
adcx r11, rcx
adcx r12, [ rsp + 0x408 ]
setc r11b
clc
movzx r14, r14b
adcx r14, rcx
adcx r15, [ rsp + 0x500 ]
setc r14b
movzx rcx, byte [ rsp + 0x510 ]
clc
mov [ rsp + 0x550 ], r12
mov r12, -0x1 
adcx rcx, r12
adcx rbp, [ rsp + 0x4d8 ]
mov rcx, r9
adox rcx, rdi
adox r13, rdi
movzx rdi, r10b
mov r12, 0x0 
adcx rdi, r12
mov r10, 0x6cfc5fd681c52056 
mov [ rsp + 0x558 ], r13
mulx r13, r12, r10
adox r8, [ rsp + 0x528 ]
adox r12, rbx
mov rbx, [ rsp + 0x4f0 ]
movzx r10, byte [ rsp + 0x548 ]
clc
mov [ rsp + 0x560 ], r12
mov r12, -0x1 
adcx r10, r12
adcx rbx, [ rsp + 0x530 ]
seto r10b
inc r12
mov r12, -0x1 
movzx r11, r11b
adox r11, r12
adox rbp, [ rsp + 0x400 ]
adox rdi, [ rsp + 0x440 ]
mov r11, [ rsp + 0x1c0 ]
seto r12b
mov [ rsp + 0x568 ], r8
movzx r8, byte [ rsp + 0x540 ]
mov [ rsp + 0x570 ], rdi
mov rdi, 0x0 
dec rdi
adox r8, rdi
adox r11, [ rsp + 0x520 ]
mov r8, 0x2341f27177344 
mov byte [ rsp + 0x578 ], r12b
mulx r12, rdi, r8
adox r15, [ rsp + 0x308 ]
mov r8, [ rsp + 0x4e8 ]
adcx r8, [ rsp + 0x4c8 ]
mov [ rsp + 0x580 ], r12
seto r12b
mov [ rsp + 0x588 ], r15
mov r15, -0x2 
inc r15
adox r9, rdx
mov r9, [ rsp + 0x4c0 ]
mov rdx, 0x0 
adcx r9, rdx
clc
movzx r14, r14b
adcx r14, r15
adcx rbx, [ rsp + 0x550 ]
seto r14b
inc r15
mov rdx, -0x1 
movzx r10, r10b
adox r10, rdx
adox r13, rdi
mov r10, [ rsp + 0x518 ]
seto dil
inc rdx
mov r15, -0x1 
movzx r14, r14b
adox r14, r15
adox r10, [ rsp + 0x538 ]
adox rcx, r11
setc r11b
clc
movzx r12, r12b
adcx r12, r15
adcx rbx, [ rsp + 0x348 ]
setc r12b
clc
adcx r10, [ rsp + 0x328 ]
setc r14b
clc
movzx r11, r11b
adcx r11, r15
adcx rbp, r8
seto r8b
inc r15
mov rdx, -0x1 
movzx r12, r12b
adox r12, rdx
adox rbp, [ rsp + 0x3a0 ]
mov r11, 0x2341f27177344 
mov rdx, r11
mulx r12, r11, r10
adcx r9, [ rsp + 0x570 ]
mov r15, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp + 0x590 ], r12
mulx r12, r10, r15
adox r9, [ rsp + 0x3d8 ]
mov r15, r10
mov [ rsp + 0x598 ], r11
setc r11b
clc
adcx r15, rdx
mov r15, 0x6cfc5fd681c52056 
mov [ rsp + 0x5a0 ], r13
mov [ rsp + 0x5a8 ], r9
mulx r9, r13, r15
mov r15, 0xfdc1767ae2ffffff 
mov [ rsp + 0x5b0 ], r9
mov [ rsp + 0x5b8 ], r13
mulx r13, r9, r15
mov r15, [ rsp + 0x558 ]
mov [ rsp + 0x5c0 ], r13
seto r13b
mov byte [ rsp + 0x5c8 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox r15, [ rsp + 0x588 ]
mov r8, 0x7bc65c783158aea3 
mov [ rsp + 0x5d0 ], r9
mulx r9, rdi, r8
movzx rdx, r11b
movzx r8, byte [ rsp + 0x578 ]
lea rdx, [ rdx + r8 ]
adox rbx, [ rsp + 0x568 ]
adox rbp, [ rsp + 0x560 ]
setc r8b
clc
mov r11, -0x1 
movzx r13, r13b
adcx r13, r11
adcx rdx, [ rsp + 0x3f8 ]
setc r13b
clc
movzx r14, r14b
adcx r14, r11
adcx rcx, [ rsp + 0x340 ]
adcx r15, [ rsp + 0x338 ]
adcx rbx, [ rsp + 0x3d0 ]
mov r14, r10
setc r11b
clc
adcx r14, r12
mov [ rsp + 0x5d8 ], rbp
seto bpl
mov byte [ rsp + 0x5e0 ], r11b
mov r11, 0x0 
dec r11
movzx r8, r8b
adox r8, r11
adox rcx, r14
seto r8b
inc r11
adox rcx, [ rsp + 0x180 ]
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x5e8 ], r9
mulx r9, r11, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x5f0 ], r9
mov [ rsp + 0x5f8 ], r11
mulx r11, r9, r14
adcx r10, r12
adcx r12, [ rsp + 0x5d0 ]
movzx r14, byte [ rsp + 0x5c8 ]
mov [ rsp + 0x600 ], r9
mov r9, [ rsp + 0x580 ]
lea r14, [ r14 + r9 ]
setc r9b
clc
mov [ rsp + 0x608 ], r11
mov r11, -0x1 
movzx r8, r8b
adcx r8, r11
adcx r15, r10
adcx r12, rbx
adox r15, [ rsp + 0x2e8 ]
mov rbx, [ rsp + 0x5a0 ]
setc r8b
clc
movzx rbp, bpl
adcx rbp, r11
adcx rbx, [ rsp + 0x5a8 ]
mov rbp, 0x6cfc5fd681c52056 
mulx r11, r10, rbp
adcx r14, rcx
seto cl
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox rdi, [ rsp + 0x5c0 ]
movzx r9, r13b
mov rbp, 0x0 
adcx r9, rbp
mov r13, [ rsp + 0x600 ]
mov [ rsp + 0x610 ], r11
mov r11, r13
clc
adcx r11, [ rsp + 0x608 ]
mov rbp, r13
adcx rbp, [ rsp + 0x608 ]
mov [ rsp + 0x618 ], r10
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x620 ], rbp
mov [ rsp + 0x628 ], r9
mulx r9, rbp, r10
mov r10, [ rsp + 0x5f8 ]
adcx r10, [ rsp + 0x608 ]
mov [ rsp + 0x630 ], r9
mov r9, [ rsp + 0x5e8 ]
adox r9, [ rsp + 0x5b8 ]
adcx rbp, [ rsp + 0x5f0 ]
mov [ rsp + 0x638 ], rbp
mov rbp, [ rsp + 0x598 ]
adox rbp, [ rsp + 0x5b0 ]
mov [ rsp + 0x640 ], rbp
setc bpl
clc
adcx r13, rdx
mov r13, [ rsp + 0x5d8 ]
mov byte [ rsp + 0x648 ], bpl
setc bpl
mov [ rsp + 0x650 ], r10
movzx r10, byte [ rsp + 0x5e0 ]
clc
mov [ rsp + 0x658 ], r14
mov r14, -0x1 
adcx r10, r14
adcx r13, [ rsp + 0x3f0 ]
adcx rbx, [ rsp + 0x480 ]
mov r10, [ rsp + 0x590 ]
mov r14, 0x0 
adox r10, r14
dec r14
movzx rbp, bpl
adox rbp, r14
adox r15, r11
seto r11b
inc r14
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox r13, rdi
setc r8b
clc
movzx rcx, cl
adcx rcx, rbp
adcx r12, [ rsp + 0x368 ]
mov rcx, 0x2341f27177344 
mulx r14, rdi, rcx
adox r9, rbx
adcx r13, [ rsp + 0x3c0 ]
adcx r9, [ rsp + 0x3b8 ]
mov rdx, [ rsp + 0x658 ]
seto bl
inc rbp
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox rdx, [ rsp + 0x488 ]
mov r8, [ rsp + 0x490 ]
adox r8, [ rsp + 0x628 ]
seto bpl
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r11, r11b
adox r11, rcx
adox r12, [ rsp + 0x620 ]
adox r13, [ rsp + 0x650 ]
setc r11b
clc
movzx rbx, bl
adcx rbx, rcx
adcx rdx, [ rsp + 0x640 ]
adox r9, [ rsp + 0x638 ]
adcx r10, r8
movzx rbx, bpl
mov r8, 0x0 
adcx rbx, r8
mov rbp, [ rsp + 0x630 ]
movzx r8, byte [ rsp + 0x648 ]
clc
adcx r8, rcx
adcx rbp, [ rsp + 0x618 ]
adcx rdi, [ rsp + 0x610 ]
setc r8b
clc
movzx r11, r11b
adcx r11, rcx
adcx rdx, [ rsp + 0x3b0 ]
adox rbp, rdx
setc r11b
seto dl
mov rcx, r15
mov [ rsp + 0x660 ], rdi
mov rdi, 0xffffffffffffffff 
sub rcx, rdi
mov [ rsp + 0x668 ], rcx
mov rcx, r12
sbb rcx, rdi
movzx rdi, r8b
lea rdi, [ rdi + r14 ]
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox r10, [ rsp + 0x3c8 ]
adox rbx, [ rsp + 0x420 ]
seto r8b
mov r11, r13
mov r14, 0xffffffffffffffff 
sbb r11, r14
mov r14, r9
mov [ rsp + 0x670 ], rcx
mov rcx, 0xfdc1767ae2ffffff 
sbb r14, rcx
mov rcx, rbp
mov [ rsp + 0x678 ], r14
mov r14, 0x7bc65c783158aea3 
sbb rcx, r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox r10, [ rsp + 0x660 ]
adox rdi, rbx
movzx rdx, r8b
mov rbx, 0x0 
adox rdx, rbx
mov r8, r10
mov rbx, 0x6cfc5fd681c52056 
sbb r8, rbx
mov r14, rdi
mov rbx, 0x2341f27177344 
sbb r14, rbx
sbb rdx, 0x00000000
cmovc r11, r13
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r11
cmovc rcx, rbp
mov r13, [ rsp + 0x670 ]
cmovc r13, r12
cmovc r8, r10
mov [ rdx + 0x8 ], r13
mov [ rdx + 0x28 ], r8
cmovc r14, rdi
mov [ rdx + 0x30 ], r14
mov r12, [ rsp + 0x668 ]
cmovc r12, r15
mov [ rdx + 0x20 ], rcx
mov r15, [ rsp + 0x678 ]
cmovc r15, r9
mov [ rdx + 0x0 ], r12
mov [ rdx + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1792
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3987
; seed 0700010143014235 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 59469 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=45, initial num_batches=31): 992 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.016680959827809448
; number reverted permutation / tried permutation: 296 / 489 =60.532%
; number reverted decision / tried decision: 284 / 510 =55.686%
; validated in 205.757s
