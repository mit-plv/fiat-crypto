SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1480
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
mov rdx, r15
mov [ rsp - 0x48 ], r8
xor r8, r8
adox rdx, rdi
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r12
mulx r12, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r9
mulx r9, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], r12
mulx r12, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r9
mulx r9, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r8
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rcx
mulx rcx, r8, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r8
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], rcx
mulx rcx, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, r15
adcx rdx, r13
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], rcx
mulx rcx, r8, r13
adox r15, rdi
adox r8, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r8
mulx r8, rdi, [ rax + 0x8 ]
setc dl
clc
adcx rdi, r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r15
mulx r15, rcx, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x98 ], r15
mov r15, -0x2 
inc r15
adox r12, rbx
adox r10, r9
mov bl, dl
mov rdx, [ rax + 0x10 ]
mulx r15, r9, [ rsi + 0x0 ]
adox rbp, r11
adcx r9, r8
seto dl
mov r11, -0x1 
inc r11
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rdi, [ rsp + 0x18 ]
adox r9, [ rsp + 0x90 ]
seto r14b
mov r8, -0x3 
inc r8
adox rdi, [ rsp + 0x10 ]
adox r12, r9
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], r8
mov [ rsp + 0xa8 ], r11
mulx r11, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb0 ], rcx
mov [ rsp + 0xb8 ], r11
mulx r11, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0xc0 ], r9b
mov [ rsp + 0xc8 ], r12
mulx r12, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r9
mulx r9, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xe0 ], r9
mov [ rsp + 0xe8 ], r12
mulx r12, r9, [ rsi + 0x0 ]
adcx r9, r15
adcx rcx, r12
adcx r8, r11
mov rdx, 0x7bc65c783158aea3 
mulx r11, r15, r13
setc r12b
clc
mov rdx, -0x1 
movzx rbx, bl
adcx rbx, rdx
adcx r15, [ rsp + 0x88 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mov byte [ rsp + 0xf0 ], r12b
mulx r12, rbx, rdi
adcx r11, [ rsp + 0x38 ]
mov rdx, rbx
mov [ rsp + 0xf8 ], rbp
setc bpl
clc
adcx rdx, r12
mov byte [ rsp + 0x100 ], bpl
mov rbp, rbx
adcx rbp, r12
mov [ rsp + 0x108 ], rbp
setc bpl
clc
mov [ rsp + 0x110 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r9, [ rsp + 0x80 ]
adox r10, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x20 ]
adcx r15, rcx
adcx r11, r8
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x118 ], r11
mov byte [ rsp + 0x120 ], bpl
mulx rbp, r11, [ rsi + 0x20 ]
adox r15, [ rsp + 0xf8 ]
setc dl
clc
adcx rbx, rdi
mov rbx, [ rsp + 0x110 ]
adcx rbx, [ rsp + 0xc8 ]
mov [ rsp + 0x128 ], rbp
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x130 ], r11
mov [ rsp + 0x138 ], r15
mulx r15, r11, [ rax + 0x28 ]
seto dl
mov byte [ rsp + 0x140 ], bpl
movzx rbp, byte [ rsp + 0xc0 ]
mov [ rsp + 0x148 ], r8
mov r8, 0x0 
dec r8
adox rbp, r8
adox r14, [ rsp - 0x28 ]
adox r11, r9
adox rcx, r15
adcx r10, [ rsp + 0x108 ]
setc bpl
clc
adcx rbx, [ rsp - 0x30 ]
mov r9, [ rsp + 0x148 ]
mov r15, 0x0 
adox r9, r15
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x150 ], r9
mulx r9, r8, r15
xchg rdx, rbx
mov [ rsp + 0x158 ], rcx
mov [ rsp + 0x160 ], r11
mulx r11, rcx, r15
mov r15, 0x7bc65c783158aea3 
xchg rdx, rbx
mov [ rsp + 0x168 ], r14
mov byte [ rsp + 0x170 ], dil
mulx rdi, r14, r15
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x178 ], r11
mov [ rsp + 0x180 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r11, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r11
mov [ rsp + 0x190 ], r10
mulx r10, r11, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x198 ], r11
mov byte [ rsp + 0x1a0 ], bpl
mulx rbp, r11, rbx
setc dl
mov [ rsp + 0x1a8 ], r11
movzx r11, byte [ rsp + 0x120 ]
clc
mov [ rsp + 0x1b0 ], rbp
mov rbp, -0x1 
adcx r11, rbp
adcx r12, r8
adox rcx, [ rsp + 0x58 ]
adcx r14, r9
mov r11, 0x6cfc5fd681c52056 
xchg rdx, r15
mulx r9, r8, r11
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r9
mulx r9, r11, [ rax + 0x8 ]
mov rdx, [ rsp - 0x40 ]
adox rdx, [ rsp + 0x50 ]
mov [ rsp + 0x1c0 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], rcx
mulx rcx, r14, rbp
seto bpl
mov rdx, -0x2 
inc rdx
adox r11, r10
adcx r8, rdi
mov rdx, [ rsi + 0x18 ]
mulx r10, rdi, [ rax + 0x10 ]
adox rdi, r9
seto dl
movzx r9, byte [ rsp + 0x1a0 ]
mov [ rsp + 0x1d8 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r9, rdi
adox r12, [ rsp + 0x138 ]
mov r9, [ rsp + 0x1a8 ]
mov rdi, r9
mov [ rsp + 0x1e0 ], rcx
setc cl
clc
adcx rdi, [ rsp + 0x1b0 ]
mov [ rsp + 0x1e8 ], r8
mov r8, [ rsp + 0x190 ]
mov [ rsp + 0x1f0 ], r14
seto r14b
mov byte [ rsp + 0x1f8 ], cl
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox r8, [ rsp + 0x188 ]
adox r12, [ rsp + 0x1d0 ]
mov r15, r9
seto cl
mov byte [ rsp + 0x200 ], r14b
mov r14, -0x2 
inc r14
adox r15, rbx
adox rdi, r8
mov r15b, dl
mov rdx, [ rax + 0x18 ]
mulx r14, r8, [ rsi + 0x18 ]
adcx r9, [ rsp + 0x1b0 ]
mov rdx, [ rsp + 0x1b0 ]
adcx rdx, [ rsp + 0x180 ]
mov [ rsp + 0x208 ], r14
setc r14b
clc
adcx rdi, [ rsp + 0x198 ]
mov [ rsp + 0x210 ], rdx
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x218 ], cl
mov byte [ rsp + 0x220 ], bpl
mulx rbp, rcx, rdi
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x228 ], r8
mov [ rsp + 0x230 ], r10
mulx r10, r8, [ rsi + 0x10 ]
adox r9, r12
mov rdx, rcx
seto r12b
mov [ rsp + 0x238 ], r10
mov r10, -0x2 
inc r10
adox rdx, rbp
adcx r11, r9
mov r9, rcx
adox r9, rbp
mov r10, 0x7bc65c783158aea3 
xchg rdx, r10
mov [ rsp + 0x240 ], r9
mov byte [ rsp + 0x248 ], r12b
mulx r12, r9, rbx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x250 ], r12
mov [ rsp + 0x258 ], r8
mulx r8, r12, r13
setc r13b
clc
adcx rcx, rdi
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x260 ], r13b
mulx r13, rcx, [ rax + 0x0 ]
setc dl
clc
mov [ rsp + 0x268 ], r13
mov r13, -0x1 
movzx r14, r14b
adcx r14, r13
adcx r9, [ rsp + 0x178 ]
setc r14b
clc
movzx rdx, dl
adcx rdx, r13
adcx r11, r10
mov r10, [ rsp + 0x230 ]
setc dl
clc
movzx r15, r15b
adcx r15, r13
adcx r10, [ rsp + 0x228 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, rdi
mov byte [ rsp + 0x270 ], dil
mulx rdi, r13, r15
setc r15b
mov [ rsp + 0x278 ], rdi
movzx rdi, byte [ rsp + 0x100 ]
clc
mov [ rsp + 0x280 ], r13
mov r13, -0x1 
adcx rdi, r13
adcx r12, [ rsp + 0x30 ]
mov rdi, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x288 ], r10
mulx r10, r13, [ rsi + 0x0 ]
mov rdx, [ rsp - 0x48 ]
mov byte [ rsp + 0x290 ], r15b
seto r15b
mov [ rsp + 0x298 ], r9
movzx r9, byte [ rsp + 0x220 ]
mov [ rsp + 0x2a0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r9, r12
adox rdx, [ rsp + 0x258 ]
mov r9, 0x0 
adcx r8, r9
mov r9, rdx
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x2a8 ], r15b
mulx r15, r12, [ rsi + 0x10 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x2b0 ], r15
mov [ rsp + 0x2b8 ], r9
mulx r9, r15, rbx
movzx rdx, byte [ rsp + 0xf0 ]
clc
mov [ rsp + 0x2c0 ], r8
mov r8, -0x1 
adcx rdx, r8
adcx r13, [ rsp + 0xb8 ]
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2c8 ], r10
mulx r10, r8, [ rsi + 0x10 ]
clc
adcx rcx, r11
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2d0 ], r13
mulx r13, r11, rbx
adox r8, [ rsp + 0x238 ]
mov rbx, 0x2341f27177344 
mov rdx, rbx
mov [ rsp + 0x2d8 ], r8
mulx r8, rbx, rcx
setc dl
clc
mov [ rsp + 0x2e0 ], r8
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx r11, [ rsp + 0x250 ]
adcx r15, r13
adox r12, r10
mov r14, [ rsp + 0x118 ]
setc r10b
movzx r13, byte [ rsp + 0x170 ]
clc
adcx r13, r8
adcx r14, [ rsp + 0x168 ]
setc r13b
movzx r8, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x2e8 ], rbx
mov rbx, -0x1 
adcx r8, rbx
adcx r14, [ rsp + 0x1c8 ]
movzx r8, r10b
lea r8, [ r8 + r9 ]
mov r9, [ rsp + 0x2a0 ]
setc r10b
movzx rbx, byte [ rsp + 0x140 ]
clc
mov byte [ rsp + 0x2f0 ], dl
mov rdx, -0x1 
adcx rbx, rdx
adcx r9, [ rsp + 0x2d0 ]
seto bl
inc rdx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox r9, [ rsp + 0x160 ]
mov r13, [ rsp + 0x2c0 ]
adcx r13, [ rsp + 0x2c8 ]
adox r13, [ rsp + 0x158 ]
mov rdx, [ rsp + 0x1b8 ]
mov [ rsp + 0x2f8 ], r8
setc r8b
mov [ rsp + 0x300 ], r15
movzx r15, byte [ rsp + 0x1f8 ]
clc
mov byte [ rsp + 0x308 ], bl
mov rbx, -0x1 
adcx r15, rbx
adcx rdx, [ rsp + 0x1f0 ]
movzx r8, r8b
movzx r15, r8b
adox r15, [ rsp + 0x150 ]
seto r8b
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox r9, [ rsp + 0x1e8 ]
adox rdx, r13
mov r10, [ rsp + 0x1e0 ]
mov r13, 0x0 
adcx r10, r13
adox r10, r15
movzx r15, byte [ rsp + 0x218 ]
clc
adcx r15, rbx
adcx r14, [ rsp + 0x1c0 ]
movzx r15, r8b
adox r15, r13
movzx r8, byte [ rsp + 0x248 ]
inc rbx
mov r13, -0x1 
adox r8, r13
adox r14, [ rsp + 0x210 ]
adcx r9, [ rsp + 0x2b8 ]
adcx rdx, [ rsp + 0x2d8 ]
adcx r12, r10
adox r9, [ rsp + 0x298 ]
adox r11, rdx
movzx r8, byte [ rsp + 0x308 ]
mov r10, [ rsp + 0x2b0 ]
lea r8, [ r8 + r10 ]
adcx r8, r15
adox r12, [ rsp + 0x300 ]
mov r10, [ rsp + 0x208 ]
setc r15b
movzx rdx, byte [ rsp + 0x290 ]
clc
adcx rdx, r13
adcx r10, [ rsp + 0xb0 ]
seto dl
movzx rbx, byte [ rsp + 0x260 ]
inc r13
mov r13, -0x1 
adox rbx, r13
adox r14, [ rsp + 0x1d8 ]
setc bl
clc
movzx rdx, dl
adcx rdx, r13
adcx r8, [ rsp + 0x2f8 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x310 ], r8
mulx r8, r13, rdi
seto dl
mov [ rsp + 0x318 ], r14
movzx r14, byte [ rsp + 0x2a8 ]
mov byte [ rsp + 0x320 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r14, r15
adox rbp, r13
setc r14b
clc
movzx rdx, dl
adcx rdx, r15
adcx r9, [ rsp + 0x288 ]
adcx r10, r11
mov r11, [ rsp + 0x98 ]
seto dl
inc r15
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox r11, [ rsp + 0xa8 ]
mov rbx, [ rsp + 0xa0 ]
adox rbx, [ rsp + 0xd8 ]
adcx r11, r12
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r12
mulx r13, r15, rdi
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x328 ], r11
mov [ rsp + 0x330 ], rbx
mulx rbx, r11, [ rsi + 0x30 ]
setc dl
clc
mov [ rsp + 0x338 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r8, [ rsp + 0x280 ]
adcx r15, [ rsp + 0x278 ]
mov r12, 0x2341f27177344 
xchg rdx, rdi
mov [ rsp + 0x340 ], r15
mulx r15, rbx, r12
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x348 ], dil
mulx rdi, r12, [ rsi + 0x28 ]
adcx rbx, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x350 ], rbx
mulx rbx, r13, [ rax + 0x10 ]
mov rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x358 ], r11
mov r11, 0x0 
adox rdx, r11
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x360 ], rdi
mov [ rsp + 0x368 ], r8
mulx r8, rdi, [ rax + 0x8 ]
mov rdx, [ rsp + 0x130 ]
mov [ rsp + 0x370 ], r11
mov r11, -0x2 
inc r11
adox rdx, [ rsp + 0x268 ]
movzx r11, r14b
mov [ rsp + 0x378 ], r8
movzx r8, byte [ rsp + 0x320 ]
lea r11, [ r11 + r8 ]
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x380 ], r11
mulx r11, r14, [ rsi + 0x28 ]
mov rdx, 0x0 
adcx r15, rdx
adox r13, [ rsp + 0x128 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x388 ], r15
mov [ rsp + 0x390 ], r14
mulx r14, r15, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x398 ], rdi
mov [ rsp + 0x3a0 ], r14
mulx r14, rdi, rcx
adox rbx, [ rsp + 0x48 ]
clc
adcx r12, r11
mov r11, [ rsp + 0x240 ]
seto dl
mov [ rsp + 0x3a8 ], r12
movzx r12, byte [ rsp + 0x270 ]
mov [ rsp + 0x3b0 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r12, rbx
adox r11, [ rsp + 0x318 ]
adox rbp, r9
adox r10, [ rsp + 0x368 ]
mov r12b, dl
mov rdx, [ rax + 0x18 ]
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x3b8 ], r12b
mov [ rsp + 0x3c0 ], rbx
mulx rbx, r12, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x3c8 ], r9
movzx r9, byte [ rsp + 0x2f0 ]
mov [ rsp + 0x3d0 ], rbx
mov rbx, 0x0 
dec rbx
adox r9, rbx
adox r11, r8
adox r13, rbp
mov r9b, dl
mov rdx, [ rax + 0x18 ]
mulx rbp, r8, [ rsi + 0x28 ]
adcx r15, [ rsp + 0x360 ]
mov rdx, rdi
seto bl
mov [ rsp + 0x3d8 ], r15
mov r15, -0x2 
inc r15
adox rdx, r14
adcx r8, [ rsp + 0x3a0 ]
adcx rbp, [ rsp - 0x8 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, rcx
mov [ rsp + 0x3e0 ], rbp
mov [ rsp + 0x3e8 ], r8
mulx r8, rbp, r15
mov r15, [ rsp - 0x10 ]
adcx r15, [ rsp + 0x8 ]
mov [ rsp + 0x3f0 ], r15
mov r15, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x3f8 ], r9b
mov [ rsp + 0x400 ], r8
mulx r8, r9, r15
adcx r12, [ rsp + 0x0 ]
mov r15, rdi
adox r15, r14
adox r9, r14
mov r14, [ rsp + 0x3d0 ]
mov [ rsp + 0x408 ], r12
mov r12, 0x0 
adcx r14, r12
clc
adcx rdi, rdx
adcx rcx, r11
adox rbp, r8
adcx r15, r13
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, r11, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x78 ]
setc r8b
clc
adcx rdx, [ rsp + 0x398 ]
mov r12, [ rsp + 0x378 ]
adcx r12, [ rsp + 0x68 ]
mov [ rsp + 0x410 ], r12
mov r12, [ rsp + 0x60 ]
adcx r12, [ rsp + 0x3c8 ]
mov [ rsp + 0x418 ], r12
seto r12b
mov [ rsp + 0x420 ], rdx
mov rdx, 0x0 
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r10, [ rsp + 0x3b0 ]
setc bl
clc
movzx r8, r8b
adcx r8, rdx
adcx r10, r9
mov r9, [ rsp + 0x3c0 ]
seto r8b
inc rdx
mov rdx, -0x1 
movzx rbx, bl
adox rbx, rdx
adox r9, [ rsp + 0x358 ]
setc bl
clc
adcx rcx, [ rsp + 0x390 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x428 ], r9
mov [ rsp + 0x430 ], r14
mulx r14, r9, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x438 ], r14
mov [ rsp + 0x440 ], r10
mulx r10, r14, rcx
adcx r15, [ rsp + 0x3a8 ]
mov rdx, r14
mov [ rsp + 0x448 ], rbp
setc bpl
clc
adcx rdx, rcx
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x450 ], bpl
mov byte [ rsp + 0x458 ], bl
mulx rbx, rbp, rcx
mov rdx, r14
mov [ rsp + 0x460 ], rbx
setc bl
clc
adcx rdx, r10
mov [ rsp + 0x468 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x470 ], r8b
mov [ rsp + 0x478 ], r13
mulx r13, r8, [ rax + 0x28 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x480 ], r13
mov [ rsp + 0x488 ], r11
mulx r11, r13, rcx
adox r8, [ rsp + 0x338 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x490 ], r8
mov [ rsp + 0x498 ], r11
mulx r11, r8, rdi
seto dil
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox r8, [ rsp + 0x400 ]
adox r11, [ rsp + 0x2e8 ]
mov r12, [ rsp + 0x2e0 ]
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rsp + 0x330 ]
mov [ rsp + 0x4a0 ], r12
movzx r12, byte [ rsp + 0x348 ]
mov [ rsp + 0x4a8 ], r11
mov r11, 0x0 
dec r11
adox r12, r11
adox rdx, [ rsp + 0x310 ]
mov r12, [ rsp + 0x380 ]
adox r12, [ rsp + 0x370 ]
adcx r14, r10
adcx r9, r10
setc r10b
clc
movzx rbx, bl
adcx rbx, r11
adcx r15, rbp
mov rbx, [ rsp + 0x488 ]
setc bpl
movzx r11, byte [ rsp + 0x3b8 ]
clc
mov [ rsp + 0x4b0 ], r9
mov r9, -0x1 
adcx r11, r9
adcx rbx, [ rsp + 0x40 ]
setc r11b
clc
adcx r15, [ rsp + 0x70 ]
mov r9, [ rsp + 0x480 ]
mov [ rsp + 0x4b8 ], r14
setc r14b
clc
mov byte [ rsp + 0x4c0 ], bpl
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx r9, [ rsp - 0x18 ]
mov rdi, [ rsp + 0x478 ]
seto bpl
mov [ rsp + 0x4c8 ], r9
mov r9, 0x0 
dec r9
movzx r11, r11b
adox r11, r9
adox rdi, [ rsp + 0x28 ]
mov r11, [ rsp + 0x340 ]
setc r9b
mov byte [ rsp + 0x4d0 ], r14b
movzx r14, byte [ rsp + 0x3f8 ]
clc
mov [ rsp + 0x4d8 ], r13
mov r13, -0x1 
adcx r14, r13
adcx r11, [ rsp + 0x328 ]
mov r14, [ rsp + 0xe8 ]
adox r14, [ rsp + 0x20 ]
mov r13, [ rsp + 0xe0 ]
mov byte [ rsp + 0x4e0 ], r9b
mov r9, 0x0 
adox r13, r9
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r9
mov byte [ rsp + 0x4e8 ], r10b
mov [ rsp + 0x4f0 ], r13
mulx r13, r10, r15
movzx rdx, byte [ rsp + 0x470 ]
mov [ rsp + 0x4f8 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox r11, rbx
mov rdx, 0x2341f27177344 
mulx r13, rbx, r15
adcx r9, [ rsp + 0x350 ]
adcx r12, [ rsp + 0x388 ]
seto dl
mov [ rsp + 0x500 ], r13
movzx r13, byte [ rsp + 0x458 ]
mov [ rsp + 0x508 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r13, rbx
adox r11, [ rsp + 0x448 ]
movzx r13, bpl
mov rbx, 0x0 
adcx r13, rbx
clc
mov rbp, -0x1 
movzx rdx, dl
adcx rdx, rbp
adcx r9, rdi
adox r8, r9
adcx r14, r12
adcx r13, [ rsp + 0x4f0 ]
mov rdi, 0x7bc65c783158aea3 
mov rdx, rcx
mulx r12, rcx, rdi
mov rdx, [ rsp + 0x440 ]
setc r9b
movzx rbx, byte [ rsp + 0x450 ]
clc
adcx rbx, rbp
adcx rdx, [ rsp + 0x3d8 ]
adcx r11, [ rsp + 0x3e8 ]
adcx r8, [ rsp + 0x3e0 ]
setc bl
movzx rbp, byte [ rsp + 0x4e8 ]
clc
mov rdi, -0x1 
adcx rbp, rdi
adcx rcx, [ rsp + 0x438 ]
adcx r12, [ rsp + 0x468 ]
mov rbp, [ rsp + 0x460 ]
adcx rbp, [ rsp + 0x4d8 ]
adox r14, [ rsp + 0x4a8 ]
adox r13, [ rsp + 0x4a0 ]
setc dil
clc
mov [ rsp + 0x510 ], r10
mov r10, -0x1 
movzx rbx, bl
adcx rbx, r10
adcx r14, [ rsp + 0x3f0 ]
movzx rbx, r9b
mov r10, 0x0 
adox rbx, r10
movzx r9, byte [ rsp + 0x4c0 ]
dec r10
adox r9, r10
adox rdx, [ rsp + 0x4b8 ]
adcx r13, [ rsp + 0x408 ]
adcx rbx, [ rsp + 0x430 ]
adox r11, [ rsp + 0x4b0 ]
adox rcx, r8
movzx r9, dil
mov r8, [ rsp + 0x498 ]
lea r9, [ r9 + r8 ]
adox r12, r14
adox rbp, r13
setc r8b
movzx rdi, byte [ rsp + 0x4d0 ]
clc
adcx rdi, r10
adcx rdx, [ rsp + 0x420 ]
adcx r11, [ rsp + 0x410 ]
mov rdi, 0xffffffffffffffff 
xchg rdx, r15
mulx r13, r14, rdi
adcx rcx, [ rsp + 0x418 ]
adox r9, rbx
movzx rbx, r8b
mov r10, 0x0 
adox rbx, r10
mov r8, r14
mov rdi, -0x3 
inc rdi
adox r8, r13
adcx r12, [ rsp + 0x428 ]
mov rdi, r14
mov [ rsp + 0x518 ], rbx
setc bl
clc
adcx rdi, rdx
mov rdi, 0xfdc1767ae2ffffff 
mov [ rsp + 0x520 ], r9
mulx r9, r10, rdi
adox r14, r13
setc dil
clc
mov [ rsp + 0x528 ], r12
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx rbp, [ rsp + 0x490 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r12
adcx r15, r8
adox r10, r13
mov r13, 0x7bc65c783158aea3 
mulx rdi, r8, r13
adox r8, r9
adcx r14, r11
adox rdi, [ rsp + 0x510 ]
mov rdx, [ rsp + 0x4f8 ]
adox rdx, [ rsp + 0x508 ]
mov r11, [ rsp + 0x500 ]
mov r9, 0x0 
adox r11, r9
movzx r9, byte [ rsp + 0x4e0 ]
mov r12, [ rsp - 0x20 ]
lea r9, [ r9 + r12 ]
adcx r10, rcx
adcx r8, [ rsp + 0x528 ]
mov r12, [ rsp + 0x520 ]
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox r12, [ rsp + 0x4c8 ]
adox r9, [ rsp + 0x518 ]
adcx rdi, rbp
adcx rdx, r12
adcx r11, r9
setc bpl
seto bl
mov r12, r15
mov r9, 0xffffffffffffffff 
sub r12, r9
mov rcx, r14
sbb rcx, r9
mov r13, r10
sbb r13, r9
movzx r9, bpl
movzx rbx, bl
lea r9, [ r9 + rbx ]
mov rbx, r8
mov rbp, 0xfdc1767ae2ffffff 
sbb rbx, rbp
mov rbp, rdi
mov [ rsp + 0x530 ], r13
mov r13, 0x7bc65c783158aea3 
sbb rbp, r13
mov r13, rdx
mov [ rsp + 0x538 ], rbp
mov rbp, 0x6cfc5fd681c52056 
sbb r13, rbp
mov rbp, r11
mov [ rsp + 0x540 ], rcx
mov rcx, 0x2341f27177344 
sbb rbp, rcx
sbb r9, 0x00000000
cmovc rbp, r11
cmovc r12, r15
cmovc r13, rdx
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x28 ], r13
cmovc rbx, r8
mov [ r9 + 0x0 ], r12
mov r15, [ rsp + 0x540 ]
cmovc r15, r14
mov [ r9 + 0x8 ], r15
mov r14, [ rsp + 0x538 ]
cmovc r14, rdi
mov r8, [ rsp + 0x530 ]
cmovc r8, r10
mov [ r9 + 0x10 ], r8
mov [ r9 + 0x20 ], r14
mov [ r9 + 0x30 ], rbp
mov [ r9 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1480
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5806
; seed 1294495793715629 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12147339 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=34, initial num_batches=31): 191949 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01580173237941248
; number reverted permutation / tried permutation: 50254 / 90049 =55.807%
; number reverted decision / tried decision: 42572 / 89950 =47.329%
; validated in 363.735s
