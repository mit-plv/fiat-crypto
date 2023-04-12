SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1496
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
test al, al
adox r14, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], rax
mulx rax, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r12
mulx r12, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r10
mulx r10, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r9
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], rdi
mulx rdi, r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rdi
mov [ rsp + 0x40 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], rdi
mulx rdi, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], r13
mulx r13, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r10
mov [ rsp + 0x70 ], r12
mulx r12, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], r10
mulx r10, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], r8
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], r9
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], rbp
mulx rbp, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], r8
mulx r8, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], rbx
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], rax
mulx rax, r9, rdx
adox rbx, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], rax
mov [ rsp + 0x118 ], r14
mulx r14, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r14
mov [ rsp + 0x128 ], rax
mulx rax, r14, [ rsi + 0x10 ]
adcx r15, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], r15
mulx r15, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], rax
mov [ rsp + 0x140 ], r14
mulx r14, rax, [ rsi + 0x8 ]
adcx rax, rbx
adox r12, rbp
adox r8, r10
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x148 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x150 ], r12
mov [ rsp + 0x158 ], rax
mulx rax, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x160 ], r12
mov [ rsp + 0x168 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], rbx
mulx rbx, r8, rdx
adox r9, r15
setc dl
clc
adcx r12, rbx
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x180 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x188 ], r12
mov [ rsp + 0x190 ], r9
mulx r9, r12, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x198 ], r9
mov r9, -0x2 
inc r9
adox rdi, rax
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x1a0 ], rdi
mulx rdi, r9, r8
mov rdx, 0x2341f27177344 
mov [ rsp + 0x1a8 ], r12
mov [ rsp + 0x1b0 ], rdi
mulx rdi, r12, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1b8 ], rdi
mov [ rsp + 0x1c0 ], r12
mulx r12, rdi, [ rsi + 0x20 ]
adox r11, r13
adox rcx, [ rsp + 0x118 ]
adox rdi, [ rsp + 0x100 ]
adox r12, [ rsp + 0xf8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1c8 ], r12
mulx r12, r13, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], rcx
mulx rcx, rdi, rdx
adcx rbp, [ rsp + 0xe0 ]
adcx r10, [ rsp + 0xc0 ]
mov rdx, r13
mov [ rsp + 0x1e0 ], r11
setc r11b
clc
adcx rdx, r12
mov [ rsp + 0x1e8 ], r10
seto r10b
mov [ rsp + 0x1f0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r15, r15b
adox r15, rbp
adox r14, [ rsp + 0x178 ]
mov r15, r13
adcx r15, r12
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1f8 ], r14
mov [ rsp + 0x200 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xf0 ]
adox rdx, [ rsp + 0x170 ]
mov [ rsp + 0x208 ], r14
setc r14b
clc
adcx r15, [ rsp + 0x90 ]
mov [ rsp + 0x210 ], r15
mov r15, [ rsp + 0x110 ]
mov [ rsp + 0x218 ], rdx
setc dl
clc
mov [ rsp + 0x220 ], rcx
mov rcx, -0x1 
movzx rax, al
adcx rax, rcx
adcx r15, [ rsp + 0xd0 ]
seto al
inc rcx
adox rbx, [ rsp + 0x88 ]
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], rbx
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x190 ]
adox rdx, [ rsp + 0x70 ]
mov [ rsp + 0x238 ], rdx
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp + 0x68 ]
mov [ rsp + 0x240 ], rdx
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x248 ], r11b
mov byte [ rsp + 0x250 ], al
mulx rax, r11, r8
mov rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x258 ], rax
mov rax, 0x0 
adcx rdx, rax
mov rax, [ rsp + 0x18 ]
adox rax, [ rsp + 0x20 ]
clc
mov [ rsp + 0x260 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r12, r9
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, [ rsi + 0x8 ]
adcx r11, [ rsp + 0x1b0 ]
adox r15, [ rsp - 0x10 ]
adox rbx, [ rsp - 0x18 ]
setc dl
clc
adcx r13, r8
adcx rbp, [ rsp + 0x188 ]
seto r13b
mov [ rsp + 0x268 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rdi, [ rsp + 0xb8 ]
seto r10b
inc rbx
adox rbp, [ rsp + 0xd8 ]
mov [ rsp + 0x270 ], rdi
seto dil
mov [ rsp + 0x278 ], r15
mov r15, -0x3 
inc r15
adox r9, [ rsp + 0x0 ]
mov rbx, [ rsp - 0x20 ]
setc r15b
clc
mov [ rsp + 0x280 ], r9
mov r9, -0x1 
movzx rcx, cl
adcx rcx, r9
adcx rbx, [ rsp + 0x50 ]
mov rcx, [ rsp + 0x80 ]
setc r9b
mov [ rsp + 0x288 ], rbx
movzx rbx, byte [ rsp + 0x250 ]
clc
mov [ rsp + 0x290 ], rax
mov rax, -0x1 
adcx rbx, rax
adcx rcx, [ rsp + 0xe8 ]
mov bl, dl
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x298 ], r9b
mulx r9, rax, [ rsi + 0x30 ]
adcx rax, [ rsp + 0x78 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2a0 ], rax
mov [ rsp + 0x2a8 ], rcx
mulx rcx, rax, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2b0 ], rcx
mov [ rsp + 0x2b8 ], rax
mulx rax, rcx, [ rsi + 0x28 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x2c0 ], dil
mov [ rsp + 0x2c8 ], r11
mulx r11, rdi, rbp
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x2d0 ], r11
mov [ rsp + 0x2d8 ], rdi
mulx rdi, r11, rbp
movzx rdx, r13b
mov [ rsp + 0x2e0 ], rdi
mov rdi, [ rsp - 0x28 ]
lea rdx, [ rdx + rdi ]
mov rdi, [ rsp + 0x60 ]
seto r13b
mov [ rsp + 0x2e8 ], rdx
movzx rdx, byte [ rsp + 0x248 ]
mov [ rsp + 0x2f0 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rdx, r11
adox rdi, [ rsp + 0x168 ]
adox rcx, [ rsp + 0x58 ]
setc dl
clc
movzx r13, r13b
adcx r13, r11
adcx r14, [ rsp + 0x140 ]
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2f8 ], r14
mulx r14, r11, rdx
adox rax, [ rsp + 0xb0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x300 ], rax
mov [ rsp + 0x308 ], rcx
mulx rcx, rax, rbp
movzx rdx, r13b
lea rdx, [ rdx + r9 ]
adcx r11, [ rsp + 0x138 ]
movzx r9, r10b
mov r13, [ rsp + 0x220 ]
lea r9, [ r9 + r13 ]
mov r13, [ rsp + 0xa8 ]
mov r10, 0x0 
adox r13, r10
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x310 ], r9
mov [ rsp + 0x318 ], r11
mulx r11, r9, r10
adcx r14, [ rsp - 0x30 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rbx, bl
adox rbx, rdx
adox r9, [ rsp + 0x258 ]
mov rbx, [ rsp + 0x1a8 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, [ rsp + 0x1f0 ]
setc r10b
clc
mov [ rsp + 0x320 ], rbx
mov rbx, -0x1 
movzx r15, r15b
adcx r15, rbx
adcx rdx, [ rsp + 0x200 ]
mov r15, 0xffffffffffffffff 
xchg rdx, rbp
mov [ rsp + 0x328 ], r14
mulx r14, rbx, r15
adox r11, [ rsp + 0x1c0 ]
adcx r12, [ rsp + 0x1e8 ]
adcx rdi, [ rsp + 0x2c8 ]
seto r15b
mov [ rsp + 0x330 ], r8
movzx r8, byte [ rsp + 0x2c0 ]
mov [ rsp + 0x338 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox r8, rcx
adox rbp, [ rsp + 0x130 ]
mov r8, rbx
setc cl
clc
adcx r8, rdx
adox r12, [ rsp + 0x158 ]
mov r8, [ rsp + 0x198 ]
setc dl
clc
mov [ rsp + 0x340 ], rax
mov rax, -0x1 
movzx r10, r10b
adcx r10, rax
adcx r8, [ rsp + 0xa0 ]
mov r10, rbx
seto al
mov [ rsp + 0x348 ], r8
mov r8, -0x2 
inc r8
adox r10, r14
adox rbx, r14
mov r8, [ rsp + 0x98 ]
mov [ rsp + 0x350 ], rdi
mov rdi, 0x0 
adcx r8, rdi
adox r14, [ rsp + 0x2d8 ]
movzx rdi, r15b
mov [ rsp + 0x358 ], r8
mov r8, [ rsp + 0x1b8 ]
lea rdi, [ rdi + r8 ]
clc
mov r8, -0x1 
movzx rcx, cl
adcx rcx, r8
adcx r9, [ rsp + 0x308 ]
seto r15b
inc r8
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox rbp, r10
adcx r11, [ rsp + 0x300 ]
adox rbx, r12
adcx rdi, r13
mov r13, [ rsp + 0x350 ]
setc dl
clc
movzx rax, al
adcx rax, rcx
adcx r13, [ rsp + 0x1f8 ]
adcx r9, [ rsp + 0x218 ]
seto al
mov r12, -0x3 
inc r12
adox rbp, [ rsp + 0x28 ]
mov r10, 0xffffffffffffffff 
xchg rdx, rbp
mulx r12, r8, r10
mov rcx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x360 ], bpl
mulx rbp, r10, rcx
mov rcx, 0x2341f27177344 
mov [ rsp + 0x368 ], rbp
mov [ rsp + 0x370 ], r10
mulx r10, rbp, rcx
adcx r11, [ rsp + 0x2a8 ]
adox rbx, [ rsp + 0x230 ]
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x378 ], r10
mov [ rsp + 0x380 ], rbp
mulx rbp, r10, rcx
mov rcx, r8
mov [ rsp + 0x388 ], rbp
seto bpl
mov [ rsp + 0x390 ], r10
mov r10, -0x2 
inc r10
adox rcx, r12
mov r10, [ rsp + 0x2d0 ]
mov [ rsp + 0x398 ], rdi
setc dil
clc
mov byte [ rsp + 0x3a0 ], bpl
mov rbp, -0x1 
movzx r15, r15b
adcx r15, rbp
adcx r10, [ rsp + 0x2f0 ]
mov r15, 0x7bc65c783158aea3 
mov byte [ rsp + 0x3a8 ], dil
mulx rdi, rbp, r15
mov r15, r8
mov [ rsp + 0x3b0 ], rdi
seto dil
mov [ rsp + 0x3b8 ], rbp
mov rbp, -0x2 
inc rbp
adox r15, rdx
mov r15, [ rsp + 0x2e0 ]
adcx r15, [ rsp + 0x2b8 ]
adox rcx, rbx
seto dl
inc rbp
mov rbx, -0x1 
movzx rax, al
adox rax, rbx
adox r13, r14
mov r14, [ rsp + 0x2b0 ]
adcx r14, [ rsp + 0x340 ]
adox r10, r9
adox r15, r11
mov al, dl
mov rdx, [ rsi + 0x20 ]
mulx r11, r9, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x338 ]
adcx rdx, rbp
movzx rbp, byte [ rsp + 0x3a0 ]
clc
adcx rbp, rbx
adcx r13, [ rsp + 0x238 ]
mov rbp, [ rsp + 0x398 ]
setc bl
mov [ rsp + 0x3c0 ], rdx
movzx rdx, byte [ rsp + 0x3a8 ]
clc
mov [ rsp + 0x3c8 ], rcx
mov rcx, -0x1 
adcx rdx, rcx
adcx rbp, [ rsp + 0x2a0 ]
mov rdx, [ rsp + 0x48 ]
setc cl
mov [ rsp + 0x3d0 ], r13
movzx r13, byte [ rsp + 0x298 ]
clc
mov byte [ rsp + 0x3d8 ], al
mov rax, -0x1 
adcx r13, rax
adcx rdx, [ rsp + 0x10 ]
mov r13, [ rsp + 0x8 ]
adcx r13, [ rsp + 0x40 ]
adcx r9, [ rsp + 0x38 ]
setc al
clc
mov [ rsp + 0x3e0 ], r9
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx r10, [ rsp + 0x240 ]
adcx r15, [ rsp + 0x290 ]
adox r14, rbp
adcx r14, [ rsp + 0x278 ]
mov rbx, r12
seto bpl
inc r9
mov r9, -0x1 
movzx rdi, dil
adox rdi, r9
adox rbx, r8
adox r12, [ rsp + 0x390 ]
mov r8, [ rsp + 0x388 ]
adox r8, [ rsp + 0x3b8 ]
movzx rdi, byte [ rsp + 0x360 ]
setc r9b
clc
mov [ rsp + 0x3e8 ], r13
mov r13, -0x1 
movzx rcx, cl
adcx rcx, r13
adcx rdi, [ rsp + 0x330 ]
setc cl
clc
movzx rax, al
adcx rax, r13
adcx r11, [ rsp + 0x128 ]
mov rax, [ rsp + 0x3b0 ]
adox rax, [ rsp + 0x370 ]
mov r13, [ rsp + 0x120 ]
mov [ rsp + 0x3f0 ], r11
mov r11, 0x0 
adcx r13, r11
movzx r11, byte [ rsp + 0x3d8 ]
clc
mov [ rsp + 0x3f8 ], r13
mov r13, -0x1 
adcx r11, r13
adcx rbx, [ rsp + 0x3d0 ]
mov r11, [ rsp + 0x3c8 ]
seto r13b
mov [ rsp + 0x400 ], rdx
mov rdx, -0x2 
inc rdx
adox r11, [ rsp - 0x8 ]
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x408 ], cl
mov byte [ rsp + 0x410 ], r9b
mulx r9, rcx, r11
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x418 ], r9
mov [ rsp + 0x420 ], rcx
mulx rcx, r9, r11
adcx r12, r10
adox rbx, [ rsp + 0x280 ]
adcx r8, r15
adox r12, [ rsp + 0x2f8 ]
adox r8, [ rsp + 0x318 ]
adcx rax, r14
mov r10, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r15, r11, r10
adox rax, [ rsp + 0x328 ]
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x428 ], rcx
mulx rcx, r10, r14
mov r14, r10
mov [ rsp + 0x430 ], rax
setc al
clc
adcx r14, rcx
mov [ rsp + 0x438 ], r8
mov r8, [ rsp + 0x368 ]
mov [ rsp + 0x440 ], r12
seto r12b
mov [ rsp + 0x448 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r13, r13b
adox r13, r9
adox r8, [ rsp + 0x380 ]
mov r13, [ rsp + 0x378 ]
mov r9, 0x0 
adox r13, r9
dec r9
movzx rbp, bpl
adox rbp, r9
adox rdi, [ rsp + 0x3c0 ]
mov rbp, r10
seto r9b
mov [ rsp + 0x450 ], r13
mov r13, -0x2 
inc r13
adox rbp, rdx
adox r14, rbx
setc bpl
movzx rbx, byte [ rsp + 0x410 ]
clc
adcx rbx, r13
adcx rdi, [ rsp + 0x268 ]
setc bl
clc
movzx rax, al
adcx rax, r13
adcx rdi, r8
mov rax, rcx
setc r8b
clc
movzx rbp, bpl
adcx rbp, r13
adcx rax, r10
adcx r11, rcx
movzx r10, r9b
movzx rcx, byte [ rsp + 0x408 ]
lea r10, [ r10 + rcx ]
seto cl
inc r13
mov rbp, -0x1 
movzx rbx, bl
adox rbx, rbp
adox r10, [ rsp + 0x2e8 ]
setc r9b
clc
movzx r12, r12b
adcx r12, rbp
adcx rdi, [ rsp + 0x320 ]
setc r12b
clc
movzx r9, r9b
adcx r9, rbp
adcx r15, [ rsp + 0x420 ]
mov rbx, [ rsp + 0x448 ]
adcx rbx, [ rsp + 0x418 ]
seto r9b
inc rbp
mov r13, -0x1 
movzx r8, r8b
adox r8, r13
adox r10, [ rsp + 0x450 ]
setc r8b
clc
movzx r12, r12b
adcx r12, r13
adcx r10, [ rsp + 0x348 ]
setc r12b
clc
movzx rcx, cl
adcx rcx, r13
adcx rax, [ rsp + 0x440 ]
setc cl
clc
adcx r14, [ rsp + 0x208 ]
movzx rbp, r9b
mov r13, 0x0 
adox rbp, r13
dec r13
movzx rcx, cl
adox rcx, r13
adox r11, [ rsp + 0x438 ]
adox r15, [ rsp + 0x430 ]
mov r9, 0x2341f27177344 
xchg rdx, r9
mulx r13, rcx, r14
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x458 ], r13
mov [ rsp + 0x460 ], rcx
mulx rcx, r13, r14
adcx rax, [ rsp + 0x210 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x468 ], rcx
mov [ rsp + 0x470 ], r13
mulx r13, rcx, r14
mov rdx, 0x2341f27177344 
mov [ rsp + 0x478 ], r13
mov [ rsp + 0x480 ], rcx
mulx rcx, r13, r9
adcx r11, [ rsp + 0x288 ]
adox rbx, rdi
seto r9b
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox r13, [ rsp + 0x428 ]
seto r8b
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r10, r13
adcx r15, [ rsp + 0x400 ]
adcx rbx, [ rsp + 0x3e8 ]
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r9
mulx r13, r9, r14
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp + 0x488 ], rbx
mulx rbx, rdi, r14
mov rdx, rdi
mov [ rsp + 0x490 ], r15
setc r15b
clc
adcx rdx, r14
mov rdx, rdi
seto r14b
mov [ rsp + 0x498 ], r11
mov r11, -0x2 
inc r11
adox rdx, rbx
adcx rdx, rax
adox rdi, rbx
adox r9, rbx
setc al
clc
movzx r15, r15b
adcx r15, r11
adcx r10, [ rsp + 0x3e0 ]
seto r15b
inc r11
mov rbx, -0x1 
movzx r12, r12b
adox r12, rbx
adox rbp, [ rsp + 0x358 ]
movzx r12, r8b
lea r12, [ r12 + rcx ]
setc cl
clc
movzx r15, r15b
adcx r15, rbx
adcx r13, [ rsp + 0x480 ]
mov r8, [ rsp + 0x478 ]
adcx r8, [ rsp + 0x470 ]
seto r15b
inc rbx
mov r11, -0x1 
movzx r14, r14b
adox r14, r11
adox rbp, r12
setc r14b
clc
movzx rcx, cl
adcx rcx, r11
adcx rbp, [ rsp + 0x3f0 ]
movzx rcx, r15b
adox rcx, rbx
adcx rcx, [ rsp + 0x3f8 ]
mov r15, [ rsp + 0x468 ]
inc r11
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox r15, [ rsp + 0x460 ]
setc r12b
clc
movzx rax, al
adcx rax, rbx
adcx rdi, [ rsp + 0x498 ]
seto al
mov r14, -0x3 
inc r14
adox rdx, [ rsp - 0x40 ]
mov r11, 0xffffffffffffffff 
mulx rbx, r14, r11
mov r11, 0x7bc65c783158aea3 
mov byte [ rsp + 0x4a0 ], r12b
mov [ rsp + 0x4a8 ], rcx
mulx rcx, r12, r11
adox rdi, [ rsp - 0x48 ]
movzx r11, al
mov [ rsp + 0x4b0 ], rdi
mov rdi, [ rsp + 0x458 ]
lea r11, [ r11 + rdi ]
adcx r9, [ rsp + 0x490 ]
adox r9, [ rsp + 0x108 ]
adcx r13, [ rsp + 0x488 ]
mov rdi, r14
seto al
mov [ rsp + 0x4b8 ], r13
mov r13, -0x2 
inc r13
adox rdi, rbx
adcx r8, r10
adcx r15, rbp
mov r10, r14
adox r10, rbx
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4c0 ], r15
mulx r15, r13, rbp
adox r13, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4c8 ], r13
mulx r13, rbp, rbx
adox r12, r15
adox rbp, rcx
mov rcx, 0x2341f27177344 
mulx rbx, r15, rcx
adcx r11, [ rsp + 0x4a8 ]
setc cl
clc
adcx r14, rdx
movzx r14, cl
movzx rdx, byte [ rsp + 0x4a0 ]
lea r14, [ r14 + rdx ]
adox r15, r13
adcx rdi, [ rsp + 0x4b0 ]
setc dl
clc
adcx rdi, [ rsp + 0x160 ]
mov r13, 0x0 
adox rbx, r13
dec r13
movzx rdx, dl
adox rdx, r13
adox r9, r10
mov r10, [ rsp + 0x4b8 ]
seto cl
inc r13
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox r10, [ rsp + 0x150 ]
mov rax, 0x2341f27177344 
mov rdx, rax
mulx r13, rax, rdi
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4d0 ], rbx
mov [ rsp + 0x4d8 ], r13
mulx r13, rbx, rdi
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x4e0 ], r14
mov [ rsp + 0x4e8 ], rax
mulx rax, r14, rdi
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4f0 ], rax
mov [ rsp + 0x4f8 ], r14
mulx r14, rax, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x500 ], r14
mov [ rsp + 0x508 ], rax
mulx rax, r14, rdi
adox r8, [ rsp + 0x148 ]
mov rdx, [ rsp + 0x180 ]
adox rdx, [ rsp + 0x4c0 ]
mov [ rsp + 0x510 ], r13
mov r13, r14
mov [ rsp + 0x518 ], r15
seto r15b
mov [ rsp + 0x520 ], rbx
mov rbx, -0x2 
inc rbx
adox r13, rax
seto bl
mov [ rsp + 0x528 ], r13
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox r10, [ rsp + 0x4c8 ]
adcx r9, [ rsp + 0x1a0 ]
adcx r10, [ rsp + 0x1e0 ]
adox r12, r8
seto cl
inc r13
mov r8, -0x1 
movzx r15, r15b
adox r15, r8
adox r11, [ rsp + 0x228 ]
mov r15, rax
setc r13b
clc
movzx rbx, bl
adcx rbx, r8
adcx r15, r14
seto bl
inc r8
mov r8, -0x1 
movzx rcx, cl
adox rcx, r8
adox rdx, rbp
adcx rax, [ rsp + 0x520 ]
seto bpl
inc r8
adox r14, rdi
adox r9, [ rsp + 0x528 ]
setc r14b
clc
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r11, [ rsp + 0x518 ]
mov rcx, [ rsp + 0x510 ]
setc bpl
clc
movzx r14, r14b
adcx r14, rdi
adcx rcx, [ rsp + 0x4f8 ]
adox r15, r10
mov r10, [ rsp + 0x4f0 ]
adcx r10, [ rsp + 0x508 ]
setc r14b
seto dil
mov [ rsp + 0x530 ], r10
mov r10, r9
mov [ rsp + 0x538 ], r11
mov r11, 0xffffffffffffffff 
sub r10, r11
mov r8, r15
sbb r8, r11
mov r11, [ rsp + 0x500 ]
mov [ rsp + 0x540 ], r8
mov r8, 0x0 
dec r8
movzx r14, r14b
adox r14, r8
adox r11, [ rsp + 0x4e8 ]
setc r14b
clc
movzx r13, r13b
adcx r13, r8
adcx r12, [ rsp + 0x1d8 ]
adcx rdx, [ rsp + 0x1d0 ]
mov r13, [ rsp + 0x4e0 ]
setc r8b
clc
mov [ rsp + 0x548 ], r10
mov r10, -0x1 
movzx rbx, bl
adcx rbx, r10
adcx r13, [ rsp + 0x260 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r10
adcx r12, rax
mov rax, [ rsp + 0x4d8 ]
mov rdi, 0x0 
adox rax, rdi
inc r10
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox r13, [ rsp + 0x4d0 ]
setc bpl
seto r10b
movzx rdi, r14b
add rdi, -0x1
mov rdi, r12
mov r14, 0xffffffffffffffff 
sbb rdi, r14
movzx r14, r10b
movzx rbx, bl
lea r14, [ r14 + rbx ]
mov rbx, -0x1 
inc rbx
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rdx, rcx
seto cl
mov rbp, rdx
mov rbx, 0xfdc1767ae2ffffff 
sbb rbp, rbx
mov r10, [ rsp + 0x1c8 ]
mov rbx, 0x0 
dec rbx
movzx r8, r8b
adox r8, rbx
adox r10, [ rsp + 0x538 ]
adox r13, [ rsp + 0x270 ]
adox r14, [ rsp + 0x310 ]
setc r8b
clc
movzx rcx, cl
adcx rcx, rbx
adcx r10, [ rsp + 0x530 ]
adcx r11, r13
adcx rax, r14
setc cl
seto r13b
movzx r14, r8b
add r14, -0x1
mov r8, r10
mov r14, 0x7bc65c783158aea3 
sbb r8, r14
mov rbx, r11
mov r14, 0x6cfc5fd681c52056 
sbb rbx, r14
mov r14, rax
mov [ rsp + 0x550 ], r8
mov r8, 0x2341f27177344 
sbb r14, r8
movzx r8, cl
movzx r13, r13b
lea r8, [ r8 + r13 ]
sbb r8, 0x00000000
cmovc rbx, r11
cmovc r14, rax
cmovc rdi, r12
mov r8, [ rsp + 0x548 ]
cmovc r8, r9
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rdi
mov [ r9 + 0x0 ], r8
cmovc rbp, rdx
mov [ r9 + 0x18 ], rbp
mov r12, [ rsp + 0x540 ]
cmovc r12, r15
mov [ r9 + 0x28 ], rbx
mov [ r9 + 0x8 ], r12
mov [ r9 + 0x30 ], r14
mov r15, [ rsp + 0x550 ]
cmovc r15, r10
mov [ r9 + 0x20 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1496
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4783
; seed 1342116071872694 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 58166 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 963 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01655606367981295
; number reverted permutation / tried permutation: 319 / 506 =63.043%
; number reverted decision / tried decision: 299 / 493 =60.649%
; validated in 209.603s
