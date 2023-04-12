SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1712
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r14
mulx r14, rcx, rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rdi
mulx rdi, r15, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], rbp
mulx rbp, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], rbp
mulx rbp, r8, [ rsi + 0x28 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r8
mulx r8, rbp, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], rbp
mulx rbp, r8, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], r8
mulx r8, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], r8
mulx r8, rbp, [ rsi + 0x8 ]
xor rdx, rdx
adox rbp, r14
adox rdi, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r14
mulx r14, r8, [ rsi + 0x28 ]
adox r13, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r14
mulx r14, r9, [ rsi + 0x30 ]
adox rax, r12
adox r11, r10
mov rdx, 0xffffffffffffffff 
mulx r12, r10, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], r8
mulx r8, r9, rcx
mov rdx, r10
adcx rdx, r12
mov [ rsp + 0x98 ], r8
mov r8, r10
adcx r8, r12
mov [ rsp + 0xa0 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], rax
mulx rax, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r13
mulx r13, r14, [ rsi + 0x30 ]
adcx r15, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r13
mulx r13, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r14
mov [ rsp + 0xd8 ], r13
mulx r13, r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], r15
mulx r15, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r15
mov [ rsp + 0xf8 ], r12
mulx r12, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r12
mov [ rsp + 0x108 ], r15
mulx r15, r12, [ rsi + 0x18 ]
setc dl
clc
adcx r10, rcx
seto r10b
mov rcx, -0x2 
inc rcx
adox r14, rax
adcx r9, rbp
adox rbx, r13
adox r12, [ rsp + 0x8 ]
adcx r8, rdi
setc bpl
clc
adcx r11, r9
adox r15, [ rsp + 0x108 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx r13, rax, r11
adcx r14, r8
mov r9, 0x2341f27177344 
mov rdx, r9
mulx r8, r9, r11
mov rcx, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x110 ], r8
mulx r8, r11, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r9
mov byte [ rsp + 0x120 ], r10b
mulx r10, r9, [ rsi + 0x8 ]
mov rdx, r11
mov [ rsp + 0x128 ], r15
setc r15b
clc
adcx rdx, r8
mov [ rsp + 0x130 ], r12
mov r12, r11
mov byte [ rsp + 0x138 ], dil
seto dil
mov [ rsp + 0x140 ], r13
mov r13, -0x2 
inc r13
adox r12, rcx
mov r12, 0x7bc65c783158aea3 
xchg rdx, rcx
mov byte [ rsp + 0x148 ], dil
mulx rdi, r13, r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], r13
mulx r13, rdi, rdx
adox rcx, r14
seto dl
mov r14, -0x2 
inc r14
adox r9, [ rsp + 0x58 ]
adox rdi, r10
adox r13, [ rsp + 0x0 ]
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], r13
mulx r13, r14, [ rsi + 0x8 ]
adcx r11, r8
mov rdx, [ rsp + 0x68 ]
adox rdx, [ rsp - 0x8 ]
mov [ rsp + 0x168 ], rdx
mov rdx, [ rsp + 0xe8 ]
mov [ rsp + 0x170 ], rdi
seto dil
mov [ rsp + 0x178 ], rax
mov rax, 0x0 
dec rax
movzx rbp, bpl
adox rbp, rax
adox rdx, [ rsp + 0xc0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x180 ], dil
mulx rdi, rax, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x188 ], rdi
mov rdi, -0x1 
movzx r15, r15b
adcx r15, rdi
adcx rbp, rbx
seto bl
inc rdi
mov r15, -0x1 
movzx r10, r10b
adox r10, r15
adox rbp, r11
seto r10b
mov r11, -0x3 
inc r11
adox rcx, [ rsp + 0x50 ]
mov dil, dl
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, rdx
adox r9, rbp
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x190 ], r10b
mulx r10, rbp, rcx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x198 ], r10
mov byte [ rsp + 0x1a0 ], bl
mulx rbx, r10, rcx
setc dl
clc
adcx r14, [ rsp + 0xb8 ]
adcx rax, r13
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1a8 ], rbx
mov [ rsp + 0x1b0 ], rax
mulx rax, rbx, [ rsi + 0x20 ]
adcx r11, [ rsp + 0x188 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b8 ], r11
mov [ rsp + 0x1c0 ], r10
mulx r10, r11, [ rsi + 0x18 ]
adcx rbx, r15
mov rdx, [ rsp + 0x60 ]
seto r15b
mov [ rsp + 0x1c8 ], rbx
movzx rbx, byte [ rsp + 0x180 ]
mov [ rsp + 0x1d0 ], r10
mov r10, 0x0 
dec r10
adox rbx, r10
adox rdx, [ rsp - 0x18 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r10
adcx r8, [ rsp + 0x178 ]
mov rdi, [ rsp + 0x140 ]
adcx rdi, [ rsp + 0x158 ]
mov r10, [ rsp + 0x48 ]
mov [ rsp + 0x1d8 ], rdx
seto dl
mov [ rsp + 0x1e0 ], r14
movzx r14, byte [ rsp + 0x138 ]
mov byte [ rsp + 0x1e8 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r14, r15
adox r10, [ rsp - 0x10 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r15, r14
mov r14, r15
mov [ rsp + 0x1f8 ], r8
setc r8b
clc
adcx r14, rdi
mov byte [ rsp + 0x200 ], r8b
mov r8, r15
adcx r8, rdi
mov [ rsp + 0x208 ], r8
seto r8b
mov byte [ rsp + 0x210 ], cl
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox rax, r11
adcx rbp, rdi
setc r11b
clc
adcx r15, rdx
adcx r14, r9
setc r15b
movzx r9, byte [ rsp + 0x1a0 ]
clc
adcx r9, rcx
adcx r10, [ rsp + 0xb0 ]
mov r9, [ rsp + 0x40 ]
seto bl
inc rcx
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox r9, [ rsp + 0x38 ]
adcx r9, [ rsp + 0xa8 ]
seto r8b
dec rcx
movzx r13, r13b
adox r13, rcx
adox r10, [ rsp + 0x130 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r13, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x218 ], rax
mov rax, -0x2 
inc rax
adox r14, [ rsp + 0x90 ]
mov rax, [ rsp - 0x20 ]
mov byte [ rsp + 0x220 ], r8b
seto r8b
mov byte [ rsp + 0x228 ], bl
movzx rbx, byte [ rsp + 0x210 ]
mov [ rsp + 0x230 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rbx, r13
adox rax, [ rsp + 0xe0 ]
setc bl
clc
adcx rcx, [ rsp - 0x28 ]
mov r13, 0x7bc65c783158aea3 
xchg rdx, rdi
mov [ rsp + 0x238 ], rax
mov byte [ rsp + 0x240 ], bl
mulx rbx, rax, r13
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0x248 ], rcx
mov [ rsp + 0x250 ], rbp
mulx rbp, rcx, r13
setc r13b
clc
mov [ rsp + 0x258 ], rbp
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx r9, [ rsp + 0x128 ]
setc dil
clc
movzx r11, r11b
adcx r11, rbp
adcx rax, [ rsp + 0x198 ]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x260 ], r13b
mulx r13, rbp, [ rsi + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x268 ], rax
mov byte [ rsp + 0x270 ], dil
mulx rdi, rax, r11
mov rdx, rax
mov [ rsp + 0x278 ], rcx
setc cl
clc
adcx rdx, rdi
mov [ rsp + 0x280 ], r13
mov r13, rax
adcx r13, rdi
mov [ rsp + 0x288 ], rbp
setc bpl
mov [ rsp + 0x290 ], r13
movzx r13, byte [ rsp + 0x190 ]
clc
mov [ rsp + 0x298 ], rdx
mov rdx, -0x1 
adcx r13, rdx
adcx r10, [ rsp + 0x1f8 ]
adcx r9, [ rsp + 0x1f0 ]
seto r13b
movzx rdx, byte [ rsp + 0x1e8 ]
mov byte [ rsp + 0x2a0 ], bpl
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox rdx, rbp
adox r10, [ rsp + 0x170 ]
seto dl
inc rbp
mov rbp, -0x1 
movzx r15, r15b
adox r15, rbp
adox r10, [ rsp + 0x208 ]
setc r15b
clc
movzx rdx, dl
adcx rdx, rbp
adcx r9, [ rsp + 0x160 ]
setc dl
clc
movzx r8, r8b
adcx r8, rbp
adcx r10, [ rsp + 0x1e0 ]
setc r8b
clc
movzx rcx, cl
adcx rcx, rbp
adcx rbx, [ rsp + 0x1c0 ]
adox r9, [ rsp + 0x250 ]
setc cl
clc
movzx r8, r8b
adcx r8, rbp
adcx r9, [ rsp + 0x1b0 ]
setc r8b
clc
adcx rax, r11
adcx r10, [ rsp + 0x298 ]
setc al
clc
adcx r10, [ rsp + 0x230 ]
setc bpl
clc
mov byte [ rsp + 0x2a8 ], r13b
mov r13, -0x1 
movzx rax, al
adcx rax, r13
adcx r9, [ rsp + 0x290 ]
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x2b0 ], rbx
mulx rbx, r13, r10
mov rdx, [ rsp + 0x1d0 ]
mov [ rsp + 0x2b8 ], rbx
setc bl
mov byte [ rsp + 0x2c0 ], cl
movzx rcx, byte [ rsp + 0x228 ]
clc
mov byte [ rsp + 0x2c8 ], r8b
mov r8, -0x1 
adcx rcx, r8
adcx rdx, [ rsp + 0x288 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x2d0 ], rcx
mulx rcx, r8, r10
mov rdx, r8
mov byte [ rsp + 0x2d8 ], bl
setc bl
clc
adcx rdx, rcx
mov byte [ rsp + 0x2e0 ], al
mov rax, r8
adcx rax, rcx
mov [ rsp + 0x2e8 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x2f0 ], r15b
mov [ rsp + 0x2f8 ], r9
mulx r9, r15, [ rsi + 0x8 ]
movzx rdx, bl
mov [ rsp + 0x300 ], r9
mov r9, [ rsp + 0x280 ]
lea rdx, [ rdx + r9 ]
mov r9, 0x7bc65c783158aea3 
xchg rdx, r9
mov [ rsp + 0x308 ], r9
mulx r9, rbx, r11
adcx r13, rcx
setc cl
movzx rdx, byte [ rsp + 0x2a0 ]
clc
mov [ rsp + 0x310 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx rdi, [ rsp + 0x278 ]
adcx rbx, [ rsp + 0x258 ]
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x318 ], cl
mulx rcx, r13, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x320 ], rcx
mov [ rsp + 0x328 ], r13
mulx r13, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x330 ], rbx
mov [ rsp + 0x338 ], r13
mulx r13, rbx, [ rsi + 0x30 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x340 ], rdi
mov [ rsp + 0x348 ], r9
mulx r9, rdi, r12
mov r12, [ rsp + 0x2f8 ]
seto dl
mov [ rsp + 0x350 ], r9
mov r9, 0x0 
dec r9
movzx rbp, bpl
adox rbp, r9
adox r12, [ rsp + 0x248 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov byte [ rsp + 0x358 ], bpl
mulx rbp, r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x360 ], rbp
mov [ rsp + 0x368 ], r9
mulx r9, rbp, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x30 ]
mov [ rsp + 0x370 ], rdi
seto dil
mov [ rsp + 0x378 ], r15
movzx r15, byte [ rsp + 0x220 ]
mov [ rsp + 0x380 ], r9
mov r9, 0x0 
dec r9
adox r15, r9
adox rdx, [ rsp + 0xa0 ]
seto r15b
inc r9
adox r8, r10
adox rax, r12
setc r8b
clc
adcx rcx, rax
movzx r12, r15b
mov rax, [ rsp + 0x98 ]
lea r12, [ r12 + rax ]
mov rax, 0x7bc65c783158aea3 
xchg rdx, rcx
mulx r9, r15, rax
setc al
mov [ rsp + 0x388 ], r9
movzx r9, byte [ rsp + 0x120 ]
clc
mov [ rsp + 0x390 ], r15
mov r15, -0x1 
adcx r9, r15
adcx rbx, [ rsp - 0x30 ]
mov r9, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x398 ], al
mulx rax, r15, r9
seto r9b
mov [ rsp + 0x3a0 ], rax
movzx rax, byte [ rsp + 0x148 ]
mov byte [ rsp + 0x3a8 ], dil
mov rdi, 0x0 
dec rdi
adox rax, rdi
adox rbp, [ rsp + 0x100 ]
mov rax, 0x0 
adcx r13, rax
mov rax, 0x2341f27177344 
mov byte [ rsp + 0x3b0 ], r9b
mulx r9, rdi, rax
mov rax, [ rsp + 0x380 ]
adox rax, [ rsp + 0x378 ]
mov [ rsp + 0x3b8 ], r9
mov r9, [ rsp + 0x300 ]
mov [ rsp + 0x3c0 ], rdi
mov rdi, 0x0 
adox r9, rdi
mov rdi, 0x2341f27177344 
xchg rdx, rdi
mov [ rsp + 0x3c8 ], r15
mov [ rsp + 0x3d0 ], r9
mulx r9, r15, r11
mov r11, [ rsp + 0x150 ]
add byte [ rsp + 0x200 ], 0x7F
adox r11, [ rsp + 0x370 ]
movzx rdx, byte [ rsp + 0x240 ]
mov [ rsp + 0x3d8 ], r9
mov r9, -0x1 
adcx rdx, r9
adcx rbx, rcx
mov rdx, [ rsp + 0x118 ]
adox rdx, [ rsp + 0x350 ]
adcx r12, r13
seto cl
movzx r13, byte [ rsp + 0x270 ]
inc r9
mov r9, -0x1 
adox r13, r9
adox rbx, rbp
setc r13b
movzx rbp, byte [ rsp + 0x2f0 ]
clc
adcx rbp, r9
adcx rbx, r11
mov rbp, [ rsp + 0x368 ]
seto r11b
inc r9
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox rbp, [ rsp + 0x348 ]
seto r8b
movzx r9, byte [ rsp + 0x2e0 ]
mov [ rsp + 0x3e0 ], rbp
mov rbp, 0x0 
dec rbp
adox r9, rbp
adox rbx, [ rsp + 0x168 ]
seto r9b
movzx rbp, byte [ rsp + 0x358 ]
mov byte [ rsp + 0x3e8 ], cl
mov rcx, 0x0 
dec rcx
adox rbp, rcx
adox rbx, [ rsp + 0x268 ]
seto bpl
movzx rcx, byte [ rsp + 0x2c8 ]
mov byte [ rsp + 0x3f0 ], r9b
mov r9, 0x0 
dec r9
adox rcx, r9
adox rbx, [ rsp + 0x1b8 ]
setc cl
movzx r9, byte [ rsp + 0x2d8 ]
clc
mov byte [ rsp + 0x3f8 ], bpl
mov rbp, -0x1 
adcx r9, rbp
adcx rbx, [ rsp + 0x340 ]
setc r9b
clc
movzx r8, r8b
adcx r8, rbp
adcx r15, [ rsp + 0x360 ]
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x400 ], r15
mulx r15, rbp, [ rsi + 0x28 ]
setc dl
clc
mov [ rsp + 0x408 ], r15
mov r15, -0x1 
movzx r11, r11b
adcx r11, r15
adcx r12, rax
movzx r13, r13b
movzx rax, r13b
adcx rax, [ rsp + 0x3d0 ]
mov r13, 0x2341f27177344 
xchg rdx, r14
mulx r15, r11, r13
seto dl
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox r12, r8
setc r8b
movzx rcx, byte [ rsp + 0x2c0 ]
clc
adcx rcx, r13
adcx r11, [ rsp + 0x1a8 ]
mov cl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x410 ], rbp
mulx rbp, r13, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x418 ], r9b
mov [ rsp + 0x420 ], rbp
mulx rbp, r9, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x428 ], r15
mov [ rsp + 0x430 ], rbx
mulx rbx, r15, [ rsi + 0x28 ]
mov rdx, r9
mov [ rsp + 0x438 ], r13
seto r13b
mov byte [ rsp + 0x440 ], cl
mov rcx, -0x2 
inc rcx
adox rdx, rbp
movzx rcx, r14b
mov [ rsp + 0x448 ], rdx
mov rdx, [ rsp + 0x3d8 ]
lea rcx, [ rcx + rdx ]
setc dl
clc
adcx r15, [ rsp + 0x338 ]
mov r14, r9
adox r14, rbp
mov [ rsp + 0x450 ], r14
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x458 ], rcx
mov [ rsp + 0x460 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x468 ], r15
mov r15, [ rsp + 0x110 ]
lea rdx, [ rdx + r15 ]
adox rbp, [ rsp + 0x3c8 ]
seto r15b
mov [ rsp + 0x470 ], rbp
movzx rbp, byte [ rsp + 0x3f0 ]
mov byte [ rsp + 0x478 ], r14b
mov r14, 0x0 
dec r14
adox rbp, r14
adox r12, [ rsp + 0x1d8 ]
setc bpl
clc
movzx r13, r13b
adcx r13, r14
adcx rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r13, rdx
adox rax, [ rsp + 0x238 ]
seto dl
mov byte [ rsp + 0x480 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rbp, bpl
adox rbp, r15
adox rbx, [ rsp - 0x38 ]
movzx rbp, r8b
mov r15, 0x0 
adcx rbp, r15
adox rcx, [ rsp - 0x40 ]
mov r8b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x488 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
movzx rdx, byte [ rsp + 0x3f8 ]
clc
mov [ rsp + 0x490 ], r14
mov r14, -0x1 
adcx rdx, r14
adcx r12, [ rsp + 0x2b0 ]
adcx r11, rax
setc dl
movzx rax, byte [ rsp + 0x440 ]
clc
adcx rax, r14
adcx r12, [ rsp + 0x1c8 ]
mov rax, [ rsp + 0x438 ]
seto r14b
mov [ rsp + 0x498 ], rbx
movzx rbx, byte [ rsp + 0x260 ]
mov [ rsp + 0x4a0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox rbx, r12
adox rax, [ rsp - 0x48 ]
mov bl, dl
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x4a8 ], r14b
mulx r14, r12, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x4b0 ], r13
mov r13, [ rsp + 0xd8 ]
lea rdx, [ rdx + r13 ]
seto r13b
mov [ rsp + 0x4b8 ], r14
movzx r14, byte [ rsp + 0x3a8 ]
mov [ rsp + 0x4c0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r14, r12
adox rax, [ rsp + 0x430 ]
setc r14b
clc
adcx r9, rdi
seto r9b
movzx r12, byte [ rsp + 0x3b0 ]
mov byte [ rsp + 0x4c8 ], r13b
mov r13, 0x0 
dec r13
adox r12, r13
adox rax, [ rsp + 0x2e8 ]
setc r12b
movzx r13, byte [ rsp + 0x398 ]
clc
mov byte [ rsp + 0x4d0 ], r9b
mov r9, -0x1 
adcx r13, r9
adcx rax, [ rsp + 0x460 ]
seto r13b
inc r9
mov r9, -0x1 
movzx r12, r12b
adox r12, r9
adox rax, [ rsp + 0x448 ]
seto r12b
inc r9
adox r15, [ rsp + 0x18 ]
setc r9b
clc
mov [ rsp + 0x4d8 ], r15
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx rbp, rdx
movzx r8, byte [ rsp + 0x478 ]
mov rdx, [ rsp + 0x428 ]
lea r8, [ r8 + rdx ]
setc dl
clc
movzx r14, r14b
adcx r14, r15
adcx r11, [ rsp + 0x218 ]
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r10
mov byte [ rsp + 0x4e0 ], r12b
mulx r12, r15, r14
setc r14b
clc
mov [ rsp + 0x4e8 ], r12
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx rbp, r8
adox rcx, [ rsp + 0x88 ]
setc bl
clc
adcx rax, [ rsp + 0x10 ]
mov r8, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov [ rsp + 0x4f0 ], rcx
mulx rcx, r12, rax
mov rdx, [ rsp + 0x4c0 ]
mov [ rsp + 0x4f8 ], rcx
seto cl
mov [ rsp + 0x500 ], r12
movzx r12, byte [ rsp + 0x4c8 ]
mov [ rsp + 0x508 ], rbp
mov rbp, 0x0 
dec rbp
adox r12, rbp
adox rdx, [ rsp + 0x420 ]
mov r12, [ rsp + 0x4b0 ]
adox r12, [ rsp + 0x4b8 ]
mov rbp, [ rsp + 0x4a0 ]
mov byte [ rsp + 0x510 ], cl
seto cl
mov byte [ rsp + 0x518 ], r14b
movzx r14, byte [ rsp + 0x418 ]
mov byte [ rsp + 0x520 ], r10b
mov r10, 0x0 
dec r10
adox r14, r10
adox rbp, [ rsp + 0x330 ]
setc r14b
movzx r10, byte [ rsp + 0x4d0 ]
clc
mov byte [ rsp + 0x528 ], cl
mov rcx, -0x1 
adcx r10, rcx
adcx rbp, rdx
mov r10, 0x2341f27177344 
mov rdx, r10
mulx rcx, r10, rax
adox r11, [ rsp + 0x3e0 ]
adcx r12, r11
mov r11, [ rsp + 0x2b8 ]
setc dl
mov [ rsp + 0x530 ], rcx
movzx rcx, byte [ rsp + 0x318 ]
clc
mov [ rsp + 0x538 ], r10
mov r10, -0x1 
adcx rcx, r10
adcx r11, [ rsp + 0x328 ]
adcx r15, [ rsp + 0x320 ]
seto cl
inc r10
mov r10, -0x1 
movzx r13, r13b
adox r13, r10
adox rbp, [ rsp + 0x310 ]
mov r13, 0x2341f27177344 
xchg rdx, r13
mov byte [ rsp + 0x540 ], r14b
mulx r14, r10, r8
adox r11, r12
setc r8b
clc
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx rbp, [ rsp + 0x498 ]
mov rdx, [ rsi + 0x28 ]
mulx r12, r9, rdx
mov rdx, [ rsp + 0x410 ]
mov [ rsp + 0x548 ], r14
setc r14b
mov [ rsp + 0x550 ], r12
movzx r12, byte [ rsp + 0x4a8 ]
clc
mov [ rsp + 0x558 ], r11
mov r11, -0x1 
adcx r12, r11
adcx rdx, [ rsp + 0x468 ]
movzx r12, bl
movzx r11, byte [ rsp + 0x520 ]
lea r12, [ r12 + r11 ]
adcx r9, [ rsp + 0x408 ]
mov r11, [ rsp + 0x508 ]
seto bl
mov [ rsp + 0x560 ], r9
movzx r9, byte [ rsp + 0x518 ]
mov [ rsp + 0x568 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r9, rdx
adox r11, [ rsp + 0x2d0 ]
adox r12, [ rsp + 0x308 ]
setc r9b
clc
movzx r8, r8b
adcx r8, rdx
adcx r10, [ rsp + 0x4e8 ]
mov r8, [ rsp + 0x28 ]
seto dl
mov byte [ rsp + 0x570 ], r9b
movzx r9, byte [ rsp + 0x528 ]
mov [ rsp + 0x578 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r9, r10
adox r8, [ rsp + 0x490 ]
mov r9b, dl
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x580 ], r14b
mulx r14, r10, [ rsi + 0x20 ]
adox r10, [ rsp + 0x20 ]
mov rdx, 0x0 
adox r14, rdx
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r11, [ rsp + 0x400 ]
adox r12, [ rsp + 0x458 ]
setc cl
clc
movzx r13, r13b
adcx r13, rdx
adcx r11, r8
adcx r10, r12
setc r13b
clc
movzx rbx, bl
adcx rbx, rdx
adcx r11, r15
movzx r15, r9b
mov rbx, 0x0 
adox r15, rbx
movzx r9, byte [ rsp + 0x4e0 ]
inc rdx
mov rbx, -0x1 
adox r9, rbx
adox rbp, [ rsp + 0x450 ]
mov r9, [ rsp + 0x558 ]
seto r8b
movzx r12, byte [ rsp + 0x580 ]
dec rdx
adox r12, rdx
adox r9, [ rsp + 0x488 ]
seto bl
inc rdx
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox r15, r14
seto r14b
inc r12
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r9, [ rsp + 0x470 ]
adcx r10, [ rsp + 0x578 ]
setc r13b
movzx r8, byte [ rsp + 0x540 ]
clc
adcx r8, rdx
adcx rbp, [ rsp + 0x4d8 ]
mov r8, 0xffffffffffffffff 
mov rdx, rax
mulx r12, rax, r8
mov r8, [ rsp + 0x80 ]
mov byte [ rsp + 0x588 ], r14b
seto r14b
mov [ rsp + 0x590 ], r10
movzx r10, byte [ rsp + 0x510 ]
mov [ rsp + 0x598 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r10, r15
adox r8, [ rsp + 0xf8 ]
mov r10, rax
setc r15b
clc
adcx r10, r12
mov [ rsp + 0x5a0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x5a8 ], r14b
mov byte [ rsp + 0x5b0 ], r13b
mulx r13, r14, [ rsi + 0x30 ]
adox r14, [ rsp + 0xf0 ]
mov rdx, rax
mov [ rsp + 0x5b8 ], r14
setc r14b
clc
adcx rdx, r8
seto dl
mov byte [ rsp + 0x5c0 ], cl
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox r9, [ rsp + 0x4f0 ]
adcx r10, rbp
mov rbp, r12
setc r15b
clc
movzx r14, r14b
adcx r14, rcx
adcx rbp, rax
mov rax, [ rsp + 0x78 ]
setc r14b
movzx rcx, byte [ rsp + 0x570 ]
clc
mov [ rsp + 0x5c8 ], r10
mov r10, -0x1 
adcx rcx, r10
adcx rax, [ rsp + 0x550 ]
mov cl, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x5d0 ], rbp
mulx rbp, r10, rdx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x5d8 ], r9
mov byte [ rsp + 0x5e0 ], r15b
mulx r15, r9, rdi
seto dil
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r14, r14b
adox r14, rdx
adox r12, [ rsp + 0x500 ]
mov r14, [ rsp + 0x3a0 ]
seto dl
mov [ rsp + 0x5e8 ], r12
movzx r12, byte [ rsp + 0x480 ]
mov byte [ rsp + 0x5f0 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r12, rdi
adox r14, [ rsp + 0x390 ]
setc r12b
clc
movzx rcx, cl
adcx rcx, rdi
adcx r13, [ rsp + 0xd0 ]
adcx r10, [ rsp + 0xc8 ]
movzx rcx, r12b
mov rdi, [ rsp + 0x70 ]
lea rcx, [ rcx + rdi ]
mov rdi, 0x0 
adcx rbp, rdi
clc
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx r11, [ rsp + 0x568 ]
adox r9, [ rsp + 0x388 ]
movzx rbx, byte [ rsp + 0x5c0 ]
mov rdi, [ rsp + 0x548 ]
lea rbx, [ rbx + rdi ]
adox r15, [ rsp + 0x3c0 ]
setc dil
movzx r12, byte [ rsp + 0x5b0 ]
clc
mov [ rsp + 0x5f8 ], rbp
mov rbp, -0x1 
adcx r12, rbp
adcx rbx, [ rsp + 0x598 ]
mov r12, 0x7bc65c783158aea3 
xchg rdx, r12
mov [ rsp + 0x600 ], r10
mulx r10, rbp, r8
mov rdx, [ rsp + 0x560 ]
mov [ rsp + 0x608 ], r13
setc r13b
clc
mov [ rsp + 0x610 ], r10
mov r10, -0x1 
movzx rdi, dil
adcx rdi, r10
adcx rdx, [ rsp + 0x590 ]
adcx rax, rbx
movzx rdi, r13b
movzx rbx, byte [ rsp + 0x588 ]
lea rdi, [ rdi + rbx ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, r8
mulx r10, r13, rbx
seto dl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r12, r12b
adox r12, rbx
adox rbp, [ rsp + 0x4f8 ]
setc r12b
movzx rbx, byte [ rsp + 0x5a8 ]
clc
mov [ rsp + 0x618 ], rbp
mov rbp, -0x1 
adcx rbx, rbp
adcx r11, r14
adcx r9, r8
seto bl
inc rbp
mov r14, -0x1 
movzx r12, r12b
adox r12, r14
adox rdi, rcx
adcx r15, rax
movzx rcx, dl
mov r8, [ rsp + 0x3b8 ]
lea rcx, [ rcx + r8 ]
adcx rcx, rdi
setc r8b
movzx rdx, byte [ rsp + 0x5f0 ]
clc
adcx rdx, r14
adcx r11, [ rsp + 0x5a0 ]
movzx rdx, r8b
adox rdx, rbp
adcx r9, [ rsp + 0x5b8 ]
dec rbp
movzx rbx, bl
adox rbx, rbp
adox r13, [ rsp + 0x610 ]
adcx r15, [ rsp + 0x608 ]
adox r10, [ rsp + 0x538 ]
mov r14, [ rsp + 0x5d0 ]
seto r12b
movzx rax, byte [ rsp + 0x5e0 ]
inc rbp
mov rbx, -0x1 
adox rax, rbx
adox r14, [ rsp + 0x5d8 ]
adox r11, [ rsp + 0x5e8 ]
movzx rax, r12b
mov rdi, [ rsp + 0x530 ]
lea rax, [ rax + rdi ]
adox r9, [ rsp + 0x618 ]
adcx rcx, [ rsp + 0x600 ]
adox r13, r15
adox r10, rcx
adcx rdx, [ rsp + 0x5f8 ]
adox rax, rdx
setc dil
seto r8b
mov r15, [ rsp + 0x5c8 ]
mov r12, 0xffffffffffffffff 
sub r15, r12
mov rcx, r14
sbb rcx, r12
mov rdx, r11
sbb rdx, r12
mov rbp, r9
mov rbx, 0xfdc1767ae2ffffff 
sbb rbp, rbx
mov r12, r13
mov rbx, 0x7bc65c783158aea3 
sbb r12, rbx
mov rbx, r10
mov [ rsp + 0x620 ], rdx
mov rdx, 0x6cfc5fd681c52056 
sbb rbx, rdx
mov rdx, rax
mov [ rsp + 0x628 ], rbx
mov rbx, 0x2341f27177344 
sbb rdx, rbx
movzx rbx, r8b
movzx rdi, dil
lea rbx, [ rbx + rdi ]
sbb rbx, 0x00000000
cmovc rbp, r9
cmovc r12, r13
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], rbp
cmovc rdx, rax
mov [ rbx + 0x30 ], rdx
cmovc r15, [ rsp + 0x5c8 ]
cmovc rcx, r14
mov r14, [ rsp + 0x620 ]
cmovc r14, r11
mov r11, [ rsp + 0x628 ]
cmovc r11, r10
mov [ rbx + 0x28 ], r11
mov [ rbx + 0x10 ], r14
mov [ rbx + 0x0 ], r15
mov [ rbx + 0x20 ], r12
mov [ rbx + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1712
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3267
; seed 3696242665837758 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12655799 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 199087 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01573089142771626
; number reverted permutation / tried permutation: 45272 / 90079 =50.258%
; number reverted decision / tried decision: 39209 / 89920 =43.604%
; validated in 332.98s
