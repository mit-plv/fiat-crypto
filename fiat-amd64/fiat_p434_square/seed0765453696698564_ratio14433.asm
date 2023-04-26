SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1560
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r15
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r12
mulx r12, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r14
mulx r14, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r14
mulx r14, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r12
mulx r12, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r12
mov [ rsp + 0x48 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], r13
mov [ rsp + 0x68 ], rbp
mulx rbp, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], rbp
mov [ rsp + 0x78 ], r13
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r13
mulx r13, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r13
mov [ rsp + 0x98 ], rbp
mulx rbp, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], rbp
mov [ rsp + 0xa8 ], r13
mulx r13, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], rbp
mulx rbp, r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], rcx
mov [ rsp + 0xc8 ], rbx
mulx rbx, rcx, [ rsi + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], rcx
mulx rcx, rbx, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rcx
mov [ rsp + 0xe8 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], rcx
mulx rcx, rbx, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x100 ], rcx
mov [ rsp + 0x108 ], r15
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x110 ], r15
mov [ rsp + 0x118 ], rcx
mulx rcx, r15, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rcx
mov [ rsp + 0x128 ], r15
mulx r15, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], rcx
mulx rcx, r15, [ rsi + 0x20 ]
test al, al
adox r8, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x140 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x148 ], r8
mov [ rsp + 0x150 ], r10
mulx r10, r8, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], r10
mov [ rsp + 0x160 ], r8
mulx r8, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x178 ], rcx
mov [ rsp + 0x180 ], r15
mulx r15, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x188 ], r10
mov [ rsp + 0x190 ], r12
mulx r12, r10, [ rsi + 0x10 ]
adox rcx, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], rcx
mulx rcx, r9, [ rsi + 0x30 ]
adox r9, r15
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], r9
mulx r9, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1a8 ], r9
mov [ rsp + 0x1b0 ], r12
mulx r12, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r9
mov [ rsp + 0x1c0 ], r15
mulx r15, r9, [ rsi + 0x10 ]
adcx rdi, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c8 ], rdi
mulx rdi, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1d0 ], r15
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r15, [ rsi + 0x30 ]
adcx r14, rax
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e0 ], r14
mulx r14, rax, rdx
setc dl
clc
adcx r11, rbp
setc bpl
clc
adcx r8, r12
mov r12b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1e8 ], r8
mov [ rsp + 0x1f0 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
adcx r10, rdi
mov rdx, rbx
seto dil
mov [ rsp + 0x1f8 ], r10
mov r10, -0x2 
inc r10
adox rdx, r13
seto dl
inc r10
adox r8, [ rsp + 0x190 ]
mov r10, [ rsp + 0x108 ]
mov [ rsp + 0x200 ], r8
setc r8b
clc
mov [ rsp + 0x208 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx r10, [ rsp + 0xc8 ]
adox r9, rcx
mov rbp, [ rsp + 0xf8 ]
seto cl
inc r15
adox rbp, [ rsp + 0xc0 ]
mov r15, 0x2341f27177344 
xchg rdx, r13
mov [ rsp + 0x210 ], rbp
mov [ rsp + 0x218 ], r9
mulx r9, rbp, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x220 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x228 ], rbp
mov [ rsp + 0x230 ], r10
mulx r10, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x238 ], r10
mov [ rsp + 0x240 ], r11
mulx r11, r10, rdx
adcx rbp, [ rsp + 0x68 ]
mov rdx, [ rsp + 0xf0 ]
adox rdx, [ rsp + 0x48 ]
mov [ rsp + 0x248 ], rdx
mov rdx, [ rsp + 0x58 ]
adox rdx, [ rsp - 0x18 ]
mov [ rsp + 0x250 ], rdx
mov rdx, [ rsp + 0x1d8 ]
mov [ rsp + 0x258 ], rbp
setc bpl
clc
mov byte [ rsp + 0x260 ], r13b
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx rdx, [ rsp + 0x1c0 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x268 ], bpl
mulx rbp, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x270 ], rdi
mov byte [ rsp + 0x278 ], cl
mulx rcx, rdi, rdx
seto dl
mov [ rsp + 0x280 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox r15, [ rsp + 0x1b0 ]
adox r13, r9
setc r8b
clc
adcx r10, [ rsp + 0x88 ]
mov r9, [ rsp + 0x1a8 ]
seto cl
mov [ rsp + 0x288 ], r13
mov r13, 0x0 
dec r13
movzx r8, r8b
adox r8, r13
adox r9, [ rsp + 0xa8 ]
adox rax, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0x188 ]
mov r8, rbx
seto r13b
mov [ rsp + 0x290 ], rax
mov rax, -0x2 
inc rax
adox r8, [ rsp + 0x100 ]
movzx rax, r13b
lea rax, [ rax + r14 ]
mov r14b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x298 ], rax
mulx rax, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2a0 ], r9
mov [ rsp + 0x2a8 ], r15
mulx r15, r9, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x2b0 ], r11
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx rdi, [ rsp + 0x50 ]
setc r14b
clc
movzx r12, r12b
adcx r12, r11
adcx r9, [ rsp + 0x40 ]
seto r12b
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox rbp, [ rsp + 0x138 ]
adox r13, [ rsp + 0x130 ]
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2b8 ], r13
mulx r13, r11, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x1d0 ]
mov [ rsp + 0x2c0 ], rbp
seto bpl
mov [ rsp + 0x2c8 ], rdi
movzx rdi, byte [ rsp + 0x278 ]
mov [ rsp + 0x2d0 ], r9
mov r9, 0x0 
dec r9
adox rdi, r9
adox rdx, [ rsp + 0xb8 ]
adox r11, [ rsp + 0xb0 ]
setc dil
clc
movzx r12, r12b
adcx r12, r9
adcx rbx, [ rsp + 0x100 ]
adox r13, [ rsp + 0x78 ]
seto r12b
movzx r9, byte [ rsp + 0x260 ]
mov [ rsp + 0x2d8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r9, r13
adox r8, [ rsp + 0x240 ]
mov r9, [ rsp + 0x100 ]
adcx r9, [ rsp + 0xe8 ]
mov r13, [ rsp + 0x280 ]
mov [ rsp + 0x2e0 ], r11
setc r11b
clc
mov [ rsp + 0x2e8 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r13, [ rsp + 0x98 ]
mov r14, [ rsp + 0x90 ]
adcx r14, [ rsp + 0xd8 ]
mov rdx, [ rsp + 0x238 ]
mov [ rsp + 0x2f0 ], r14
setc r14b
mov [ rsp + 0x2f8 ], r13
movzx r13, byte [ rsp + 0x268 ]
clc
mov byte [ rsp + 0x300 ], cl
mov rcx, -0x1 
adcx r13, rcx
adcx rdx, [ rsp + 0x28 ]
mov r13, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x118 ]
movzx rcx, bpl
lea rcx, [ rcx + rax ]
mov rax, [ rsp - 0x8 ]
seto bpl
mov [ rsp + 0x308 ], rcx
mov rcx, 0x0 
dec rcx
movzx r12, r12b
adox r12, rcx
adox rax, [ rsp + 0x70 ]
seto r12b
inc rcx
mov rcx, -0x1 
movzx rbp, bpl
adox rbp, rcx
adox rbx, [ rsp + 0x230 ]
adox r9, [ rsp + 0x258 ]
setc bpl
clc
movzx rdi, dil
adcx rdi, rcx
adcx r15, [ rsp + 0x180 ]
mov rdi, [ rsp + 0x18 ]
adcx rdi, [ rsp + 0x170 ]
mov rcx, [ rsp + 0x150 ]
adcx rcx, [ rsp + 0x10 ]
mov byte [ rsp + 0x310 ], r14b
mov r14, [ rsp + 0xe0 ]
mov [ rsp + 0x318 ], rax
seto al
mov [ rsp + 0x320 ], rcx
mov rcx, 0x0 
dec rcx
movzx r11, r11b
adox r11, rcx
adox r14, [ rsp + 0x128 ]
mov r11, [ rsp + 0x160 ]
adox r11, [ rsp + 0x120 ]
mov rcx, [ rsp + 0x158 ]
adox rcx, [ rsp + 0x228 ]
mov [ rsp + 0x328 ], rdi
mov rdi, [ rsp + 0x110 ]
mov [ rsp + 0x330 ], r15
setc r15b
clc
mov [ rsp + 0x338 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rdi, [ rsp - 0x20 ]
movzx rbp, r12b
mov r9, [ rsp - 0x10 ]
lea rbp, [ rbp + r9 ]
setc r9b
clc
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx rdx, r14
adcx r11, r13
adcx rcx, rdi
seto r13b
inc r12
adox r8, [ rsp + 0x80 ]
mov rax, 0x7bc65c783158aea3 
xchg rdx, r8
mulx rdi, r14, rax
adox r10, rbx
mov rbx, [ rsp + 0x338 ]
adox rbx, [ rsp + 0x2b0 ]
movzx r12, r15b
mov rax, [ rsp + 0x148 ]
lea r12, [ r12 + rax ]
mov rax, 0x6cfc5fd681c52056 
mov [ rsp + 0x340 ], rbp
mulx rbp, r15, rax
mov rax, [ rsp + 0x178 ]
mov [ rsp + 0x348 ], r12
setc r12b
mov [ rsp + 0x350 ], rbp
movzx rbp, byte [ rsp + 0x300 ]
clc
mov [ rsp + 0x358 ], rbx
mov rbx, -0x1 
adcx rbp, rbx
adcx rax, [ rsp - 0x28 ]
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x360 ], r15
mulx r15, rbx, rbp
mov rbp, 0x2341f27177344 
mov [ rsp + 0x368 ], rdi
mov [ rsp + 0x370 ], r10
mulx r10, rdi, rbp
movzx rbp, r9b
mov [ rsp + 0x378 ], r10
mov r10, [ rsp - 0x30 ]
lea rbp, [ rbp + r10 ]
movzx r10, r13b
mov r9, [ rsp + 0x220 ]
lea r10, [ r10 + r9 ]
seto r9b
mov r13, 0x0 
dec r13
movzx r12, r12b
adox r12, r13
adox rbp, r10
mov r12, [ rsp - 0x38 ]
adcx r12, [ rsp + 0x8 ]
mov r10, [ rsp + 0x0 ]
adcx r10, [ rsp + 0x38 ]
mov r13, 0xfdc1767ae2ffffff 
mov [ rsp + 0x380 ], rdi
mov [ rsp + 0x388 ], rbp
mulx rbp, rdi, r13
mov r13, rbx
mov [ rsp + 0x390 ], r10
setc r10b
clc
adcx r13, r15
mov byte [ rsp + 0x398 ], r10b
mov r10, rbx
adcx r10, r15
adcx rdi, r15
adcx r14, rbp
seto r15b
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox r8, rax
setc r9b
clc
adcx rbx, rdx
adox r12, r11
adox rcx, [ rsp + 0x390 ]
adcx r13, [ rsp + 0x370 ]
mov rbx, [ rsp + 0x30 ]
setc r11b
movzx rdx, byte [ rsp + 0x398 ]
clc
adcx rdx, rbp
adcx rbx, [ rsp + 0x208 ]
adox rbx, [ rsp + 0x388 ]
seto al
inc rbp
adox r13, [ rsp + 0x168 ]
mov rdx, [ rsp + 0x1f0 ]
adcx rdx, rbp
mov rbp, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x3a0 ], rbx
mov [ rsp + 0x3a8 ], rcx
mulx rcx, rbx, rbp
clc
mov rbp, -0x1 
movzx r15, r15b
movzx rax, al
adcx rax, rbp
adcx r13, r15
mov r15, 0xfdc1767ae2ffffff 
mulx rbp, rax, r15
mov r15, 0x7bc65c783158aea3 
mov [ rsp + 0x3b0 ], r13
mov [ rsp + 0x3b8 ], rbp
mulx rbp, r13, r15
mov r15, 0x6cfc5fd681c52056 
mov [ rsp + 0x3c0 ], rbp
mov [ rsp + 0x3c8 ], r13
mulx r13, rbp, r15
mov r15, [ rsp + 0x360 ]
mov [ rsp + 0x3d0 ], r13
setc r13b
clc
mov [ rsp + 0x3d8 ], rbp
mov rbp, -0x1 
movzx r9, r9b
adcx r9, rbp
adcx r15, [ rsp + 0x368 ]
setc r9b
clc
movzx r11, r11b
adcx r11, rbp
adcx r10, [ rsp + 0x358 ]
adcx rdi, r8
adox r10, [ rsp + 0x1c8 ]
adcx r14, r12
adcx r15, [ rsp + 0x3a8 ]
mov r8, [ rsp + 0x380 ]
setc r12b
clc
movzx r9, r9b
adcx r9, rbp
adcx r8, [ rsp + 0x350 ]
mov r11, rbx
seto r9b
inc rbp
adox r11, rcx
mov [ rsp + 0x3e0 ], r15
mov r15, rbx
mov byte [ rsp + 0x3e8 ], r13b
setc r13b
clc
adcx r15, rdx
adox rbx, rcx
adcx r11, r10
adox rax, rcx
setc r15b
clc
mov rcx, -0x1 
movzx r9, r9b
adcx r9, rcx
adcx rdi, [ rsp + 0x1e0 ]
adcx r14, [ rsp + 0x2d0 ]
mov r9, [ rsp + 0x3b8 ]
adox r9, [ rsp + 0x3c8 ]
seto r10b
dec rbp
movzx r15, r15b
adox r15, rbp
adox rdi, rbx
setc cl
clc
adcx r11, [ rsp + 0x60 ]
adox rax, r14
adcx rdi, [ rsp + 0x200 ]
mov rbx, 0x2341f27177344 
xchg rdx, r11
mulx r14, r15, rbx
movzx rbp, r13b
mov rbx, [ rsp + 0x378 ]
lea rbp, [ rbp + rbx ]
setc bl
clc
mov r13, -0x1 
movzx r12, r12b
adcx r12, r13
adcx r8, [ rsp + 0x3a0 ]
adcx rbp, [ rsp + 0x3b0 ]
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3f0 ], r14
mulx r14, r13, r12
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x3f8 ], r15
mov [ rsp + 0x400 ], r14
mulx r14, r15, r12
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x408 ], r14
mov [ rsp + 0x410 ], r15
mulx r15, r14, r12
mov r12, r14
mov [ rsp + 0x418 ], rdi
seto dil
mov [ rsp + 0x420 ], rbp
mov rbp, -0x2 
inc rbp
adox r12, rdx
mov r12, 0x7bc65c783158aea3 
mov [ rsp + 0x428 ], r8
mulx r8, rbp, r12
movzx rdx, byte [ rsp + 0x3e8 ]
mov r12, 0x0 
adcx rdx, r12
clc
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx rax, [ rsp + 0x218 ]
mov rbx, 0x2341f27177344 
xchg rdx, rbx
mov [ rsp + 0x430 ], r8
mulx r8, r12, r11
mov r11, r14
seto dl
mov [ rsp + 0x438 ], rbx
mov rbx, -0x2 
inc rbx
adox r11, r15
mov rbx, [ rsp + 0x3d8 ]
mov [ rsp + 0x440 ], rax
setc al
clc
mov [ rsp + 0x448 ], rbp
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx rbx, [ rsp + 0x3c0 ]
adox r14, r15
adcx r12, [ rsp + 0x3d0 ]
adox r13, r15
mov r10, 0x0 
adcx r8, r10
mov r15, [ rsp + 0x330 ]
clc
movzx rcx, cl
adcx rcx, rbp
adcx r15, [ rsp + 0x3e0 ]
seto cl
dec r10
movzx rdi, dil
adox rdi, r10
adox r15, r9
mov rbp, [ rsp + 0x428 ]
adcx rbp, [ rsp + 0x328 ]
mov r9, [ rsp + 0x420 ]
adcx r9, [ rsp + 0x320 ]
setc dil
clc
movzx rdx, dl
adcx rdx, r10
adcx r11, [ rsp + 0x418 ]
setc dl
clc
movzx rax, al
adcx rax, r10
adcx r15, [ rsp + 0x2e8 ]
mov rax, [ rsp + 0x448 ]
setc r10b
clc
mov [ rsp + 0x450 ], r11
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx rax, [ rsp + 0x400 ]
setc cl
clc
movzx rdx, dl
adcx rdx, r11
adcx r14, [ rsp + 0x440 ]
adox rbx, rbp
adox r12, r9
adcx r13, r15
mov rbp, [ rsp + 0x438 ]
setc r9b
clc
movzx rdi, dil
adcx rdi, r11
adcx rbp, [ rsp + 0x348 ]
adox r8, rbp
mov rdi, [ rsp + 0x430 ]
seto dl
inc r11
mov r15, -0x1 
movzx rcx, cl
adox rcx, r15
adox rdi, [ rsp + 0x410 ]
mov rcx, [ rsp + 0x3f8 ]
adox rcx, [ rsp + 0x408 ]
mov rbp, [ rsp + 0x3f0 ]
adox rbp, r11
mov r15, [ rsp - 0x40 ]
mov [ rsp + 0x458 ], rbp
mov rbp, -0x3 
inc rbp
adox r15, [ rsp + 0x450 ]
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r11
mov [ rsp + 0x460 ], rcx
mulx rcx, rbp, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x468 ], rcx
mov [ rsp + 0x470 ], rbp
mulx rbp, rcx, r15
adox r14, [ rsp + 0x210 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x478 ], r14
mov [ rsp + 0x480 ], r8
mulx r8, r14, r15
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x488 ], r8
mov [ rsp + 0x490 ], r14
mulx r14, r8, r15
mov rdx, rcx
mov [ rsp + 0x498 ], r14
setc r14b
clc
adcx rdx, rbp
adox r13, [ rsp + 0x248 ]
mov [ rsp + 0x4a0 ], r13
seto r13b
mov [ rsp + 0x4a8 ], rdx
mov rdx, 0x0 
dec rdx
movzx r10, r10b
adox r10, rdx
adox rbx, [ rsp + 0x2e0 ]
movzx r10, r11b
movzx r14, r14b
lea r10, [ r10 + r14 ]
adox r12, [ rsp + 0x2d8 ]
seto r14b
inc rdx
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox rbx, rax
adox rdi, r12
mov rax, [ rsp + 0x318 ]
setc r9b
clc
movzx r14, r14b
adcx r14, r11
adcx rax, [ rsp + 0x480 ]
mov r14, 0x2341f27177344 
mov rdx, r15
mulx r12, r15, r14
mov r11, rbp
seto r14b
mov [ rsp + 0x4b0 ], rdi
mov rdi, 0x0 
dec rdi
movzx r9, r9b
adox r9, rdi
adox r11, rcx
adox rbp, [ rsp + 0x470 ]
adox r8, [ rsp + 0x468 ]
movzx r9, byte [ rsp + 0x310 ]
mov rdi, [ rsp + 0xd0 ]
lea r9, [ r9 + rdi ]
mov rdi, [ rsp + 0x498 ]
adox rdi, [ rsp + 0x490 ]
adox r15, [ rsp + 0x488 ]
adcx r10, [ rsp + 0x340 ]
mov [ rsp + 0x4b8 ], r15
setc r15b
clc
mov [ rsp + 0x4c0 ], rdi
mov rdi, -0x1 
movzx r13, r13b
adcx r13, rdi
adcx rbx, [ rsp + 0x250 ]
mov r13, 0x0 
adox r12, r13
inc rdi
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox rax, [ rsp + 0x460 ]
adox r10, [ rsp + 0x458 ]
mov r14, [ rsp + 0x4b0 ]
adcx r14, [ rsp + 0x2c8 ]
setc r13b
clc
adcx rcx, rdx
movzx rcx, r15b
adox rcx, rdi
mov rdx, [ rsp + 0x4a8 ]
adcx rdx, [ rsp + 0x478 ]
dec rdi
movzx r13, r13b
adox r13, rdi
adox rax, [ rsp + 0x2f8 ]
adox r10, [ rsp + 0x2f0 ]
adcx r11, [ rsp + 0x4a0 ]
seto r15b
inc rdi
adox rdx, [ rsp + 0x1b8 ]
adcx rbp, rbx
mov rbx, 0x6cfc5fd681c52056 
mulx rdi, r13, rbx
adcx r8, r14
mov r14, 0x7bc65c783158aea3 
mov [ rsp + 0x4c8 ], rdi
mulx rdi, rbx, r14
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x4d0 ], r12
mov [ rsp + 0x4d8 ], r10
mulx r10, r12, r14
setc r14b
clc
mov [ rsp + 0x4e0 ], rax
mov rax, -0x1 
movzx r15, r15b
adcx r15, rax
adcx rcx, r9
mov r9, 0xfdc1767ae2ffffff 
mulx rax, r15, r9
mov r9, r12
mov [ rsp + 0x4e8 ], rcx
setc cl
clc
adcx r9, rdx
mov r9, 0x2341f27177344 
mov byte [ rsp + 0x4f0 ], cl
mov byte [ rsp + 0x4f8 ], r14b
mulx r14, rcx, r9
adox r11, [ rsp + 0x1e8 ]
adox rbp, [ rsp + 0x1f8 ]
mov rdx, r12
seto r9b
mov [ rsp + 0x500 ], r14
mov r14, -0x2 
inc r14
adox rdx, r10
adcx rdx, r11
setc r11b
clc
adcx rdx, [ rsp - 0x48 ]
mov r14, 0xfdc1767ae2ffffff 
mov [ rsp + 0x508 ], rcx
mov [ rsp + 0x510 ], r13
mulx r13, rcx, r14
setc r14b
clc
mov [ rsp + 0x518 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx r8, [ rsp + 0x2a8 ]
mov r9, 0x6cfc5fd681c52056 
mov [ rsp + 0x520 ], rcx
mulx rcx, r13, r9
adox r12, r10
adox r15, r10
seto r10b
mov r9, 0x0 
dec r9
movzx r11, r11b
adox r11, r9
adox rbp, r12
seto r11b
inc r9
mov r12, -0x1 
movzx r14, r14b
adox r14, r12
adox rbp, [ rsp + 0x140 ]
setc r14b
clc
movzx r10, r10b
adcx r10, r12
adcx rax, rbx
mov rbx, 0xffffffffffffffff 
mulx r9, r10, rbx
adcx rdi, [ rsp + 0x510 ]
mov r12, 0x2341f27177344 
mov [ rsp + 0x528 ], rdi
mulx rdi, rbx, r12
mov r12, r10
mov [ rsp + 0x530 ], rdi
setc dil
clc
adcx r12, rdx
setc r12b
clc
mov [ rsp + 0x538 ], rbx
mov rbx, -0x1 
movzx r11, r11b
adcx r11, rbx
adcx r8, r15
mov r15, 0x7bc65c783158aea3 
mulx rbx, r11, r15
adox r8, [ rsp + 0x198 ]
mov rdx, r10
seto r15b
mov [ rsp + 0x540 ], rcx
mov rcx, -0x2 
inc rcx
adox rdx, r9
adox r10, r9
setc cl
clc
mov [ rsp + 0x548 ], r13
mov r13, -0x1 
movzx r12, r12b
adcx r12, r13
adcx rbp, rdx
adox r9, [ rsp + 0x520 ]
adcx r10, r8
mov r12, [ rsp + 0x4e0 ]
setc r8b
movzx rdx, byte [ rsp + 0x4f8 ]
clc
adcx rdx, r13
adcx r12, [ rsp + 0x4c0 ]
mov rdx, [ rsp + 0x4b8 ]
adcx rdx, [ rsp + 0x4d8 ]
seto r13b
mov [ rsp + 0x550 ], r9
mov r9, 0x0 
dec r9
movzx r14, r14b
adox r14, r9
adox r12, [ rsp + 0x288 ]
setc r14b
seto r9b
mov byte [ rsp + 0x558 ], r8b
mov r8, rbp
mov [ rsp + 0x560 ], rbx
mov rbx, 0xffffffffffffffff 
sub r8, rbx
mov rbx, [ rsp + 0x4e8 ]
mov [ rsp + 0x568 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rbx, [ rsp + 0x4d0 ]
seto r14b
mov r8, r10
mov [ rsp + 0x570 ], rbx
mov rbx, 0xffffffffffffffff 
sbb r8, rbx
movzx rbx, r14b
mov [ rsp + 0x578 ], r8
movzx r8, byte [ rsp + 0x4f0 ]
lea rbx, [ rbx + r8 ]
mov r8, 0x0 
dec r8
movzx rcx, cl
adox rcx, r8
adox r12, rax
setc al
clc
movzx r15, r15b
adcx r15, r8
adcx r12, [ rsp + 0x1a0 ]
setc cl
clc
movzx r9, r9b
adcx r9, r8
adcx rdx, [ rsp + 0x2c0 ]
setc r15b
clc
movzx r13, r13b
adcx r13, r8
adcx r11, [ rsp + 0x518 ]
mov r13, [ rsp + 0x4c8 ]
seto r9b
inc r8
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox r13, [ rsp + 0x508 ]
mov rdi, [ rsp + 0x560 ]
adcx rdi, [ rsp + 0x548 ]
mov r8, [ rsp + 0x540 ]
adcx r8, [ rsp + 0x538 ]
mov r14, [ rsp + 0x530 ]
mov [ rsp + 0x580 ], r8
mov r8, 0x0 
adcx r14, r8
mov r8, [ rsp + 0x570 ]
clc
mov [ rsp + 0x588 ], r14
mov r14, -0x1 
movzx r15, r15b
adcx r15, r14
adcx r8, [ rsp + 0x2b8 ]
adcx rbx, [ rsp + 0x308 ]
seto r15b
inc r14
mov r14, -0x1 
movzx r9, r9b
adox r9, r14
adox rdx, [ rsp + 0x528 ]
setc r9b
movzx r14, byte [ rsp + 0x558 ]
clc
mov byte [ rsp + 0x590 ], al
mov rax, -0x1 
adcx r14, rax
adcx r12, [ rsp + 0x550 ]
setc r14b
clc
movzx rcx, cl
adcx rcx, rax
adcx rdx, [ rsp + 0x270 ]
adox r13, r8
adcx r13, [ rsp + 0x2a0 ]
movzx rcx, r15b
mov r8, [ rsp + 0x500 ]
lea rcx, [ rcx + r8 ]
adox rcx, rbx
movzx r8, r9b
mov r15, 0x0 
adox r8, r15
inc rax
mov r15, -0x1 
movzx r14, r14b
adox r14, r15
adox rdx, r11
adox rdi, r13
adcx rcx, [ rsp + 0x290 ]
adcx r8, [ rsp + 0x298 ]
setc r11b
seto r9b
movzx rbx, byte [ rsp + 0x590 ]
add rbx, -0x1
mov rbx, r12
mov r14, 0xffffffffffffffff 
sbb rbx, r14
mov r13, rdx
mov rax, 0xfdc1767ae2ffffff 
sbb r13, rax
mov r15, rdi
mov rax, 0x7bc65c783158aea3 
sbb r15, rax
mov r14, 0x0 
dec r14
movzx r9, r9b
adox r9, r14
adox rcx, [ rsp + 0x580 ]
adox r8, [ rsp + 0x588 ]
movzx r9, r11b
mov r14, 0x0 
adox r9, r14
mov r11, rcx
mov r14, 0x6cfc5fd681c52056 
sbb r11, r14
mov r14, r8
mov rax, 0x2341f27177344 
sbb r14, rax
sbb r9, 0x00000000
cmovc r14, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x30 ], r14
cmovc r15, rdi
cmovc r13, rdx
cmovc r11, rcx
mov rdx, [ rsp + 0x578 ]
cmovc rdx, r10
mov [ r9 + 0x28 ], r11
mov r10, [ rsp + 0x568 ]
cmovc r10, rbp
cmovc rbx, r12
mov [ r9 + 0x0 ], r10
mov [ r9 + 0x10 ], rbx
mov [ r9 + 0x8 ], rdx
mov [ r9 + 0x20 ], r15
mov [ r9 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1560
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4433
; seed 0765453696698564 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56248 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 985 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.017511733750533352
; number reverted permutation / tried permutation: 315 / 501 =62.874%
; number reverted decision / tried decision: 289 / 498 =58.032%
; validated in 211.79s
