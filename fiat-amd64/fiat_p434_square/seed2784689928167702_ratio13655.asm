SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1640
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], rax
mulx rax, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rbp
mulx rbp, r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rbp
mov [ rsp + 0x8 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r9
mulx r9, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], r8
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], r14
mulx r14, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], r8
mulx r8, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], r12
mulx r12, r13, [ rsi + 0x10 ]
test al, al
adox r11, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r9
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r12
mulx r12, r9, r14
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], r9
mulx r9, r12, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], r13
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r9
mulx r9, r13, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r13
mulx r13, r9, r14
mov rdx, r9
adcx rdx, r13
mov [ rsp + 0xb8 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r10
mov [ rsp + 0xc8 ], rbp
mulx rbp, r10, [ rsi + 0x10 ]
adox rdi, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], rbp
mulx rbp, rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r10
mov [ rsp + 0xe0 ], rbp
mulx rbp, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe8 ], rbp
mov [ rsp + 0xf0 ], r10
mulx r10, rbp, [ rsi + 0x8 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xf8 ], r10
mov [ rsp + 0x100 ], rbp
mulx rbp, r10, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rdi
mov [ rsp + 0x110 ], rcx
mulx rcx, rdi, [ rsi + 0x18 ]
adox r8, r15
mov rdx, r9
adcx rdx, r13
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x118 ], r8
mov [ rsp + 0x120 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
adcx r10, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r10
mulx r10, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r13
mulx r13, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], r10
mov [ rsp + 0x148 ], r15
mulx r15, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r10
mov [ rsp + 0x158 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x160 ], rdi
mov rdi, -0x2 
inc rdi
adox r9, r14
adcx r12, rbp
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
adox rax, r11
setc dl
clc
adcx rbx, r13
seto r11b
mov r13, -0x2 
inc r13
adox r8, r15
adox rcx, [ rsp + 0xc8 ]
mov r15, [ rsp + 0xc0 ]
seto r13b
mov [ rsp + 0x180 ], rcx
mov rcx, -0x2 
inc rcx
adox r15, [ rsp + 0x158 ]
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r8
mov [ rsp + 0x190 ], r15
mulx r15, r8, [ rsi + 0x10 ]
adcx r14, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x198 ], r14
mov [ rsp + 0x1a0 ], rbx
mulx rbx, r14, [ rsi + 0x28 ]
adcx rbp, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x70 ]
setc dl
clc
mov [ rsp + 0x1a8 ], r8
mov r8, -0x1 
movzx r9, r9b
adcx r9, r8
adcx r10, [ rsp + 0x68 ]
mov r9b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], rbp
mulx rbp, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b8 ], r8
mov [ rsp + 0x1c0 ], rax
mulx rax, r8, [ rsi + 0x0 ]
adox r12, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x110 ]
seto dl
mov [ rsp + 0x1c8 ], rdi
mov rdi, -0x2 
inc rdi
adox r14, rbp
adcx r8, [ rsp + 0x160 ]
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1d0 ], r14
mulx r14, rdi, [ rsi + 0x28 ]
adcx rax, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1d8 ], r12
mov [ rsp + 0x1e0 ], r14
mulx r14, r12, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x98 ]
mov [ rsp + 0x1e8 ], rax
mov rax, 0x0 
adcx rdx, rax
mov [ rsp + 0x1f0 ], rdx
mov rdx, [ rsp + 0x60 ]
clc
adcx rdx, [ rsp + 0x58 ]
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1f8 ], r14
mov byte [ rsp + 0x200 ], r13b
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x208 ], rax
mov [ rsp + 0x210 ], r14
mulx r14, rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x218 ], r8
mov byte [ rsp + 0x220 ], cl
mulx rcx, r8, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x108 ]
mov [ rsp + 0x228 ], rcx
setc cl
clc
mov [ rsp + 0x230 ], r8
mov r8, -0x1 
movzx r11, r11b
adcx r11, r8
adcx rdx, [ rsp + 0x148 ]
setc r11b
clc
adcx rax, r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x238 ], rax
mulx rax, r8, [ rsi + 0x18 ]
adcx r14, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x240 ], r14
mov [ rsp + 0x248 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x50 ]
mov [ rsp + 0x250 ], rax
setc al
clc
mov [ rsp + 0x258 ], r10
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rdx, [ rsp + 0x28 ]
adcx r14, [ rsp + 0x18 ]
mov rcx, [ rsp - 0x8 ]
setc r10b
clc
mov [ rsp + 0x260 ], r14
mov r14, -0x1 
movzx rbp, bpl
adcx rbp, r14
adcx rcx, [ rsp + 0xe0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x268 ], rcx
mulx rcx, r14, rdx
adcx r12, [ rsp - 0x10 ]
seto dl
mov [ rsp + 0x270 ], rbp
mov rbp, 0x0 
dec rbp
movzx rax, al
adox rax, rbp
adox r8, [ rsp + 0xf8 ]
setc al
clc
movzx r10, r10b
adcx r10, rbp
adcx r13, r14
seto r10b
inc rbp
mov r14, -0x1 
movzx r9, r9b
adox r9, r14
adox r15, [ rsp + 0x138 ]
adcx rdi, rcx
mov r9, [ rsp + 0x118 ]
setc cl
clc
movzx r11, r11b
adcx r11, r14
adcx r9, [ rsp + 0x128 ]
seto r11b
inc r14
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox rbx, [ rsp - 0x18 ]
mov rdx, [ rsp + 0x258 ]
adcx rdx, [ rsp + 0x168 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x278 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x280 ], rdi
setc dil
mov [ rsp + 0x288 ], r13
movzx r13, byte [ rsp + 0x220 ]
clc
mov [ rsp + 0x290 ], r12
mov r12, -0x1 
adcx r13, r12
adcx rdx, [ rsp + 0x80 ]
mov r13, [ rsp - 0x30 ]
adox r13, [ rsp - 0x28 ]
seto r12b
mov [ rsp + 0x298 ], r13
mov r13, 0x0 
dec r13
movzx rdi, dil
adox rdi, r13
adox rdx, [ rsp + 0x218 ]
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2a0 ], r15
mulx r15, r13, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x78 ]
adcx rdx, [ rsp + 0xb0 ]
mov byte [ rsp + 0x2a8 ], r11b
mov r11, [ rsp + 0xa8 ]
mov [ rsp + 0x2b0 ], rdi
mov rdi, 0x0 
adcx r11, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x2b8 ], cl
mov [ rsp + 0x2c0 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
movzx rdx, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x2c8 ], r8
mov r8, -0x1 
adcx rdx, r8
adcx rbp, [ rsp + 0x10 ]
mov rdx, [ rsp + 0x1f8 ]
seto r8b
mov [ rsp + 0x2d0 ], rbp
mov rbp, 0x0 
dec rbp
movzx rax, al
adox rax, rbp
adox rdx, [ rsp + 0x230 ]
adcx rbx, [ rsp - 0x38 ]
setc al
clc
movzx r12, r12b
adcx r12, rbp
adcx rcx, [ rsp - 0x40 ]
mov r12, [ rsp + 0x250 ]
seto bpl
mov [ rsp + 0x2d8 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox r12, [ rsp + 0x48 ]
mov r10, [ rsp + 0x1c0 ]
setc bl
clc
adcx r10, [ rsp + 0x210 ]
mov [ rsp + 0x2e0 ], rcx
seto cl
mov [ rsp + 0x2e8 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox r13, [ rsp - 0x48 ]
mov rax, [ rsp + 0x40 ]
seto dl
mov [ rsp + 0x2f0 ], r13
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox rax, [ rsp + 0x38 ]
mov cl, dl
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x2f8 ], bl
mulx rbx, r13, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x300 ], rbx
mov [ rsp + 0x308 ], rax
mulx rax, rbx, r10
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp + 0x178 ]
mov [ rsp + 0x310 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x318 ], r14
mov byte [ rsp + 0x320 ], bpl
mulx rbp, r14, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x238 ]
adcx rdx, [ rsp + 0x248 ]
mov [ rsp + 0x328 ], rbp
seto bpl
mov [ rsp + 0x330 ], r12
mov r12, 0x0 
dec r12
movzx r8, r8b
adox r8, r12
adox rdi, [ rsp + 0x1e8 ]
adcx r9, [ rsp + 0x240 ]
adox r11, [ rsp + 0x1f0 ]
mov r8, rbx
setc r12b
clc
adcx r8, rax
mov byte [ rsp + 0x338 ], bpl
mov rbp, rbx
mov [ rsp + 0x340 ], r11
seto r11b
mov [ rsp + 0x348 ], rdi
mov rdi, -0x2 
inc rdi
adox rbp, r10
adox r8, rdx
mov rbp, 0xfdc1767ae2ffffff 
mov rdx, r10
mulx rdi, r10, rbp
setc bpl
clc
mov [ rsp + 0x350 ], rdi
mov rdi, -0x1 
movzx rcx, cl
adcx rcx, rdi
adcx r15, r13
mov rcx, rax
seto r13b
inc rdi
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox rcx, rbx
movzx rbx, byte [ rsp + 0x320 ]
mov rbp, [ rsp + 0x228 ]
lea rbx, [ rbx + rbp ]
adox r10, rax
mov rbp, [ rsp + 0x2c0 ]
setc al
clc
movzx r12, r12b
adcx r12, rdi
adcx rbp, [ rsp + 0x318 ]
seto r12b
inc rdi
mov rdi, -0x1 
movzx r13, r13b
adox r13, rdi
adox r9, rcx
setc r13b
clc
adcx r8, [ rsp + 0x140 ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x358 ], r15
mulx r15, rdi, r8
adcx r9, [ rsp + 0x1a0 ]
adox r10, rbp
setc bpl
movzx rdx, byte [ rsp + 0x2b8 ]
clc
mov [ rsp + 0x360 ], rbx
mov rbx, -0x1 
adcx rdx, rbx
adcx r14, [ rsp + 0x1e0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x368 ], r14
mulx r14, rbx, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x370 ], r14
mov [ rsp + 0x378 ], r10
mulx r10, r14, r8
mov rdx, r14
mov byte [ rsp + 0x380 ], bpl
seto bpl
mov [ rsp + 0x388 ], rbx
mov rbx, -0x2 
inc rbx
adox rdx, r8
mov rdx, [ rsp + 0x310 ]
setc bl
clc
mov byte [ rsp + 0x390 ], bpl
mov rbp, -0x1 
movzx r13, r13b
adcx r13, rbp
adcx rdx, [ rsp + 0x2b0 ]
mov r13, [ rsp + 0x308 ]
adcx r13, [ rsp + 0x348 ]
mov rbp, [ rsp + 0x330 ]
adcx rbp, [ rsp + 0x340 ]
mov byte [ rsp + 0x398 ], bl
movzx rbx, byte [ rsp + 0x338 ]
mov [ rsp + 0x3a0 ], rbp
mov rbp, [ rsp + 0x170 ]
lea rbx, [ rbx + rbp ]
mov rbp, 0x7bc65c783158aea3 
xchg rdx, rbp
mov [ rsp + 0x3a8 ], r13
mov [ rsp + 0x3b0 ], rbp
mulx rbp, r13, rcx
movzx rdx, r11b
adcx rdx, rbx
mov r11, r14
seto bl
mov [ rsp + 0x3b8 ], rdx
mov rdx, -0x2 
inc rdx
adox r11, r10
adox r14, r10
setc dl
clc
mov [ rsp + 0x3c0 ], r14
mov r14, -0x1 
movzx r12, r12b
adcx r12, r14
adcx r13, [ rsp + 0x350 ]
adox rdi, r10
mov r12, [ rsp + 0x2c8 ]
seto r10b
movzx r14, byte [ rsp + 0x2f8 ]
mov [ rsp + 0x3c8 ], rdi
mov rdi, 0x0 
dec rdi
adox r14, rdi
adox r12, [ rsp + 0x8 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, rdi
adcx r9, r11
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, rbx
mulx rdi, r11, rcx
mov rdx, [ rsp + 0x0 ]
adox rdx, [ rsp + 0xf0 ]
mov [ rsp + 0x3d0 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x3d8 ], r12
mov byte [ rsp + 0x3e0 ], bl
mulx rbx, r12, rcx
setc cl
clc
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx rbp, r11
mov r14, 0x6cfc5fd681c52056 
mov rdx, r8
mulx r11, r8, r14
adcx r12, rdi
seto dil
mov r14, -0x2 
inc r14
adox r9, [ rsp - 0x20 ]
mov r14, 0x2341f27177344 
xchg rdx, r14
mov byte [ rsp + 0x3e8 ], dil
mov [ rsp + 0x3f0 ], r12
mulx r12, rdi, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3f8 ], r12
mov [ rsp + 0x400 ], rdi
mulx rdi, r12, r9
movzx rdx, al
mov [ rsp + 0x408 ], rdi
mov rdi, [ rsp + 0x300 ]
lea rdx, [ rdx + rdi ]
mov rdi, 0xffffffffffffffff 
xchg rdx, rdi
mov [ rsp + 0x410 ], rdi
mulx rdi, rax, r9
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x418 ], r12
mov [ rsp + 0x420 ], rbx
mulx rbx, r12, r14
clc
mov r14, -0x1 
movzx r10, r10b
adcx r10, r14
adcx r15, r12
mulx r12, r10, r9
adcx r8, rbx
seto bl
movzx r14, byte [ rsp + 0x390 ]
mov rdx, 0x0 
dec rdx
adox r14, rdx
adox r13, [ rsp + 0x3b0 ]
adcx r11, [ rsp + 0x388 ]
adox rbp, [ rsp + 0x3a8 ]
mov r14, [ rsp + 0x198 ]
seto dl
mov [ rsp + 0x428 ], r11
movzx r11, byte [ rsp + 0x380 ]
mov [ rsp + 0x430 ], r8
mov r8, 0x0 
dec r8
adox r11, r8
adox r14, [ rsp + 0x378 ]
adox r13, [ rsp + 0x1b0 ]
setc r11b
clc
movzx rcx, cl
adcx rcx, r8
adcx r14, [ rsp + 0x3c0 ]
mov rcx, rax
setc r8b
clc
adcx rcx, r9
seto cl
mov [ rsp + 0x438 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rbx, bl
adox rbx, r15
adox r14, [ rsp + 0x190 ]
mov rbx, rax
setc r15b
clc
adcx rbx, rdi
mov [ rsp + 0x440 ], r12
mov r12, [ rsp + 0xd8 ]
mov [ rsp + 0x448 ], r10
seto r10b
mov [ rsp + 0x450 ], rbx
movzx rbx, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x458 ], r14
mov r14, 0x0 
dec r14
adox rbx, r14
adox r12, [ rsp + 0x130 ]
mov rbx, [ rsp + 0xd0 ]
mov r14, 0x0 
adox rbx, r14
movzx r14, r11b
mov byte [ rsp + 0x460 ], r10b
mov r10, [ rsp + 0x370 ]
lea r14, [ r14 + r10 ]
adcx rax, rdi
mov r10, [ rsp + 0x3f0 ]
mov r11, 0x0 
dec r11
movzx rdx, dl
adox rdx, r11
adox r10, [ rsp + 0x3a0 ]
mov rdx, [ rsp + 0x3b8 ]
adox rdx, [ rsp + 0x420 ]
setc r11b
clc
mov [ rsp + 0x468 ], rax
mov rax, -0x1 
movzx rcx, cl
adcx rcx, rax
adcx rbp, [ rsp + 0x1a8 ]
movzx rcx, byte [ rsp + 0x3e0 ]
mov rax, 0x0 
adox rcx, rax
dec rax
movzx r8, r8b
adox r8, rax
adox r13, [ rsp + 0x3c8 ]
mov r8, [ rsp + 0x458 ]
seto al
mov [ rsp + 0x470 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r15, r15b
adox r15, r13
adox r8, [ rsp + 0x450 ]
seto r15b
inc r13
adox r8, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x2a0 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov byte [ rsp + 0x478 ], r15b
mov [ rsp + 0x480 ], r14
mulx r14, r15, r13
mov r13, 0x2341f27177344 
mov [ rsp + 0x488 ], r14
mov [ rsp + 0x490 ], r15
mulx r15, r14, r13
adcx r12, r8
seto r8b
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r11, r11b
adox r11, r13
adox rdi, [ rsp + 0x418 ]
mov r11, 0x6cfc5fd681c52056 
xchg rdx, r11
mov [ rsp + 0x498 ], r15
mulx r15, r13, r9
mov r9, [ rsp + 0x448 ]
adox r9, [ rsp + 0x408 ]
adox r13, [ rsp + 0x440 ]
adcx rbx, rcx
seto cl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox rbp, [ rsp + 0x438 ]
adox r10, [ rsp + 0x430 ]
adox r12, [ rsp + 0x428 ]
adox rbx, [ rsp + 0x480 ]
seto al
inc rdx
mov rdx, -0x1 
movzx rcx, cl
adox rcx, rdx
adox r15, [ rsp + 0x400 ]
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp + 0x4a0 ], r15
mulx r15, rcx, r11
mov rdx, rcx
mov [ rsp + 0x4a8 ], r14
setc r14b
clc
adcx rdx, r15
mov [ rsp + 0x4b0 ], rdx
mov rdx, rcx
adcx rdx, r15
adcx r15, [ rsp + 0x490 ]
mov [ rsp + 0x4b8 ], r15
setc r15b
clc
adcx rcx, r11
mov rcx, [ rsp + 0x470 ]
mov [ rsp + 0x4c0 ], rdx
seto dl
mov [ rsp + 0x4c8 ], r13
movzx r13, byte [ rsp + 0x460 ]
mov byte [ rsp + 0x4d0 ], r8b
mov r8, 0x0 
dec r8
adox r13, r8
adox rcx, [ rsp + 0x1d8 ]
mov r13, 0x6cfc5fd681c52056 
xchg rdx, r13
mov byte [ rsp + 0x4d8 ], r13b
mulx r13, r8, r11
adox rbp, [ rsp + 0x1c8 ]
adox r10, [ rsp + 0x268 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x4e0 ], r13
mov [ rsp + 0x4e8 ], r9
mulx r9, r13, r11
adox r12, [ rsp + 0x290 ]
setc r11b
clc
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx r13, [ rsp + 0x488 ]
adcx r8, r9
movzx r15, al
movzx r14, r14b
lea r15, [ r15 + r14 ]
adox rbx, [ rsp + 0x2e8 ]
seto r14b
movzx rax, byte [ rsp + 0x478 ]
inc rdx
mov r9, -0x1 
adox rax, r9
adox rcx, [ rsp + 0x468 ]
adox rdi, rbp
adox r10, [ rsp + 0x4e8 ]
setc al
movzx rbp, byte [ rsp + 0x4d0 ]
clc
adcx rbp, r9
adcx rcx, [ rsp + 0x208 ]
adox r12, [ rsp + 0x4c8 ]
setc bpl
clc
movzx r11, r11b
adcx r11, r9
adcx rcx, [ rsp + 0x4b0 ]
setc r11b
clc
movzx rbp, bpl
adcx rbp, r9
adcx rdi, [ rsp + 0x270 ]
adcx r10, [ rsp + 0x260 ]
mov rbp, [ rsp + 0x4e0 ]
setc dl
clc
movzx rax, al
adcx rax, r9
adcx rbp, [ rsp + 0x4a8 ]
adox rbx, [ rsp + 0x4a0 ]
seto al
inc r9
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox r15, [ rsp + 0x360 ]
movzx r14, byte [ rsp + 0x4d8 ]
mov r9, [ rsp + 0x3f8 ]
lea r14, [ r14 + r9 ]
seto r9b
mov [ rsp + 0x4f0 ], rbp
mov rbp, 0x0 
dec rbp
movzx rax, al
adox rax, rbp
adox r15, r14
mov rax, [ rsp + 0x498 ]
mov r14, 0x0 
adcx rax, r14
clc
adcx rcx, [ rsp + 0x1b8 ]
mov r14, 0x2341f27177344 
xchg rdx, r14
mov [ rsp + 0x4f8 ], rax
mulx rax, rbp, rcx
setc dl
clc
mov [ rsp + 0x500 ], r8
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx r12, [ rsp + 0x288 ]
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0x508 ], r13
mulx r13, r8, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x510 ], r12
mov [ rsp + 0x518 ], rax
mulx rax, r12, rcx
adcx rbx, [ rsp + 0x280 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x520 ], rbx
mov [ rsp + 0x528 ], rbp
mulx rbp, rbx, rcx
setc dl
clc
mov [ rsp + 0x530 ], rbp
mov rbp, -0x1 
movzx r11, r11b
adcx r11, rbp
adcx rdi, [ rsp + 0x4c0 ]
seto r11b
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox rdi, [ rsp + 0x1d0 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x538 ], rbx
mulx rbx, rbp, r14
mov r14, rbp
mov [ rsp + 0x540 ], rax
seto al
mov [ rsp + 0x548 ], r10
mov r10, -0x2 
inc r10
adox r14, rbx
mov r10, rbp
adox r10, rbx
mov [ rsp + 0x550 ], r10
movzx r10, byte [ rsp + 0x398 ]
mov byte [ rsp + 0x558 ], al
mov rax, [ rsp + 0x328 ]
lea r10, [ r10 + rax ]
movzx rax, r11b
movzx r9, r9b
lea rax, [ rax + r9 ]
seto r9b
mov r11, 0x0 
dec r11
movzx rcx, cl
adox rcx, r11
adox r15, [ rsp + 0x368 ]
setc cl
clc
adcx rbp, rdx
adcx r14, rdi
setc bpl
clc
adcx r14, [ rsp + 0x150 ]
mov rdx, 0x6cfc5fd681c52056 
mulx r11, rdi, r14
adox r10, rax
mov rax, 0xffffffffffffffff 
mov rdx, rax
mov [ rsp + 0x560 ], r11
mulx r11, rax, r14
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x568 ], rdi
mov [ rsp + 0x570 ], r10
mulx r10, rdi, r14
mov rdx, rax
mov [ rsp + 0x578 ], r15
seto r15b
mov byte [ rsp + 0x580 ], bpl
mov rbp, -0x2 
inc rbp
adox rdx, r11
mov rbp, rax
adox rbp, r11
mov [ rsp + 0x588 ], rbp
setc bpl
clc
mov byte [ rsp + 0x590 ], r15b
mov r15, -0x1 
movzx r9, r9b
adcx r9, r15
adcx rbx, r8
adcx r12, r13
mov r8, 0x7bc65c783158aea3 
xchg rdx, r14
mulx r9, r13, r8
adox rdi, r11
mov r11, [ rsp + 0x548 ]
seto r15b
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rcx, cl
adox rcx, r8
adox r11, [ rsp + 0x4b8 ]
seto cl
inc r8
mov r8, -0x1 
movzx r15, r15b
adox r15, r8
adox r10, r13
seto r13b
movzx r15, byte [ rsp + 0x558 ]
inc r8
mov r8, -0x1 
adox r15, r8
adox r11, [ rsp + 0x278 ]
mov r15, [ rsp + 0x540 ]
adcx r15, [ rsp + 0x538 ]
seto r8b
mov [ rsp + 0x598 ], r10
movzx r10, byte [ rsp + 0x580 ]
mov [ rsp + 0x5a0 ], r15
mov r15, 0x0 
dec r15
adox r10, r15
adox r11, [ rsp + 0x550 ]
seto r10b
inc r15
mov r15, -0x1 
movzx rbp, bpl
adox rbp, r15
adox r11, [ rsp + 0x188 ]
mov rbp, [ rsp + 0x530 ]
adcx rbp, [ rsp + 0x528 ]
movzx r15, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x5a8 ], rbp
mov rbp, [ rsp + 0xe8 ]
lea r15, [ r15 + rbp ]
mov rbp, [ rsp + 0x518 ]
mov [ rsp + 0x5b0 ], r15
mov r15, 0x0 
adcx rbp, r15
mov r15, [ rsp + 0x510 ]
clc
mov [ rsp + 0x5b8 ], rbp
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx r15, [ rsp + 0x508 ]
seto cl
inc rbp
adox rax, rdx
adox r14, r11
mov rax, [ rsp + 0x520 ]
adcx rax, [ rsp + 0x500 ]
mov r11, [ rsp + 0x578 ]
adcx r11, [ rsp + 0x4f0 ]
seto bpl
mov [ rsp + 0x5c0 ], rdi
mov rdi, 0x0 
dec rdi
movzx r8, r8b
adox r8, rdi
adox r15, [ rsp + 0x298 ]
mov r8, [ rsp + 0x570 ]
adcx r8, [ rsp + 0x4f8 ]
adox rax, [ rsp + 0x2e0 ]
setc dil
clc
mov [ rsp + 0x5c8 ], r8
mov r8, -0x1 
movzx r10, r10b
adcx r10, r8
adcx r15, rbx
adox r11, [ rsp + 0x3d8 ]
setc bl
clc
movzx rcx, cl
adcx rcx, r8
adcx r15, [ rsp + 0x180 ]
mov r10, 0x2341f27177344 
mulx r8, rcx, r10
setc dl
clc
mov r10, -0x1 
movzx r13, r13b
adcx r13, r10
adcx r9, [ rsp + 0x568 ]
adcx rcx, [ rsp + 0x560 ]
setc r13b
clc
movzx rbx, bl
adcx rbx, r10
adcx rax, r12
seto r12b
inc r10
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox rax, [ rsp + 0x2d0 ]
movzx rdx, r13b
lea rdx, [ rdx + r8 ]
movzx r8, dil
movzx r13, byte [ rsp + 0x590 ]
lea r8, [ r8 + r13 ]
setc r13b
seto dil
mov rbx, r14
mov [ rsp + 0x5d0 ], rdx
mov rdx, 0xffffffffffffffff 
sub rbx, rdx
dec r10
movzx rbp, bpl
adox rbp, r10
adox r15, [ rsp + 0x588 ]
seto bpl
mov r10, r15
sbb r10, rdx
mov rdx, 0x0 
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox rax, [ rsp + 0x5c0 ]
seto bpl
mov rdx, rax
mov [ rsp + 0x5d8 ], r10
mov r10, 0xffffffffffffffff 
sbb rdx, r10
mov r10, [ rsp + 0x5c8 ]
mov [ rsp + 0x5e0 ], rbx
mov rbx, 0x0 
dec rbx
movzx r12, r12b
adox r12, rbx
adox r10, [ rsp + 0x3d0 ]
adox r8, [ rsp + 0x5b0 ]
setc r12b
clc
movzx r13, r13b
adcx r13, rbx
adcx r11, [ rsp + 0x5a0 ]
adcx r10, [ rsp + 0x5a8 ]
seto r13b
inc rbx
mov rbx, -0x1 
movzx rdi, dil
adox rdi, rbx
adox r11, [ rsp + 0x2d8 ]
seto dil
inc rbx
mov rbx, -0x1 
movzx rbp, bpl
adox rbp, rbx
adox r11, [ rsp + 0x598 ]
adcx r8, [ rsp + 0x5b8 ]
movzx rbp, r13b
mov rbx, 0x0 
adcx rbp, rbx
clc
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx r10, [ rsp + 0x2f0 ]
adcx r8, [ rsp + 0x358 ]
setc dil
seto bl
movzx r13, r12b
add r13, -0x1
mov r12, r11
mov r13, 0xfdc1767ae2ffffff 
sbb r12, r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox r10, r9
adox rcx, r8
seto r9b
mov rbx, r10
mov r8, 0x7bc65c783158aea3 
sbb rbx, r8
mov r13, rcx
mov r8, 0x6cfc5fd681c52056 
sbb r13, r8
mov r8, 0x0 
dec r8
movzx rdi, dil
adox rdi, r8
adox rbp, [ rsp + 0x410 ]
setc dil
clc
movzx r9, r9b
adcx r9, r8
adcx rbp, [ rsp + 0x5d0 ]
seto r9b
adc r9b, 0x0
movzx r9, r9b
movzx r8, dil
add r8, -0x1
mov rdi, rbp
mov r8, 0x2341f27177344 
sbb rdi, r8
movzx r8, r9b
sbb r8, 0x00000000
cmovc rdx, rax
cmovc rbx, r10
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], rdx
cmovc rdi, rbp
mov rax, [ rsp + 0x5e0 ]
cmovc rax, r14
mov [ r8 + 0x30 ], rdi
mov [ r8 + 0x20 ], rbx
mov r14, [ rsp + 0x5d8 ]
cmovc r14, r15
mov [ r8 + 0x8 ], r14
mov [ r8 + 0x0 ], rax
cmovc r13, rcx
cmovc r12, r11
mov [ r8 + 0x28 ], r13
mov [ r8 + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1640
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3655
; seed 2784689928167702 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 76981 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 1128 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.014652966316363779
; number reverted permutation / tried permutation: 256 / 495 =51.717%
; number reverted decision / tried decision: 220 / 504 =43.651%
; validated in 340.363s
