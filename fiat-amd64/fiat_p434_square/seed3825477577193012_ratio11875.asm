SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1688
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], r13
mulx r13, rax, [ rsi + 0x30 ]
add r8, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r8
mulx r8, r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], rax
mov [ rsp - 0x10 ], rcx
mulx rcx, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], rax
mulx rax, rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r14
mulx r14, r12, rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r9
mulx r9, r8, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r8
mulx r8, r9, rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x78 ], rax
mov [ rsp + 0x80 ], rcx
mulx rcx, rax, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rax
mulx rax, rcx, [ rsi + 0x28 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x98 ], rax
mov [ rsp + 0xa0 ], rcx
mulx rcx, rax, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], rcx
mov [ rsp + 0xb0 ], rax
mulx rax, rcx, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xb8 ], rax
mov [ rsp + 0xc0 ], rcx
mulx rcx, rax, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r11
mov [ rsp + 0xd0 ], r8
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, rax
mov [ rsp + 0xd8 ], r13
mov r13, -0x2 
inc r13
adox rdx, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], r9
mulx r9, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], r9
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x108 ], r13
mov [ rsp + 0x110 ], rbp
mulx rbp, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x118 ], rbp
mov [ rsp + 0x120 ], r13
mulx r13, rbp, [ rsi + 0x30 ]
setc dl
clc
adcx r11, r10
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], r13
mulx r13, r11, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r13
mulx r13, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r11
mov [ rsp + 0x148 ], r13
mulx r13, r11, [ rsi + 0x20 ]
mov rdx, rax
mov [ rsp + 0x150 ], r10
setc r10b
clc
adcx rdx, rcx
mov [ rsp + 0x158 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x160 ], r12b
mov byte [ rsp + 0x168 ], r10b
mulx r10, r12, [ rsi + 0x10 ]
setc dl
clc
adcx r8, r14
adcx rdi, r9
mov r14, rcx
seto r9b
mov [ rsp + 0x170 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rdx, dl
adox rdx, rdi
adox r14, rax
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, [ rsi + 0x18 ]
adcx rax, r15
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x178 ], rax
mulx rax, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x180 ], r14
mov [ rsp + 0x188 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x190 ], r14
mov [ rsp + 0x198 ], r8
mulx r8, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1a0 ], r8
mov byte [ rsp + 0x1a8 ], r9b
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1b0 ], r8
mov [ rsp + 0x1b8 ], r14
mulx r14, r8, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x1c0 ], r14
mov r14, -0x2 
inc r14
adox rbx, rbp
adox r11, [ rsp + 0x110 ]
adox r13, [ rsp + 0x108 ]
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c8 ], r13
mulx r13, r14, rdx
mov rdx, [ rsp + 0xf0 ]
mov [ rsp + 0x1d0 ], r11
seto r11b
mov [ rsp + 0x1d8 ], rbx
movzx rbx, byte [ rsp + 0x168 ]
mov [ rsp + 0x1e0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rbx, r13
adox rdx, [ rsp + 0xe0 ]
mov rbx, [ rsp + 0xe8 ]
setc r13b
clc
mov [ rsp + 0x1e8 ], rdx
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rbx, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f0 ], rbx
mulx rbx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x1f8 ], bpl
mov [ rsp + 0x200 ], r14
mulx r14, rbp, [ rsi + 0x8 ]
adox r11, [ rsp + 0xd0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], r11
mov [ rsp + 0x210 ], r8
mulx r8, r11, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0x218 ], r11
seto r11b
mov [ rsp + 0x220 ], rbx
mov rbx, -0x2 
inc rbx
adox rdx, [ rsp + 0xc8 ]
mov rbx, [ rsp + 0x78 ]
adox rbx, [ rsp + 0xc0 ]
mov [ rsp + 0x228 ], rbx
setc bl
clc
adcx rbp, r8
mov r8, [ rsp + 0x60 ]
mov [ rsp + 0x230 ], rbp
seto bpl
mov [ rsp + 0x238 ], rdx
movzx rdx, byte [ rsp + 0x160 ]
mov byte [ rsp + 0x240 ], r11b
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rdx, r11
adox r8, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x248 ], r8
mulx r8, r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x250 ], r9
mov [ rsp + 0x258 ], rax
mulx rax, r9, [ rsi + 0x18 ]
adcx r12, r14
mov rdx, [ rsp + 0x58 ]
seto r14b
mov [ rsp + 0x260 ], r12
mov r12, 0x0 
dec r12
movzx rbx, bl
adox rbx, r12
adox rdx, [ rsp + 0x40 ]
adcx r11, r10
setc r10b
clc
movzx rbp, bpl
adcx rbp, r12
adcx r9, [ rsp + 0xb8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, rbp, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x268 ], rbx
mov rbx, -0x1 
movzx r14, r14b
adcx r14, rbx
adcx r15, [ rsp + 0x118 ]
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x270 ], r15
mulx r15, rbx, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x278 ], r11
mov r11, 0x0 
dec r11
movzx r10, r10b
adox r10, r11
adox r8, rbp
seto r10b
inc r11
mov rbp, -0x1 
movzx r13, r13b
adox r13, rbp
adox rdi, [ rsp + 0x50 ]
mov r13, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x258 ]
mov r11b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x280 ], r13
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x10 ]
adcx rdx, [ rsp + 0x8 ]
mov [ rsp + 0x288 ], rdx
mov rdx, [ rsp + 0x250 ]
mov [ rsp + 0x290 ], r8
seto r8b
mov [ rsp + 0x298 ], r9
mov r9, -0x2 
inc r9
adox rdx, [ rsp + 0x100 ]
mov r9, [ rsp + 0x220 ]
mov [ rsp + 0x2a0 ], rdx
seto dl
mov [ rsp + 0x2a8 ], rdi
movzx rdi, byte [ rsp + 0x240 ]
mov [ rsp + 0x2b0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox rdi, r12
adox r9, [ rsp + 0x210 ]
mov dil, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2b8 ], r9
mulx r9, r12, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x1b8 ]
adox rdx, [ rsp + 0x1c0 ]
mov [ rsp + 0x2c0 ], rdx
mov rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x2c8 ], r9
setc r9b
clc
mov byte [ rsp + 0x2d0 ], r10b
mov r10, -0x1 
movzx rdi, dil
adcx rdi, r10
adcx rdx, [ rsp + 0x0 ]
setc dil
clc
movzx r8, r8b
adcx r8, r10
adcx rbp, [ rsp + 0x48 ]
adcx r13, [ rsp + 0x30 ]
mov r8, [ rsp + 0x188 ]
setc r10b
mov [ rsp + 0x2d8 ], rdx
movzx rdx, byte [ rsp + 0x1a8 ]
clc
mov [ rsp + 0x2e0 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx r8, [ rsp + 0x198 ]
mov rdx, [ rsp + 0x180 ]
adcx rdx, [ rsp + 0x170 ]
adox r12, [ rsp + 0x1a0 ]
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2e8 ], r12
mov [ rsp + 0x2f0 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
seto dl
mov byte [ rsp + 0x2f8 ], r9b
mov r9, -0x2 
inc r9
adox r8, [ rsp - 0x10 ]
mov r9, 0x2341f27177344 
xchg rdx, r9
mov byte [ rsp + 0x300 ], r9b
mov [ rsp + 0x308 ], rbp
mulx rbp, r9, r8
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x310 ], rbp
mov [ rsp + 0x318 ], r9
mulx r9, rbp, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x320 ], r9
mov [ rsp + 0x328 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x330 ], rbp
mov [ rsp + 0x338 ], r12
mulx r12, rbp, r8
seto dl
mov [ rsp + 0x340 ], r12
mov r12, 0x0 
dec r12
movzx r14, r14b
adox r14, r12
adox rax, r9
seto r14b
inc r12
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox r13, [ rsp + 0x238 ]
movzx rdx, r10b
mov r12, [ rsp + 0x28 ]
lea rdx, [ rdx + r12 ]
mov r12, rbp
seto r10b
inc r9
adox r12, r8
mov r12, [ rsp - 0x28 ]
setc r9b
clc
mov [ rsp + 0x348 ], rdx
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r12, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x350 ], r12
mulx r12, r11, rdx
mov rdx, [ rsp + 0x130 ]
mov [ rsp + 0x358 ], rax
mov rax, 0x0 
adcx rdx, rax
clc
mov rax, -0x1 
movzx rdi, dil
adcx rdi, rax
adcx rbx, [ rsp - 0x8 ]
adcx r15, [ rsp + 0x338 ]
mov rdi, rbp
setc al
clc
adcx rdi, [ rsp + 0x340 ]
mov [ rsp + 0x360 ], r15
mov r15, [ rsp + 0x308 ]
mov [ rsp + 0x368 ], rdx
seto dl
mov [ rsp + 0x370 ], rbx
mov rbx, 0x0 
dec rbx
movzx rax, al
adox rax, rbx
adox r15, [ rsp + 0x200 ]
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x378 ], r15
mulx r15, rbx, r8
adcx rbp, [ rsp + 0x340 ]
adcx rbx, [ rsp + 0x340 ]
seto dl
mov [ rsp + 0x380 ], rbx
movzx rbx, byte [ rsp + 0x2f8 ]
mov [ rsp + 0x388 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox rbx, rbp
adox r11, [ rsp - 0x30 ]
mov rbx, [ rsp - 0x38 ]
seto bpl
mov [ rsp + 0x390 ], r11
movzx r11, byte [ rsp + 0x2d0 ]
mov byte [ rsp + 0x398 ], dl
mov rdx, 0x0 
dec rdx
adox r11, rdx
adox rbx, [ rsp + 0x2b0 ]
mov r11, [ rsp - 0x40 ]
adox r11, [ rsp + 0x150 ]
mov rdx, [ rsp + 0x330 ]
mov [ rsp + 0x3a0 ], r11
setc r11b
clc
mov [ rsp + 0x3a8 ], rbx
mov rbx, -0x1 
movzx r14, r14b
adcx r14, rbx
adcx rdx, [ rsp + 0xa0 ]
mov r14, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x98 ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, rbx
mov [ rsp + 0x3b0 ], r14
mov [ rsp + 0x3b8 ], rbx
mulx rbx, r14, r8
mov r8, [ rsp + 0x148 ]
mov rdx, 0x0 
adox r8, rdx
movzx rdx, byte [ rsp + 0x1f8 ]
mov [ rsp + 0x3c0 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox rdx, r8
adox rcx, [ rsp + 0x90 ]
setc dl
clc
movzx r11, r11b
adcx r11, r8
adcx r15, r14
movzx r11, bpl
lea r11, [ r11 + r12 ]
adcx rbx, [ rsp + 0x328 ]
mov r12, [ rsp + 0x320 ]
adcx r12, [ rsp + 0x318 ]
mov bpl, dl
mov rdx, [ rsi + 0x30 ]
mulx r8, r14, [ rsi + 0x28 ]
setc dl
clc
mov [ rsp + 0x3c8 ], r11
mov r11, -0x1 
movzx rax, al
adcx rax, r11
adcx r13, rdi
setc al
clc
adcx r13, [ rsp - 0x48 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r13
mov [ rsp + 0x3d0 ], r12
mulx r12, r11, rdi
mov rdi, [ rsp + 0x88 ]
adox rdi, [ rsp + 0xb0 ]
mov byte [ rsp + 0x3d8 ], r13b
mov r13, [ rsp + 0xa8 ]
adox r13, [ rsp + 0x140 ]
mov [ rsp + 0x3e0 ], rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x3e8 ], r15
mov [ rsp + 0x3f0 ], r12
mulx r12, r15, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x3f8 ], r11
mov byte [ rsp + 0x400 ], bpl
mulx rbp, r11, rbx
mov rbx, r15
mov [ rsp + 0x408 ], rbp
setc bpl
clc
adcx rbx, rdx
setc bl
clc
mov byte [ rsp + 0x410 ], bpl
mov rbp, -0x1 
movzx r9, r9b
adcx r9, rbp
adcx rcx, [ rsp + 0x178 ]
mov r9, 0x2341f27177344 
mov byte [ rsp + 0x418 ], bl
mulx rbx, rbp, r9
adcx rdi, [ rsp + 0x2a8 ]
mov r9, [ rsp + 0x138 ]
adox r9, [ rsp + 0x70 ]
mov [ rsp + 0x420 ], rbx
mov rbx, r15
mov [ rsp + 0x428 ], rbp
setc bpl
clc
adcx rbx, r12
mov [ rsp + 0x430 ], rbx
mov rbx, [ rsp + 0x68 ]
mov [ rsp + 0x438 ], r11
mov r11, 0x0 
adox rbx, r11
dec r11
movzx r10, r10b
adox r10, r11
adox rcx, [ rsp + 0x228 ]
setc r10b
movzx r11, byte [ rsp + 0x398 ]
clc
mov [ rsp + 0x440 ], rbx
mov rbx, -0x1 
adcx r11, rbx
adcx r14, [ rsp + 0x1e0 ]
seto r11b
inc rbx
mov rbx, -0x1 
movzx rax, al
adox rax, rbx
adox rcx, [ rsp + 0x388 ]
mov rax, 0x0 
adcx r8, rax
clc
movzx r11, r11b
adcx r11, rbx
adcx rdi, [ rsp + 0x298 ]
seto r11b
dec rax
movzx rbp, bpl
adox rbp, rax
adox r13, [ rsp + 0x2f0 ]
adcx r13, [ rsp + 0x358 ]
adox r9, [ rsp + 0x2e0 ]
movzx rbx, byte [ rsp + 0x400 ]
mov rbp, [ rsp + 0x18 ]
lea rbx, [ rbx + rbp ]
adcx r9, [ rsp + 0x3b8 ]
mov rbp, r12
setc al
clc
mov [ rsp + 0x448 ], r8
mov r8, -0x1 
movzx r10, r10b
adcx r10, r8
adcx rbp, r15
mov r15, [ rsp + 0x440 ]
adox r15, [ rsp + 0x348 ]
adcx r12, [ rsp + 0x3f8 ]
seto r10b
inc r8
mov r8, -0x1 
movzx rax, al
adox rax, r8
adox r15, [ rsp + 0x3b0 ]
mov rax, 0x7bc65c783158aea3 
mov [ rsp + 0x450 ], r14
mulx r14, r8, rax
movzx rdx, r10b
adox rdx, rbx
adcx r8, [ rsp + 0x3f0 ]
seto bl
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r11, r11b
adox r11, r10
adox rdi, [ rsp + 0x380 ]
adcx r14, [ rsp + 0x438 ]
mov r11, [ rsp + 0x408 ]
adcx r11, [ rsp + 0x428 ]
setc r10b
movzx rax, byte [ rsp + 0x410 ]
clc
mov [ rsp + 0x458 ], r11
mov r11, -0x1 
adcx rax, r11
adcx rcx, [ rsp + 0x128 ]
adcx rdi, [ rsp + 0x1e8 ]
adox r13, [ rsp + 0x3e8 ]
adox r9, [ rsp + 0x3e0 ]
adcx r13, [ rsp + 0x208 ]
seto al
movzx r11, byte [ rsp + 0x418 ]
mov byte [ rsp + 0x460 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r11, rbx
adox rcx, [ rsp + 0x430 ]
adcx r9, [ rsp + 0x2b8 ]
setc r11b
clc
adcx rcx, [ rsp + 0x218 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x468 ], r14
mov [ rsp + 0x470 ], r8
mulx r8, r14, rcx
adox rbp, rdi
mov rdi, 0x6cfc5fd681c52056 
mov rdx, rcx
mov [ rsp + 0x478 ], r9
mulx r9, rcx, rdi
adox r12, r13
adcx rbp, [ rsp + 0x230 ]
movzx r13, byte [ rsp + 0x3d8 ]
mov rdi, [ rsp + 0x310 ]
lea r13, [ r13 + rdi ]
adcx r12, [ rsp + 0x260 ]
seto dil
mov [ rsp + 0x480 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx rax, al
adox rax, r9
adox r15, [ rsp + 0x3d0 ]
adox r13, rbx
mov rbx, r14
seto al
inc r9
adox rbx, r8
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x488 ], r12
mov [ rsp + 0x490 ], rcx
mulx rcx, r12, r9
movzx r9, r10b
mov byte [ rsp + 0x498 ], al
mov rax, [ rsp + 0x420 ]
lea r9, [ r9 + rax ]
mov rax, r14
adox rax, r8
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x4a0 ], rax
mov [ rsp + 0x4a8 ], r9
mulx r9, rax, r10
movzx r10, byte [ rsp + 0x300 ]
mov [ rsp + 0x4b0 ], r9
mov r9, [ rsp + 0x2c8 ]
lea r10, [ r10 + r9 ]
adox r12, r8
adox rax, rcx
setc r9b
clc
mov r8, -0x1 
movzx r11, r11b
adcx r11, r8
adcx r15, [ rsp + 0x2c0 ]
mov r11, [ rsp + 0x478 ]
setc cl
clc
movzx rdi, dil
adcx rdi, r8
adcx r11, [ rsp + 0x470 ]
adcx r15, [ rsp + 0x468 ]
setc dil
clc
adcx r14, rdx
adcx rbx, rbp
seto r14b
inc r8
adox rbx, [ rsp + 0x190 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x4b8 ], rax
mulx rax, r8, rbp
setc bpl
clc
mov [ rsp + 0x4c0 ], r12
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx r13, [ rsp + 0x2e8 ]
movzx rcx, byte [ rsp + 0x498 ]
movzx r12, byte [ rsp + 0x460 ]
lea rcx, [ rcx + r12 ]
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4c8 ], r15
mov [ rsp + 0x4d0 ], r8
mulx r8, r15, r12
adcx r10, rcx
setc cl
clc
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx r13, [ rsp + 0x458 ]
adcx r10, [ rsp + 0x4a8 ]
seto dil
inc r12
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox r11, [ rsp + 0x278 ]
mov r9, 0x2341f27177344 
mov [ rsp + 0x4d8 ], r8
mulx r8, r12, r9
mov r9, [ rsp + 0x490 ]
mov [ rsp + 0x4e0 ], r8
setc r8b
clc
mov [ rsp + 0x4e8 ], r12
mov r12, -0x1 
movzx r14, r14b
adcx r14, r12
adcx r9, [ rsp + 0x4b0 ]
mov r14, 0x2341f27177344 
xchg rdx, r14
mov [ rsp + 0x4f0 ], r9
mulx r9, r12, rbx
mov rbx, [ rsp + 0x488 ]
setc dl
clc
mov [ rsp + 0x4f8 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rbx, [ rsp + 0x4a0 ]
setc bpl
clc
movzx rdx, dl
adcx rdx, r9
adcx r12, [ rsp + 0x480 ]
mov rdx, rax
setc r9b
clc
adcx rdx, [ rsp + 0x4d0 ]
mov [ rsp + 0x500 ], r12
mov r12, rax
adcx r12, [ rsp + 0x4d0 ]
mov byte [ rsp + 0x508 ], r9b
mov r9, [ rsp + 0x4c8 ]
adox r9, [ rsp + 0x290 ]
mov [ rsp + 0x510 ], r9
setc r9b
clc
mov [ rsp + 0x518 ], r12
mov r12, -0x1 
movzx rbp, bpl
adcx rbp, r12
adcx r11, [ rsp + 0x4c0 ]
adox r13, [ rsp + 0x3a8 ]
adox r10, [ rsp + 0x3a0 ]
movzx rbp, r8b
movzx rcx, cl
lea rbp, [ rbp + rcx ]
seto cl
inc r12
mov r8, -0x1 
movzx rdi, dil
adox rdi, r8
adox rbx, [ rsp + 0x1d8 ]
seto dil
dec r12
movzx r9, r9b
adox r9, r12
adox rax, r15
mov r8, 0x7bc65c783158aea3 
xchg rdx, r14
mulx r9, r15, r8
mov r12, rdx
setc r8b
clc
adcx r12, [ rsp + 0x4d0 ]
adox r15, [ rsp + 0x4d8 ]
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x520 ], r15
mov [ rsp + 0x528 ], rax
mulx rax, r15, r12
adcx r14, rbx
seto dl
mov rbx, -0x2 
inc rbx
adox r14, [ rsp + 0x1b0 ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x530 ], r10
mulx r10, r12, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x538 ], r10
mov [ rsp + 0x540 ], r12
mulx r12, r10, rbx
seto bl
mov [ rsp + 0x548 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox rbp, [ rsp + 0x3c0 ]
seto cl
inc r12
mov r12, -0x1 
movzx rdi, dil
adox rdi, r12
adox r11, [ rsp + 0x1d0 ]
adcx r11, [ rsp + 0x518 ]
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x550 ], r10
mulx r10, r12, rdi
mov rdi, [ rsp + 0x510 ]
mov [ rsp + 0x558 ], r11
setc r11b
clc
mov byte [ rsp + 0x560 ], bl
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx rdi, [ rsp + 0x4b8 ]
seto r8b
inc rbx
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox r9, r15
adox rax, [ rsp + 0x4e8 ]
seto r14b
inc rbx
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox rdi, [ rsp + 0x1c8 ]
mov r8, r12
seto r15b
mov [ rsp + 0x568 ], rax
mov rax, -0x3 
inc rax
adox r8, r10
mov rbx, r12
adox rbx, r10
mov rax, 0xfdc1767ae2ffffff 
mov [ rsp + 0x570 ], r9
mov [ rsp + 0x578 ], rbx
mulx rbx, r9, rax
adcx r13, [ rsp + 0x4f0 ]
adox r9, r10
movzx r10, byte [ rsp + 0x508 ]
mov rax, [ rsp + 0x4f8 ]
lea r10, [ r10 + rax ]
mov rax, [ rsp + 0x500 ]
adcx rax, [ rsp + 0x530 ]
adcx r10, rbp
adox rbx, [ rsp + 0x540 ]
movzx rbp, r14b
mov [ rsp + 0x580 ], rbx
mov rbx, [ rsp + 0x4e0 ]
lea rbp, [ rbp + rbx ]
movzx rbx, cl
mov r14, 0x0 
adcx rbx, r14
clc
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx r13, [ rsp + 0x1f0 ]
seto r15b
inc rcx
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox rdi, [ rsp + 0x528 ]
adox r13, [ rsp + 0x520 ]
adcx rax, [ rsp + 0x268 ]
setc r11b
clc
adcx r12, rdx
seto r12b
inc r14
mov rcx, -0x1 
movzx r11, r11b
adox r11, rcx
adox r10, [ rsp + 0x350 ]
mov r11, [ rsp + 0x558 ]
seto r14b
movzx rcx, byte [ rsp + 0x560 ]
mov [ rsp + 0x588 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox rcx, rbp
adox r11, [ rsp + 0x2a0 ]
adcx r8, r11
adox rdi, [ rsp + 0x2d8 ]
mov rcx, 0x2341f27177344 
mulx rbp, r11, rcx
mov rdx, [ rsp + 0x538 ]
seto cl
mov [ rsp + 0x590 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r15, r15b
adox r15, rbp
adox rdx, [ rsp + 0x550 ]
adox r11, [ rsp + 0x548 ]
seto r15b
inc rbp
adox r8, [ rsp - 0x18 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x598 ], r11
mov [ rsp + 0x5a0 ], r8
mulx r8, r11, rbp
mov rbp, 0x2341f27177344 
mov [ rsp + 0x5a8 ], r8
mov [ rsp + 0x5b0 ], r11
mulx r11, r8, rbp
seto bpl
mov [ rsp + 0x5b8 ], r11
mov r11, 0x0 
dec r11
movzx r12, r12b
adox r12, r11
adox rax, [ rsp + 0x570 ]
adcx rdi, [ rsp + 0x578 ]
adox r10, [ rsp + 0x568 ]
seto r12b
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox r13, [ rsp + 0x370 ]
setc cl
clc
movzx r14, r14b
adcx r14, r11
adcx rbx, [ rsp + 0x368 ]
setc r14b
clc
movzx rcx, cl
adcx rcx, r11
adcx r13, r9
movzx r9, r15b
mov rcx, [ rsp + 0x590 ]
lea r9, [ r9 + rcx ]
mov rcx, 0xffffffffffffffff 
mulx r11, r15, rcx
mov rcx, r15
mov [ rsp + 0x5c0 ], r9
seto r9b
mov [ rsp + 0x5c8 ], r8
mov r8, -0x2 
inc r8
adox rcx, rdx
setc cl
clc
movzx rbp, bpl
adcx rbp, r8
adcx rdi, [ rsp - 0x20 ]
setc bpl
clc
movzx r12, r12b
adcx r12, r8
adcx rbx, [ rsp + 0x588 ]
seto r12b
inc r8
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox r13, [ rsp + 0x248 ]
seto bpl
inc r8
mov r8, -0x1 
movzx r9, r9b
adox r9, r8
adox rax, [ rsp + 0x360 ]
adox r10, [ rsp + 0x378 ]
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x5d0 ], r13
mulx r13, r8, r9
mov r9, r15
mov byte [ rsp + 0x5d8 ], r14b
setc r14b
clc
adcx r9, r11
adox rbx, [ rsp + 0x450 ]
adcx r15, r11
adcx r8, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x5e0 ], r8
mov [ rsp + 0x5e8 ], r15
mulx r15, r8, r11
seto dl
mov r11, 0x0 
dec r11
movzx r12, r12b
adox r12, r11
adox rdi, r9
adcx r8, r13
setc r12b
clc
movzx rcx, cl
adcx rcx, r11
adcx rax, [ rsp + 0x580 ]
adcx r10, [ rsp + 0x5a0 ]
setc cl
seto r13b
mov r9, rdi
mov r11, 0xffffffffffffffff 
sub r9, r11
mov r11, 0x0 
dec r11
movzx rbp, bpl
adox rbp, r11
adox rax, [ rsp + 0x270 ]
adox r10, [ rsp + 0x280 ]
movzx rbp, r14b
movzx r11, byte [ rsp + 0x5d8 ]
lea rbp, [ rbp + r11 ]
setc r11b
clc
mov r14, -0x1 
movzx r12, r12b
adcx r12, r14
adcx r15, [ rsp + 0x5b0 ]
setc r12b
clc
movzx rcx, cl
adcx rcx, r14
adcx rbx, [ rsp + 0x598 ]
mov rcx, [ rsp + 0x5d0 ]
setc r14b
clc
mov [ rsp + 0x5f0 ], r9
mov r9, -0x1 
movzx r13, r13b
adcx r13, r9
adcx rcx, [ rsp + 0x5e8 ]
mov r13, [ rsp + 0x5c8 ]
seto r9b
mov [ rsp + 0x5f8 ], r15
mov r15, 0x0 
dec r15
movzx r12, r12b
adox r12, r15
adox r13, [ rsp + 0x5a8 ]
setc r12b
seto r15b
mov [ rsp + 0x600 ], r13
movzx r13, r11b
add r13, -0x1
mov r11, rcx
mov r13, 0xffffffffffffffff 
sbb r11, r13
mov r13, 0x0 
dec r13
movzx r12, r12b
adox r12, r13
adox rax, [ rsp + 0x5e0 ]
setc r12b
clc
movzx rdx, dl
adcx rdx, r13
adcx rbp, [ rsp + 0x448 ]
movzx rdx, r15b
mov r13, [ rsp + 0x5b8 ]
lea rdx, [ rdx + r13 ]
seto r13b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r14, r14b
adox r14, r15
adox rbp, [ rsp + 0x5c0 ]
seto r14b
adc r14b, 0x0
movzx r14, r14b
add r13b, 0xFF
adcx r10, r8
setc r8b
movzx r13, r12b
add r13, -0x1
mov r12, rax
mov r13, 0xffffffffffffffff 
sbb r12, r13
mov r15, r10
mov r13, 0xfdc1767ae2ffffff 
sbb r15, r13
mov r13, 0x0 
dec r13
movzx r9, r9b
adox r9, r13
adox rbx, [ rsp + 0x288 ]
adox rbp, [ rsp + 0x390 ]
movzx r14, r14b
movzx r9, r14b
adox r9, [ rsp + 0x3c8 ]
seto r14b
inc r13
mov r13, -0x1 
movzx r8, r8b
adox r8, r13
adox rbx, [ rsp + 0x5f8 ]
adox rbp, [ rsp + 0x600 ]
seto r8b
mov r13, rbx
mov [ rsp + 0x608 ], r11
mov r11, 0x7bc65c783158aea3 
sbb r13, r11
mov r11, rbp
mov [ rsp + 0x610 ], r13
mov r13, 0x6cfc5fd681c52056 
sbb r11, r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r8, r8b
adox r8, r13
adox r9, rdx
movzx rdx, r14b
mov r8, 0x0 
adox rdx, r8
mov r14, r9
mov r8, 0x2341f27177344 
sbb r14, r8
sbb rdx, 0x00000000
cmovc r12, rax
cmovc r15, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r15
mov rax, [ rsp + 0x610 ]
cmovc rax, rbx
mov [ rdx + 0x20 ], rax
cmovc r14, r9
mov r10, [ rsp + 0x5f0 ]
cmovc r10, rdi
mov [ rdx + 0x10 ], r12
mov [ rdx + 0x0 ], r10
cmovc r11, rbp
mov rdi, [ rsp + 0x608 ]
cmovc rdi, rcx
mov [ rdx + 0x8 ], rdi
mov [ rdx + 0x30 ], r14
mov [ rdx + 0x28 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1688
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1875
; seed 3825477577193012 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 64956 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 925 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.014240408892173163
; number reverted permutation / tried permutation: 266 / 482 =55.187%
; number reverted decision / tried decision: 270 / 517 =52.224%
; validated in 264.305s
