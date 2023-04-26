SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1736
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], r15
mulx r15, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r8
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], r9
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], r9
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], rax
mulx rax, r15, r8
mov rdx, 0x2341f27177344 
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r13
mulx r13, r14, r8
xor rdx, rdx
adox rbx, r10
mov r10, r15
adcx r10, rax
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], r14
mulx r14, r13, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], rbx
mulx rbx, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], rdi
mulx rdi, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], rdi
mov [ rsp + 0x88 ], rbx
mulx rbx, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], rbx
mulx rbx, rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], rbx
mov [ rsp + 0xb8 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], rbx
mulx rbx, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], rdi
mov [ rsp + 0xe8 ], rbx
mulx rbx, rdi, [ rsi + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], rdi
mulx rdi, rbx, r8
mov rdx, r15
adcx rdx, rax
adcx rbx, rax
adox r12, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x100 ], r12
mulx r12, rax, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x108 ], r12
mov [ rsp + 0x110 ], rax
mulx rax, r12, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], rbx
mov [ rsp + 0x120 ], rbp
mulx rbp, rbx, rdx
adcx r12, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], rbp
mulx rbp, rdi, [ rsi + 0x0 ]
adcx r13, rax
seto dl
mov rax, -0x2 
inc rax
adox rdi, r9
adox r11, rbp
mov r9b, dl
mov rdx, [ rsi + 0x30 ]
mulx rax, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], rax
mov [ rsp + 0x138 ], rbp
mulx rbp, rax, rdx
adox r14, rcx
setc dl
clc
adcx r15, r8
adcx r10, rdi
mov r15, [ rsp + 0x60 ]
adox r15, [ rsp + 0x68 ]
mov rcx, [ rsp + 0x38 ]
adox rcx, [ rsp + 0x30 ]
mov r8b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], rbp
mulx rbp, rdi, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x148 ], rax
mov rax, -0x2 
inc rax
adox r10, [ rsp + 0x28 ]
mov rax, 0xffffffffffffffff 
xchg rdx, rax
mov [ rsp + 0x150 ], rbx
mov byte [ rsp + 0x158 ], r8b
mulx r8, rbx, r10
mov rdx, rbx
mov byte [ rsp + 0x160 ], al
seto al
mov [ rsp + 0x168 ], r13
mov r13, -0x2 
inc r13
adox rdx, r10
adcx r11, [ rsp + 0x120 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x170 ], rcx
mulx rcx, r13, r10
adcx r14, [ rsp + 0x118 ]
seto dl
mov [ rsp + 0x178 ], rcx
mov rcx, -0x2 
inc rcx
adox rbp, [ rsp + 0x20 ]
adcx r12, r15
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x180 ], rbp
mulx rbp, rcx, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x188 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rax, al
adox rax, rbp
adox r11, [ rsp + 0x58 ]
adox r14, [ rsp + 0x100 ]
mov rax, 0x7bc65c783158aea3 
xchg rdx, r10
mov [ rsp + 0x190 ], rcx
mulx rcx, rbp, rax
mov rax, rbx
mov byte [ rsp + 0x198 ], r10b
setc r10b
clc
adcx rax, r8
adcx rbx, r8
mov [ rsp + 0x1a0 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x1a8 ], r10b
mov [ rsp + 0x1b0 ], r13
mulx r13, r10, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x1b8 ], rcx
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox r11, rax
setc r15b
clc
adcx r10, r11
mov rax, 0xffffffffffffffff 
xchg rdx, rax
mulx rcx, r11, r10
mov rdx, r11
mov byte [ rsp + 0x1c0 ], al
seto al
mov [ rsp + 0x1c8 ], rbp
mov rbp, -0x2 
inc rbp
adox rdx, r10
mov rdx, r11
setc bpl
clc
adcx rdx, rcx
mov byte [ rsp + 0x1d0 ], r9b
mov r9, 0x2341f27177344 
xchg rdx, r12
mov byte [ rsp + 0x1d8 ], r15b
mov [ rsp + 0x1e0 ], rdi
mulx rdi, r15, r9
adcx r11, rcx
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e8 ], r11
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r11, [ rsi + 0x8 ]
setc dl
clc
adcx r11, r13
setc r13b
clc
mov [ rsp + 0x1f8 ], rdi
mov rdi, -0x1 
movzx rax, al
adcx rax, rdi
adcx r14, rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, r10
mulx rdi, rax, rbx
setc bl
clc
mov byte [ rsp + 0x200 ], r13b
mov r13, -0x1 
movzx rbp, bpl
adcx rbp, r13
adcx r14, r11
adox r12, r14
mov rbp, 0x6cfc5fd681c52056 
mulx r14, r11, rbp
setc r13b
clc
adcx r12, [ rsp + 0x1e0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], r14
mov byte [ rsp + 0x210 ], r13b
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x218 ], r11
mov [ rsp + 0x220 ], rdi
mulx rdi, r11, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x228 ], rdi
mov [ rsp + 0x230 ], r11
mulx r11, rdi, r12
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x238 ], bl
mov [ rsp + 0x240 ], rax
mulx rax, rbx, [ rsi + 0x30 ]
mov rdx, rdi
mov [ rsp + 0x248 ], rax
seto al
mov byte [ rsp + 0x250 ], r10b
mov r10, -0x2 
inc r10
adox rdx, r11
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov [ rsp + 0x258 ], r9
mov byte [ rsp + 0x260 ], al
mulx rax, r9, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x268 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
setc dl
mov [ rsp + 0x270 ], rbx
movzx rbx, byte [ rsp + 0x1d8 ]
clc
mov [ rsp + 0x278 ], r15
mov r15, -0x1 
adcx rbx, r15
adcx r8, r9
setc bl
movzx r9, byte [ rsp + 0x1d0 ]
clc
adcx r9, r15
adcx r14, [ rsp - 0x8 ]
adcx r10, r13
setc r9b
clc
movzx rbx, bl
adcx rbx, r15
adcx rax, [ rsp + 0x1c8 ]
mov r13, rdi
adox r13, r11
mov rbx, [ rsp + 0x1b8 ]
adcx rbx, [ rsp + 0x1b0 ]
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x280 ], rbx
mov [ rsp + 0x288 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x290 ], r15b
mov [ rsp + 0x298 ], rax
mulx rax, r15, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x178 ]
adcx rdx, [ rsp + 0x278 ]
mov [ rsp + 0x2a0 ], rdx
seto dl
mov [ rsp + 0x2a8 ], rax
mov rax, 0x0 
dec rax
movzx r9, r9b
adox r9, rax
adox rbx, [ rsp + 0x270 ]
adox r13, [ rsp + 0x268 ]
setc r9b
movzx rax, byte [ rsp + 0x250 ]
clc
mov byte [ rsp + 0x2b0 ], dl
mov rdx, -0x1 
adcx rax, rdx
adcx rcx, [ rsp + 0x240 ]
mov rax, [ rsp + 0x248 ]
mov rdx, 0x0 
adox rax, rdx
mov rdx, [ rsp + 0x170 ]
mov [ rsp + 0x2b8 ], rax
movzx rax, byte [ rsp + 0x1a8 ]
mov [ rsp + 0x2c0 ], r13
mov r13, 0x0 
dec r13
adox rax, r13
adox rdx, [ rsp + 0x168 ]
setc al
movzx r13, byte [ rsp + 0x1c0 ]
clc
mov [ rsp + 0x2c8 ], rbx
mov rbx, -0x1 
adcx r13, rbx
adcx r14, [ rsp + 0x1a0 ]
adcx r10, rdx
mov r13, 0x7bc65c783158aea3 
mov rdx, rbp
mulx rbx, rbp, r13
seto r13b
mov [ rsp + 0x2d0 ], rcx
movzx rcx, byte [ rsp + 0x238 ]
mov [ rsp + 0x2d8 ], r10
mov r10, 0x0 
dec r10
adox rcx, r10
adox r14, r8
setc cl
clc
movzx rax, al
adcx rax, r10
adcx rbp, [ rsp + 0x220 ]
adcx rbx, [ rsp + 0x218 ]
movzx r8, r9b
mov rax, [ rsp + 0x1f0 ]
lea r8, [ r8 + rax ]
mov rax, [ rsp + 0x1f8 ]
setc r9b
movzx r10, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x2e0 ], rbx
mov rbx, -0x1 
adcx r10, rbx
adcx rax, [ rsp + 0xb8 ]
adcx r15, [ rsp + 0xb0 ]
mov r10, [ rsp + 0x2a8 ]
adcx r10, [ rsp + 0x8 ]
mov rbx, [ rsp + 0x0 ]
adcx rbx, [ rsp + 0x18 ]
mov [ rsp + 0x2e8 ], rbx
mov rbx, [ rsp + 0x298 ]
adox rbx, [ rsp + 0x2d8 ]
mov [ rsp + 0x2f0 ], r8
mov r8, [ rsp + 0x78 ]
adcx r8, [ rsp + 0x10 ]
mov [ rsp + 0x2f8 ], r8
setc r8b
mov byte [ rsp + 0x300 ], r9b
movzx r9, byte [ rsp + 0x210 ]
clc
mov [ rsp + 0x308 ], rbp
mov rbp, -0x1 
adcx r9, rbp
adcx r14, rax
seto r9b
movzx rax, byte [ rsp + 0x260 ]
inc rbp
mov rbp, -0x1 
adox rax, rbp
adox r14, [ rsp + 0x1e8 ]
adcx r15, rbx
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, [ rsi + 0x0 ]
setc dl
mov [ rsp + 0x310 ], rbp
movzx rbp, byte [ rsp + 0x290 ]
clc
mov [ rsp + 0x318 ], r10
mov r10, -0x1 
adcx rbp, r10
adcx r14, [ rsp + 0x180 ]
adox r15, [ rsp + 0x2d0 ]
seto bpl
inc r10
adox rdi, r12
mov rdi, [ rsp - 0x28 ]
setc r10b
mov byte [ rsp + 0x320 ], bpl
movzx rbp, byte [ rsp + 0x160 ]
clc
mov byte [ rsp + 0x328 ], dl
mov rdx, -0x1 
adcx rbp, rdx
adcx rdi, [ rsp + 0xf8 ]
adox r14, [ rsp + 0x258 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x330 ], r9b
mulx r9, rbp, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x48 ]
mov [ rsp + 0x338 ], r9
seto r9b
mov [ rsp + 0x340 ], rbp
movzx rbp, byte [ rsp + 0x158 ]
mov byte [ rsp + 0x348 ], cl
mov rcx, 0x0 
dec rcx
adox rbp, rcx
adox rdx, [ rsp + 0x50 ]
mov rbp, [ rsp + 0x40 ]
mov rcx, 0x0 
adox rbp, rcx
mov byte [ rsp + 0x350 ], r9b
mov r9, -0x3 
inc r9
adox rbx, r14
mov r14, 0xffffffffffffffff 
xchg rdx, rbx
mulx r9, rcx, r14
seto r14b
mov [ rsp + 0x358 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r13, r13b
adox r13, r9
adox rdi, rbx
mov r13, rcx
seto bl
inc r9
adox r13, rdx
mov r13, 0x7bc65c783158aea3 
mov byte [ rsp + 0x360 ], r14b
mulx r14, r9, r13
movzx r13, r8b
mov [ rsp + 0x368 ], r14
mov r14, [ rsp + 0x70 ]
lea r13, [ r13 + r14 ]
mov r14, [ rsp - 0x10 ]
setc r8b
mov [ rsp + 0x370 ], r9
movzx r9, byte [ rsp + 0x198 ]
clc
mov [ rsp + 0x378 ], r13
mov r13, -0x1 
adcx r9, r13
adcx r14, [ rsp + 0xa8 ]
setc r9b
clc
movzx r10, r10b
adcx r10, r13
adcx r15, r14
movzx r10, r8b
mov r14, [ rsp + 0xf0 ]
lea r10, [ r10 + r14 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, r13
adcx r10, rbp
mov r8, 0xfdc1767ae2ffffff 
mulx rbx, rbp, r8
seto r13b
movzx r8, byte [ rsp + 0x350 ]
mov [ rsp + 0x380 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r8, rbx
adox r15, [ rsp + 0x288 ]
mov r8, rcx
seto bl
mov [ rsp + 0x388 ], rbp
mov rbp, -0x2 
inc rbp
adox r8, [ rsp + 0x358 ]
mov rbp, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x390 ], bl
mov byte [ rsp + 0x398 ], r14b
mulx r14, rbx, rbp
seto bpl
mov [ rsp + 0x3a0 ], r14
movzx r14, byte [ rsp + 0x348 ]
mov [ rsp + 0x3a8 ], rbx
mov rbx, 0x0 
dec rbx
adox r14, rbx
adox rdi, [ rsp + 0x2c8 ]
adox r10, [ rsp + 0x2c0 ]
mov r14, [ rsp + 0x150 ]
setc bl
clc
mov byte [ rsp + 0x3b0 ], bpl
mov rbp, -0x1 
movzx r9, r9b
adcx r9, rbp
adcx r14, [ rsp + 0xa0 ]
mov r9, [ rsp + 0x128 ]
adcx r9, [ rsp - 0x18 ]
movzx rbx, bl
movzx rbp, bl
adox rbp, [ rsp + 0x2b8 ]
seto bl
mov [ rsp + 0x3b8 ], r9
movzx r9, byte [ rsp + 0x330 ]
mov [ rsp + 0x3c0 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox r9, rbp
adox rdi, [ rsp + 0x280 ]
seto r9b
movzx rbp, byte [ rsp + 0x328 ]
mov byte [ rsp + 0x3c8 ], bl
mov rbx, 0x0 
dec rbx
adox rbp, rbx
adox rdi, [ rsp + 0x318 ]
seto bpl
movzx rbx, byte [ rsp + 0x320 ]
mov [ rsp + 0x3d0 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rbx, r14
adox rdi, [ rsp + 0x308 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x3d8 ], bpl
mulx rbp, r14, rdx
seto dl
mov [ rsp + 0x3e0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox r10, [ rsp + 0x2a0 ]
mov r9, [ rsp + 0x310 ]
setc bpl
clc
adcx r9, [ rsp + 0xd8 ]
mov byte [ rsp + 0x3e8 ], dl
mov rdx, [ rsp + 0x88 ]
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x3f0 ], rdx
mov rdx, [ rsp + 0x80 ]
adcx rdx, [ rsp + 0x340 ]
mov [ rsp + 0x3f8 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x400 ], r10
mov byte [ rsp + 0x408 ], bpl
mulx rbp, r10, rax
mov rax, 0xfdc1767ae2ffffff 
mov rdx, rax
mov [ rsp + 0x410 ], rbp
mulx rbp, rax, r12
adcx r14, [ rsp + 0x338 ]
setc dl
mov [ rsp + 0x418 ], r14
movzx r14, byte [ rsp + 0x2b0 ]
clc
mov [ rsp + 0x420 ], rbp
mov rbp, -0x1 
adcx r14, rbp
adcx r11, rax
setc r14b
movzx rax, byte [ rsp + 0x300 ]
clc
adcx rax, rbp
adcx r10, [ rsp + 0x208 ]
seto al
movzx rbp, byte [ rsp + 0x360 ]
mov byte [ rsp + 0x428 ], dl
mov rdx, 0x0 
dec rdx
adox rbp, rdx
adox r15, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rsi + 0x28 ]
setc dl
clc
mov [ rsp + 0x430 ], r9
mov r9, -0x1 
movzx r13, r13b
adcx r13, r9
adcx r15, r8
mov r13, 0x7bc65c783158aea3 
xchg rdx, r12
mulx r9, r8, r13
seto r13b
mov byte [ rsp + 0x438 ], r12b
mov r12, -0x2 
inc r12
adox rbp, r15
seto r15b
movzx r12, byte [ rsp + 0x398 ]
mov [ rsp + 0x440 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r12, r10
adox rdi, [ rsp + 0x3d0 ]
mov r12, [ rsp + 0x2f0 ]
setc r10b
clc
mov byte [ rsp + 0x448 ], r15b
mov r15, -0x1 
movzx rax, al
adcx rax, r15
adcx r12, [ rsp + 0x3c0 ]
movzx rax, byte [ rsp + 0x3c8 ]
mov r15, 0x0 
adcx rax, r15
clc
mov r15, -0x1 
movzx r14, r14b
adcx r14, r15
adcx r8, [ rsp + 0x420 ]
seto r14b
movzx r15, byte [ rsp + 0x390 ]
mov byte [ rsp + 0x450 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r15, r10
adox rdi, r11
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rsi + 0x30 ]
adcx r9, [ rsp + 0x230 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x458 ], r11
mov [ rsp + 0x460 ], r9
mulx r9, r11, rbp
mov rdx, r11
mov [ rsp + 0x468 ], r8
setc r8b
clc
adcx rdx, r9
mov [ rsp + 0x470 ], rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x478 ], r10
mov byte [ rsp + 0x480 ], r14b
mulx r14, r10, rbp
mov rdx, 0x2341f27177344 
mov [ rsp + 0x488 ], r14
mov [ rsp + 0x490 ], r10
mulx r10, r14, r15
mov r15, [ rsp - 0x20 ]
seto dl
mov [ rsp + 0x498 ], rdi
movzx rdi, byte [ rsp + 0x408 ]
mov byte [ rsp + 0x4a0 ], r13b
mov r13, 0x0 
dec r13
adox rdi, r13
adox r15, [ rsp - 0x30 ]
mov rdi, r11
adcx rdi, r9
mov r13, 0x2341f27177344 
xchg rdx, rbp
mov [ rsp + 0x4a8 ], rdi
mov byte [ rsp + 0x4b0 ], bpl
mulx rbp, rdi, r13
mov r13, [ rsp + 0x400 ]
mov [ rsp + 0x4b8 ], rbp
seto bpl
mov [ rsp + 0x4c0 ], rdi
movzx rdi, byte [ rsp + 0x3d8 ]
mov [ rsp + 0x4c8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rdi, r15
adox r13, [ rsp + 0x2e8 ]
seto dil
inc r15
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox r14, [ rsp + 0x228 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, r15
adcx r12, [ rsp + 0x2f8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x4d0 ], r14
mulx r14, r15, [ rsi + 0x18 ]
adcx rax, [ rsp + 0x378 ]
mov rdx, 0x0 
adox r10, rdx
movzx rdx, byte [ rsp + 0x3b0 ]
mov [ rsp + 0x4d8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rdx, r14
adox rcx, [ rsp + 0x358 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x4e0 ], r10
mulx r10, r14, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x4e8 ], r10
movzx r10, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x4f0 ], rax
mov rax, 0x0 
dec rax
adox r10, rax
adox r13, [ rsp + 0x2e0 ]
mov r10, [ rsp + 0x498 ]
setc al
mov [ rsp + 0x4f8 ], r14
movzx r14, byte [ rsp + 0x4a0 ]
clc
mov [ rsp + 0x500 ], rcx
mov rcx, -0x1 
adcx r14, rcx
adcx r10, [ rsp + 0x3f0 ]
mov r14b, dl
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x508 ], al
mulx rax, rcx, [ rsi + 0x28 ]
adox r12, [ rsp + 0x440 ]
mov rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x510 ], rax
seto al
mov [ rsp + 0x518 ], rcx
mov rcx, 0x0 
dec rcx
movzx rbp, bpl
adox rbp, rcx
adox rdx, [ rsp - 0x38 ]
seto bpl
inc rcx
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox r9, [ rsp + 0x490 ]
movzx r8, bpl
mov rcx, [ rsp + 0xc0 ]
lea r8, [ r8 + rcx ]
setc cl
movzx rbp, byte [ rsp + 0x480 ]
clc
mov [ rsp + 0x520 ], r8
mov r8, -0x1 
adcx rbp, r8
adcx r13, [ rsp + 0x3b8 ]
mov rbp, [ rsp + 0x98 ]
seto r8b
mov [ rsp + 0x528 ], r9
mov r9, -0x2 
inc r9
adox rbp, [ rsp + 0x478 ]
adcx r12, [ rsp + 0x4c8 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x530 ], rbp
mov byte [ rsp + 0x538 ], r8b
mulx r8, rbp, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xe8 ]
adox rdx, [ rsp + 0x90 ]
mov [ rsp + 0x540 ], rdx
seto dl
mov [ rsp + 0x548 ], r9
movzx r9, byte [ rsp + 0x4b0 ]
mov byte [ rsp + 0x550 ], al
mov rax, 0x0 
dec rax
adox r9, rax
adox r13, [ rsp + 0x468 ]
adox r12, [ rsp + 0x460 ]
setc r9b
movzx rax, byte [ rsp + 0x428 ]
clc
mov [ rsp + 0x558 ], r10
mov r10, -0x1 
adcx rax, r10
adcx rbp, [ rsp + 0x3e0 ]
setc al
clc
movzx rdx, dl
adcx rdx, r10
adcx r15, [ rsp + 0xe0 ]
seto dl
inc r10
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox r13, [ rsp + 0x3f8 ]
adox r12, [ rsp + 0x418 ]
mov rcx, [ rsp + 0x358 ]
setc r10b
clc
mov [ rsp + 0x560 ], r15
mov r15, -0x1 
movzx r14, r14b
adcx r14, r15
adcx rcx, [ rsp + 0x388 ]
seto r14b
inc r15
mov r15, -0x1 
movzx rax, al
adox rax, r15
adox r8, [ rsp - 0x40 ]
mov rax, [ rsp - 0x48 ]
mov r15, 0x0 
adox rax, r15
mov byte [ rsp + 0x568 ], r10b
mov r10, [ rsp + 0x430 ]
mov [ rsp + 0x570 ], rax
mov rax, -0x3 
inc rax
adox r10, [ rsp + 0x190 ]
mov r15, [ rsp + 0x558 ]
setc al
mov [ rsp + 0x578 ], r8
movzx r8, byte [ rsp + 0x450 ]
clc
mov [ rsp + 0x580 ], rbp
mov rbp, -0x1 
adcx r8, rbp
adcx r15, [ rsp + 0x500 ]
mov r8, [ rsp + 0x380 ]
seto bpl
mov byte [ rsp + 0x588 ], r14b
mov r14, 0x0 
dec r14
movzx rax, al
adox rax, r14
adox r8, [ rsp + 0x370 ]
adcx rcx, r13
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mulx r14, rax, [ rsi + 0x28 ]
adcx r8, r12
mov rdx, [ rsp + 0x518 ]
seto r12b
mov byte [ rsp + 0x590 ], r13b
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbp, bpl
adox rbp, r13
adox rdx, [ rsp + 0x188 ]
movzx rbp, byte [ rsp + 0x438 ]
mov r13, [ rsp + 0x410 ]
lea rbp, [ rbp + r13 ]
adox rax, [ rsp + 0x510 ]
adox r14, [ rsp + 0x4f8 ]
setc r13b
mov [ rsp + 0x598 ], r14
movzx r14, byte [ rsp + 0x550 ]
clc
mov byte [ rsp + 0x5a0 ], r12b
mov r12, -0x1 
adcx r14, r12
adcx rbp, [ rsp + 0x4f0 ]
seto r14b
inc r12
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox rbp, [ rsp + 0x548 ]
seto r9b
movzx r12, byte [ rsp + 0x448 ]
mov byte [ rsp + 0x5a8 ], r14b
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r12, r14
adox r15, r10
setc r12b
clc
adcx r11, rdi
adcx r15, [ rsp + 0x470 ]
adox rdx, rcx
adox rax, r8
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx rcx, r10, [ rsi + 0x30 ]
adcx r11, [ rsp + 0x4a8 ]
mov rdx, 0x2341f27177344 
mulx r14, r8, rbx
adcx rax, [ rsp + 0x528 ]
mov rbx, [ rsp + 0x368 ]
seto dl
mov [ rsp + 0x5b0 ], rcx
movzx rcx, byte [ rsp + 0x5a0 ]
mov [ rsp + 0x5b8 ], r10
mov r10, 0x0 
dec r10
adox rcx, r10
adox rbx, [ rsp + 0x3a8 ]
movzx rcx, r12b
movzx r10, byte [ rsp + 0x508 ]
lea rcx, [ rcx + r10 ]
adox r8, [ rsp + 0x3a0 ]
setc r10b
movzx r12, byte [ rsp + 0x590 ]
clc
mov [ rsp + 0x5c0 ], rax
mov rax, -0x1 
adcx r12, rax
adcx rbp, [ rsp + 0x4d0 ]
mov r12, 0x0 
adox r14, r12
inc rax
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox rcx, [ rsp + 0x520 ]
adcx rcx, [ rsp + 0x4e0 ]
seto r9b
adc r9b, 0x0
movzx r9, r9b
add byte [ rsp + 0x588 ], 0x7F
adox rbp, [ rsp + 0x580 ]
adox rcx, [ rsp + 0x578 ]
movzx r13, r13b
adcx r13, r12
adcx rbp, rbx
adcx r8, rcx
movzx r9, r9b
movzx r13, r9b
adox r13, [ rsp + 0x570 ]
adcx r14, r13
seto bl
adc bl, 0x0
movzx rbx, bl
add dl, 0x7F
adox rbp, [ rsp + 0x598 ]
adcx r15, [ rsp + 0x458 ]
mov rdx, [ rsp + 0x4e8 ]
seto r9b
movzx rcx, byte [ rsp + 0x5a8 ]
dec rax
adox rcx, rax
adox rdx, [ rsp + 0x110 ]
seto r12b
inc rax
mov rcx, -0x1 
movzx r9, r9b
adox r9, rcx
adox r8, rdx
mov r13, 0x7bc65c783158aea3 
mov rdx, r13
mulx r9, r13, rdi
mov rax, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, rax
mov rax, r15
mov byte [ rsp + 0x5c8 ], bl
setc bl
clc
adcx rax, rcx
mov [ rsp + 0x5d0 ], r14
mov r14, r15
adcx r14, rcx
mov [ rsp + 0x5d8 ], r14
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r14
mov byte [ rsp + 0x5e0 ], r12b
mov [ rsp + 0x5e8 ], r8
mulx r8, r12, rdi
seto dil
movzx rdx, byte [ rsp + 0x538 ]
mov [ rsp + 0x5f0 ], rbp
mov rbp, 0x0 
dec rbp
adox rdx, rbp
adox r13, [ rsp + 0x488 ]
seto dl
inc rbp
mov rbp, -0x1 
movzx rbx, bl
adox rbx, rbp
adox r11, [ rsp + 0x530 ]
seto bl
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r9, r12
seto r12b
inc rbp
adox r15, r14
mov r15, 0x7bc65c783158aea3 
mov rdx, r14
mulx rbp, r14, r15
seto r15b
mov [ rsp + 0x5f8 ], rbp
mov rbp, 0x0 
dec rbp
movzx r12, r12b
adox r12, rbp
adox r8, [ rsp + 0x4c0 ]
seto r12b
inc rbp
mov rbp, -0x1 
movzx r15, r15b
adox r15, rbp
adox r11, rax
mov rax, 0xfdc1767ae2ffffff 
mulx rbp, r15, rax
adcx r15, rcx
seto cl
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx r10, r10b
adox r10, rax
adox r13, [ rsp + 0x5f0 ]
adox r9, [ rsp + 0x5e8 ]
mov r10, [ rsp + 0x5c0 ]
setc al
clc
mov [ rsp + 0x600 ], r15
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx r10, [ rsp + 0x540 ]
adcx r13, [ rsp + 0x560 ]
mov rbx, [ rsp + 0x108 ]
setc r15b
mov [ rsp + 0x608 ], r13
movzx r13, byte [ rsp + 0x5e0 ]
clc
mov [ rsp + 0x610 ], r10
mov r10, -0x1 
adcx r13, r10
adcx rbx, [ rsp + 0x138 ]
seto r13b
inc r10
mov r10, -0x1 
movzx rdi, dil
adox rdi, r10
adox rbx, [ rsp + 0x5d0 ]
mov rdi, [ rsp + 0x130 ]
mov r10, 0x0 
adcx rdi, r10
clc
mov r10, -0x1 
movzx rax, al
adcx rax, r10
adcx rbp, r14
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x30 ]
setc dl
mov [ rsp + 0x618 ], rbp
seto bpl
mov byte [ rsp + 0x620 ], cl
mov rcx, r11
mov [ rsp + 0x628 ], r9
mov r9, 0xffffffffffffffff 
sub rcx, r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
mov [ rsp + 0x630 ], rcx
movzx rcx, byte [ rsp + 0x5c8 ]
movzx rbp, bpl
adox rbp, r9
adox rdi, rcx
setc cl
clc
movzx r13, r13b
adcx r13, r9
adcx rbx, r8
mov r8, 0x2341f27177344 
xchg rdx, r8
mulx rbp, r13, r14
mov r9, 0x6cfc5fd681c52056 
mov rdx, r14
mov byte [ rsp + 0x638 ], cl
mulx rcx, r14, r9
seto dl
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox r14, [ rsp + 0x5f8 ]
adox r13, rcx
seto r8b
movzx rcx, byte [ rsp + 0x568 ]
inc r9
mov r9, -0x1 
adox rcx, r9
adox rax, [ rsp + 0x4d8 ]
movzx rcx, r12b
mov r9, [ rsp + 0x4b8 ]
lea rcx, [ rcx + r9 ]
movzx r9, r8b
lea r9, [ r9 + rbp ]
adcx rcx, rdi
adox r10, [ rsp + 0x5b8 ]
mov r12, [ rsp + 0x148 ]
adox r12, [ rsp + 0x5b0 ]
movzx rdi, dl
mov rbp, 0x0 
adcx rdi, rbp
clc
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx rax, [ rsp + 0x628 ]
mov r15, [ rsp + 0x140 ]
adox r15, rbp
mov r8, [ rsp + 0x610 ]
movzx rbp, byte [ rsp + 0x620 ]
inc rdx
mov rdx, -0x1 
adox rbp, rdx
adox r8, [ rsp + 0x5d8 ]
adcx r10, rbx
mov rbp, [ rsp + 0x608 ]
adox rbp, [ rsp + 0x600 ]
adox rax, [ rsp + 0x618 ]
adcx r12, rcx
adox r14, r10
adox r13, r12
adcx r15, rdi
adox r9, r15
setc bl
seto cl
movzx rdi, byte [ rsp + 0x638 ]
add rdi, -0x1
mov rdi, r8
mov r10, 0xffffffffffffffff 
sbb rdi, r10
movzx r12, cl
movzx rbx, bl
lea r12, [ r12 + rbx ]
mov rbx, rbp
sbb rbx, r10
mov r15, rax
mov rcx, 0xfdc1767ae2ffffff 
sbb r15, rcx
mov rdx, r14
mov rcx, 0x7bc65c783158aea3 
sbb rdx, rcx
mov rcx, r13
mov r10, 0x6cfc5fd681c52056 
sbb rcx, r10
mov r10, r9
mov [ rsp + 0x640 ], rdx
mov rdx, 0x2341f27177344 
sbb r10, rdx
sbb r12, 0x00000000
cmovc r10, r9
cmovc rdi, r8
cmovc rbx, rbp
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x30 ], r10
cmovc r15, rax
cmovc rcx, r13
mov [ r12 + 0x18 ], r15
mov [ r12 + 0x10 ], rbx
mov [ r12 + 0x28 ], rcx
mov r8, [ rsp + 0x630 ]
cmovc r8, r11
mov r11, [ rsp + 0x640 ]
cmovc r11, r14
mov [ r12 + 0x20 ], r11
mov [ r12 + 0x8 ], rdi
mov [ r12 + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1736
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1719
; seed 3468694270907004 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10734170 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 165567 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.015424294565858376
; number reverted permutation / tried permutation: 51742 / 89977 =57.506%
; number reverted decision / tried decision: 45997 / 90022 =51.095%
; validated in 260.753s
