SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1728
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r8
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rcx
mulx rcx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r15
mulx r15, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], r14
mulx r14, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], r13
mulx r13, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], r15
mulx r15, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r11
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r8
mov [ rsp + 0x70 ], r11
mulx r11, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r12
mulx r12, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r10
mulx r10, r12, [ rax + 0x0 ]
test al, al
adox rdi, r10
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x98 ], rdi
mulx rdi, r10, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa0 ], r12
mov [ rsp + 0xa8 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], r10
mulx r10, r12, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r10
mov [ rsp + 0xc8 ], r12
mulx r12, r10, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r10
mulx r10, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r10
mov [ rsp + 0xe8 ], r12
mulx r12, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xf0 ], rdi
mov [ rsp + 0xf8 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], rdi
mulx rdi, r15, [ rax + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], r15
mulx r15, rdi, [ rax + 0x18 ]
adcx r10, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x120 ], r15
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], rdi
mov [ rsp + 0x130 ], r10
mulx r10, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x138 ], r15
mov [ rsp + 0x140 ], r11
mulx r11, r15, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x148 ], r11
mov [ rsp + 0x150 ], r15
mulx r15, r11, [ rsi + 0x28 ]
adcx r14, r12
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x158 ], r14
mulx r14, r12, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x160 ], r12
mov r12, -0x2 
inc r12
adox rdi, r14
mov r14b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x168 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
seto dl
mov byte [ rsp + 0x170 ], r14b
mov r14, -0x2 
inc r14
adox r9, rbx
adox r12, rcx
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], rcx
mulx rcx, r14, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], r12
mov [ rsp + 0x190 ], r9
mulx r9, r12, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x198 ], r15
mov r15, 0x0 
dec r15
movzx rbx, bl
adox rbx, r15
adox r10, rbp
mov bpl, dl
mov rdx, [ rax + 0x8 ]
mulx r15, rbx, [ rsi + 0x18 ]
mov rdx, r14
mov [ rsp + 0x1a0 ], r10
setc r10b
clc
adcx rdx, r8
mov rdx, r14
mov byte [ rsp + 0x1a8 ], r10b
setc r10b
clc
adcx rdx, rcx
mov [ rsp + 0x1b0 ], rdx
seto dl
mov byte [ rsp + 0x1b8 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rdi, r13
adox r12, [ rsp + 0xf8 ]
adox r9, [ rsp + 0x80 ]
mov r13b, dl
mov rdx, [ rax + 0x30 ]
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1c0 ], r9
mov [ rsp + 0x1c8 ], r12
mulx r12, r9, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], r10
mulx r10, rdi, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x1e0 ], rdi
mov rdi, -0x2 
inc rdi
adox rbx, [ rsp + 0xf0 ]
adox r15, [ rsp + 0x140 ]
mov dil, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1e8 ], r15
mov [ rsp + 0x1f0 ], rbx
mulx rbx, r15, [ rsi + 0x18 ]
adcx r14, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], r14
mov [ rsp + 0x200 ], rbp
mulx rbp, r14, [ rax + 0x10 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x208 ], rbx
mov byte [ rsp + 0x210 ], r13b
mulx r13, rbx, r8
adcx rbx, rcx
mov r8, [ rsp + 0x138 ]
adox r8, [ rsp + 0x78 ]
adox r15, [ rsp + 0x60 ]
mov rcx, [ rsp + 0x58 ]
seto dl
mov [ rsp + 0x218 ], r15
mov r15, 0x0 
dec r15
movzx rdi, dil
adox rdi, r15
adox rcx, [ rsp + 0x150 ]
mov dil, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x220 ], r8
mulx r8, r15, [ rax + 0x30 ]
adcx r9, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x228 ], rcx
mulx rcx, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x230 ], r9
mov [ rsp + 0x238 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
adcx r12, [ rsp + 0xb8 ]
mov rdx, [ rsp + 0xa8 ]
adcx rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x240 ], rdx
setc dl
clc
adcx r10, [ rsp + 0x40 ]
mov [ rsp + 0x248 ], r10
mov r10, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x10 ]
mov [ rsp + 0x250 ], r10
mov r10, [ rsp + 0x148 ]
mov [ rsp + 0x258 ], r12
mov r12, 0x0 
adox r10, r12
adcx r11, [ rsp + 0x8 ]
mov [ rsp + 0x260 ], r11
mov r11, -0x3 
inc r11
adox r9, [ rsp + 0x70 ]
mov r12, [ rsp + 0x198 ]
adcx r12, [ rsp + 0x30 ]
mov r11b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x268 ], r12
mov [ rsp + 0x270 ], r10
mulx r10, r12, [ rsi + 0x30 ]
adox rbx, [ rsp - 0x10 ]
seto dl
mov [ rsp + 0x278 ], rbx
movzx rbx, byte [ rsp + 0x170 ]
mov [ rsp + 0x280 ], r9
mov r9, 0x0 
dec r9
adox rbx, r9
adox r14, [ rsp + 0x18 ]
mov rbx, [ rsp - 0x18 ]
setc r9b
clc
mov [ rsp + 0x288 ], r14
mov r14, -0x1 
movzx rdx, dl
adcx rdx, r14
adcx rbx, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x28 ]
movzx rdx, r11b
mov r14, [ rsp + 0xc0 ]
lea rdx, [ rdx + r14 ]
mov r14, [ rsp + 0x1b0 ]
setc r11b
mov [ rsp + 0x290 ], rbp
movzx rbp, byte [ rsp + 0x1b8 ]
clc
mov [ rsp + 0x298 ], rbx
mov rbx, -0x1 
adcx rbp, rbx
adcx r14, [ rsp + 0x130 ]
setc bpl
clc
adcx r14, [ rsp - 0x30 ]
mov rbx, [ rsp + 0xe8 ]
mov [ rsp + 0x2a0 ], rdx
seto dl
mov byte [ rsp + 0x2a8 ], r11b
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox rbx, [ rsp + 0x28 ]
mov r9b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2b0 ], rbx
mulx rbx, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x2b8 ], bpl
mov byte [ rsp + 0x2c0 ], r9b
mulx r9, rbp, [ rax + 0x30 ]
setc dl
mov [ rsp + 0x2c8 ], r9
movzx r9, byte [ rsp + 0x210 ]
clc
mov [ rsp + 0x2d0 ], rbp
mov rbp, -0x1 
adcx r9, rbp
adcx r11, [ rsp - 0x38 ]
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x2d8 ], r11
mulx r11, rbp, [ rax + 0x28 ]
adcx r12, rbx
adcx r10, [ rsp + 0x118 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2e0 ], r10
mulx r10, rbx, [ rsi + 0x20 ]
adcx r15, [ rsp + 0x110 ]
seto dl
mov [ rsp + 0x2e8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rdi, dil
adox rdi, r15
adox r13, [ rsp + 0x208 ]
mov rdi, 0x0 
adcx r8, rdi
adox rcx, [ rsp + 0x200 ]
mov rdi, 0x7bc65c783158aea3 
xchg rdx, rdi
mov [ rsp + 0x2f0 ], r8
mulx r8, r15, r14
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x2f8 ], r12
movzx r12, byte [ rsp + 0x1a8 ]
clc
mov [ rsp + 0x300 ], rcx
mov rcx, -0x1 
adcx r12, rcx
adcx rdx, [ rsp + 0x128 ]
setc r12b
movzx rcx, byte [ rsp + 0x2c0 ]
clc
mov [ rsp + 0x308 ], r13
mov r13, -0x1 
adcx rcx, r13
adcx rbx, [ rsp - 0x40 ]
mov rcx, [ rsp + 0xe0 ]
seto r13b
mov [ rsp + 0x310 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx rdi, dil
adox rdi, rbx
adox rcx, [ rsp + 0x2d0 ]
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x318 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x2c8 ]
mov [ rsp + 0x320 ], r8
mov r8, 0x0 
adox rdx, r8
movzx r8, r13b
mov [ rsp + 0x328 ], rdx
mov rdx, [ rsp + 0x1d8 ]
lea r8, [ r8 + rdx ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x330 ], r8
mulx r8, r13, r14
adcx r10, [ rsp + 0xd8 ]
mov rdx, [ rsp + 0x108 ]
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x338 ], rdx
mov rdx, [ rsp + 0x158 ]
mov [ rsp + 0x340 ], r10
movzx r10, byte [ rsp + 0x2b8 ]
mov [ rsp + 0x348 ], r8
mov r8, 0x0 
dec r8
adox r10, r8
adox rdx, [ rsp + 0x1f8 ]
adox rdi, [ rsp + 0x238 ]
mov r10, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0x350 ], r13
mulx r13, r8, r10
mov r10, [ rsp - 0x48 ]
mov [ rsp + 0x358 ], r15
seto r15b
mov [ rsp + 0x360 ], r11
movzx r11, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x368 ], rdi
mov rdi, 0x0 
dec rdi
adox r11, rdi
adox r10, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
setc r11b
clc
movzx r9, r9b
adcx r9, rdi
adcx r14, [ rsp + 0x190 ]
mov r9, r8
seto dil
mov [ rsp + 0x370 ], rbp
mov rbp, -0x2 
inc rbp
adox r9, r13
mov rbp, r8
adox rbp, r13
mov [ rsp + 0x378 ], r10
seto r10b
mov byte [ rsp + 0x380 ], r11b
mov r11, -0x2 
inc r11
adox r8, rdx
setc r8b
clc
movzx r12, r12b
adcx r12, r11
adcx rbx, [ rsp + 0x120 ]
adcx rcx, [ rsp + 0x50 ]
mov r12, [ rsp + 0x90 ]
adcx r12, [ rsp + 0x48 ]
setc r11b
clc
mov [ rsp + 0x388 ], r12
mov r12, -0x1 
movzx r15, r15b
adcx r15, r12
adcx rbx, [ rsp + 0x230 ]
adcx rcx, [ rsp + 0x258 ]
mov r15, [ rsp + 0x188 ]
seto r12b
mov byte [ rsp + 0x390 ], r10b
mov r10, 0x0 
dec r10
movzx r8, r8b
adox r8, r10
adox r15, [ rsp + 0x368 ]
adox rbx, [ rsp + 0x1d0 ]
movzx r8, r11b
mov r10, [ rsp + 0x88 ]
lea r8, [ r8 + r10 ]
adox rcx, [ rsp + 0x1c8 ]
setc r10b
clc
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx r14, r9
adcx rbp, r15
setc r9b
clc
adcx r14, [ rsp + 0x68 ]
adcx rbp, [ rsp + 0x280 ]
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r12
mulx r11, r15, r14
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x398 ], r11
mov [ rsp + 0x3a0 ], r15
mulx r15, r11, r14
mov rdx, [ rsp + 0x180 ]
mov [ rsp + 0x3a8 ], r15
setc r15b
clc
mov [ rsp + 0x3b0 ], r11
mov r11, -0x1 
movzx rdi, dil
adcx rdi, r11
adcx rdx, [ rsp + 0x360 ]
movzx rdi, byte [ rsp + 0x380 ]
mov r11, [ rsp + 0x100 ]
lea rdi, [ rdi + r11 ]
mov r11, [ rsp + 0x178 ]
mov [ rsp + 0x3b8 ], rdi
mov rdi, 0x0 
adcx r11, rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x3c0 ], r11
mov [ rsp + 0x3c8 ], rdi
mulx rdi, r11, r12
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x3d0 ], r15b
mov [ rsp + 0x3d8 ], rcx
mulx rcx, r15, r14
mov rdx, r15
clc
adcx rdx, r14
seto dl
mov [ rsp + 0x3e0 ], rbp
movzx rbp, byte [ rsp + 0x390 ]
mov [ rsp + 0x3e8 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rbp, rbx
adox r13, r11
mov rbp, r15
setc r11b
clc
adcx rbp, rcx
adox rdi, [ rsp + 0x358 ]
adcx r15, rcx
mov rbx, 0x2341f27177344 
xchg rdx, rbx
mov [ rsp + 0x3f0 ], r15
mov [ rsp + 0x3f8 ], rdi
mulx rdi, r15, r14
mov rdx, [ rsp + 0x320 ]
adox rdx, [ rsp + 0x350 ]
mov [ rsp + 0x400 ], rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x408 ], r15
mov [ rsp + 0x410 ], rdi
mulx rdi, r15, r14
mov r14, [ rsp + 0x388 ]
setc dl
clc
mov [ rsp + 0x418 ], rdi
mov rdi, -0x1 
movzx r10, r10b
adcx r10, rdi
adcx r14, [ rsp + 0x240 ]
adcx r8, [ rsp + 0x2a0 ]
seto r10b
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r13, [ rsp + 0x3e8 ]
setc r9b
clc
movzx r11, r11b
adcx r11, rdi
adcx rbp, [ rsp + 0x3e0 ]
setc r11b
clc
movzx rbx, bl
adcx rbx, rdi
adcx r14, [ rsp + 0x1c0 ]
mov rbx, [ rsp + 0x3d8 ]
adox rbx, [ rsp + 0x3f8 ]
adcx r8, [ rsp + 0x228 ]
mov rdi, 0x2341f27177344 
xchg rdx, r12
mov byte [ rsp + 0x420 ], r11b
mov [ rsp + 0x428 ], rbx
mulx rbx, r11, rdi
adox r14, [ rsp + 0x410 ]
movzx r9, r9b
movzx rdx, r9b
adcx rdx, [ rsp + 0x270 ]
seto r9b
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r12, r12b
adox r12, rdi
adox rcx, r15
setc r12b
clc
movzx r10, r10b
adcx r10, rdi
adcx r11, [ rsp + 0x348 ]
mov r10, [ rsp + 0x3b0 ]
adox r10, [ rsp + 0x418 ]
mov r15, [ rsp + 0x3a0 ]
adox r15, [ rsp + 0x3a8 ]
mov rdi, [ rsp + 0x398 ]
adox rdi, [ rsp + 0x408 ]
mov [ rsp + 0x430 ], rdi
setc dil
clc
mov byte [ rsp + 0x438 ], r12b
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx r8, r11
setc r9b
clc
adcx rbp, [ rsp + 0xb0 ]
setc r11b
movzx r12, byte [ rsp + 0x3d0 ]
clc
mov [ rsp + 0x440 ], rdx
mov rdx, -0x1 
adcx r12, rdx
adcx r13, [ rsp + 0x278 ]
mov r12, 0x6cfc5fd681c52056 
mov rdx, rbp
mov byte [ rsp + 0x448 ], r9b
mulx r9, rbp, r12
mov r12, [ rsp + 0x400 ]
mov [ rsp + 0x450 ], r9
mov r9, 0x0 
adox r12, r9
mov r9, [ rsp + 0x298 ]
adcx r9, [ rsp + 0x428 ]
mov [ rsp + 0x458 ], rbp
mov rbp, 0x7bc65c783158aea3 
mov [ rsp + 0x460 ], r12
mov [ rsp + 0x468 ], rbx
mulx rbx, r12, rbp
adcx r14, [ rsp + 0x378 ]
mov rbp, 0x2341f27177344 
mov [ rsp + 0x470 ], rbx
mov [ rsp + 0x478 ], r12
mulx r12, rbx, rbp
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x480 ], r12
mov [ rsp + 0x488 ], rbx
mulx rbx, r12, rbp
movzx rbp, byte [ rsp + 0x420 ]
mov [ rsp + 0x490 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rbp, rbx
adox r13, [ rsp + 0x3f0 ]
adcx r8, [ rsp + 0x370 ]
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x498 ], r12
mulx r12, rbx, rbp
mov rbp, rbx
mov byte [ rsp + 0x4a0 ], dil
setc dil
clc
adcx rbp, rdx
adox rcx, r9
setc bpl
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r13, [ rsp + 0x1f0 ]
adcx rcx, [ rsp + 0x1e8 ]
adox r10, r14
adcx r10, [ rsp + 0x220 ]
mov r11, rbx
seto r9b
inc rdx
adox r11, r12
adox rbx, r12
seto r14b
dec rdx
movzx r9, r9b
adox r9, rdx
adox r8, r15
seto r15b
inc rdx
mov r9, -0x1 
movzx rbp, bpl
adox rbp, r9
adox r13, r11
setc bpl
clc
adcx r13, [ rsp + 0xa0 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r9, r11, r13
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4a8 ], r10
mov [ rsp + 0x4b0 ], rbx
mulx rbx, r10, r13
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4b8 ], rcx
mov [ rsp + 0x4c0 ], rbx
mulx rbx, rcx, r13
mov rdx, 0x2341f27177344 
mov [ rsp + 0x4c8 ], rbx
mov [ rsp + 0x4d0 ], rcx
mulx rcx, rbx, r13
movzx rdx, byte [ rsp + 0x4a0 ]
mov [ rsp + 0x4d8 ], rcx
mov rcx, [ rsp + 0x468 ]
lea rdx, [ rdx + rcx ]
mov rcx, r11
mov [ rsp + 0x4e0 ], rbx
seto bl
mov [ rsp + 0x4e8 ], r10
mov r10, -0x2 
inc r10
adox rcx, r13
seto cl
movzx r10, byte [ rsp + 0x448 ]
mov byte [ rsp + 0x4f0 ], bl
mov rbx, 0x0 
dec rbx
adox r10, rbx
adox rdx, [ rsp + 0x440 ]
seto r10b
inc rbx
mov rbx, -0x1 
movzx rdi, dil
adox rdi, rbx
adox rdx, [ rsp + 0x3c8 ]
movzx rdi, r10b
movzx rbx, byte [ rsp + 0x438 ]
lea rdi, [ rdi + rbx ]
mov rbx, r11
setc r10b
clc
adcx rbx, r9
mov [ rsp + 0x4f8 ], rbx
mov rbx, 0x7bc65c783158aea3 
xchg rdx, r13
mov byte [ rsp + 0x500 ], cl
mov byte [ rsp + 0x508 ], r10b
mulx r10, rcx, rbx
adcx r11, r9
setc dl
clc
mov rbx, -0x1 
movzx rbp, bpl
adcx rbp, rbx
adcx r8, [ rsp + 0x218 ]
setc bpl
clc
movzx r14, r14b
adcx r14, rbx
adcx r12, [ rsp + 0x498 ]
adox rdi, [ rsp + 0x3c0 ]
setc r14b
clc
movzx r15, r15b
adcx r15, rbx
adcx r13, [ rsp + 0x430 ]
seto r15b
inc rbx
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox r9, [ rsp + 0x4e8 ]
adox rcx, [ rsp + 0x4c0 ]
adcx rdi, [ rsp + 0x460 ]
adox r10, [ rsp + 0x4d0 ]
mov rdx, [ rsp + 0x4b8 ]
setc bl
mov [ rsp + 0x510 ], r10
movzx r10, byte [ rsp + 0x4f0 ]
clc
mov [ rsp + 0x518 ], rcx
mov rcx, -0x1 
adcx r10, rcx
adcx rdx, [ rsp + 0x4b0 ]
adcx r12, [ rsp + 0x4a8 ]
mov r10, [ rsp + 0x478 ]
setc cl
clc
mov [ rsp + 0x520 ], r9
mov r9, -0x1 
movzx r14, r14b
adcx r14, r9
adcx r10, [ rsp + 0x490 ]
mov r14, [ rsp + 0x470 ]
adcx r14, [ rsp + 0x458 ]
seto r9b
mov [ rsp + 0x528 ], r11
movzx r11, byte [ rsp + 0x508 ]
mov [ rsp + 0x530 ], r14
mov r14, 0x0 
dec r14
adox r11, r14
adox rdx, [ rsp + 0x98 ]
setc r11b
movzx r14, byte [ rsp + 0x500 ]
clc
mov [ rsp + 0x538 ], rdi
mov rdi, -0x1 
adcx r14, rdi
adcx rdx, [ rsp + 0x4f8 ]
setc r14b
clc
movzx rcx, cl
adcx rcx, rdi
adcx r8, r10
setc cl
clc
adcx rdx, [ rsp + 0x1e0 ]
setc r10b
clc
movzx rbp, bpl
adcx rbp, rdi
adcx r13, [ rsp + 0x308 ]
mov rbp, [ rsp + 0x4c8 ]
setc dil
clc
mov byte [ rsp + 0x540 ], r10b
mov r10, -0x1 
movzx r9, r9b
adcx r9, r10
adcx rbp, [ rsp + 0x4e0 ]
mov r9, 0x7bc65c783158aea3 
mov [ rsp + 0x548 ], rbp
mulx rbp, r10, r9
adox r12, [ rsp + 0x288 ]
mov r9, 0x6cfc5fd681c52056 
mov [ rsp + 0x550 ], rbp
mov [ rsp + 0x558 ], r10
mulx r10, rbp, r9
mov r9, [ rsp + 0x4d8 ]
mov [ rsp + 0x560 ], r10
mov r10, 0x0 
adcx r9, r10
mov r10, [ rsp + 0x450 ]
clc
mov [ rsp + 0x568 ], rbp
mov rbp, -0x1 
movzx r11, r11b
adcx r11, rbp
adcx r10, [ rsp + 0x488 ]
adox r8, [ rsp + 0x290 ]
movzx r11, bl
movzx r15, r15b
lea r11, [ r11 + r15 ]
mov r15, 0xffffffffffffffff 
mulx rbp, rbx, r15
mov r15, [ rsp + 0x480 ]
mov [ rsp + 0x570 ], r9
mov r9, 0x0 
adcx r15, r9
mov r9, [ rsp + 0x300 ]
clc
mov [ rsp + 0x578 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx r9, [ rsp + 0x538 ]
adcx r11, [ rsp + 0x330 ]
setc dil
clc
movzx rcx, cl
adcx rcx, r8
adcx r13, [ rsp + 0x530 ]
adcx r10, r9
adcx r15, r11
mov rcx, rbx
setc r9b
clc
adcx rcx, rdx
movzx rcx, r9b
movzx rdi, dil
lea rcx, [ rcx + rdi ]
mov rdi, rbx
setc r11b
clc
adcx rdi, rbp
seto r9b
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox r12, [ rsp + 0x528 ]
mov r14, 0xfdc1767ae2ffffff 
mov [ rsp + 0x580 ], rdi
mulx rdi, r8, r14
adcx rbx, rbp
mov r14, [ rsp + 0x578 ]
adox r14, [ rsp + 0x520 ]
mov [ rsp + 0x588 ], rdi
setc dil
clc
mov [ rsp + 0x590 ], rbx
mov rbx, -0x1 
movzx r9, r9b
adcx r9, rbx
adcx r13, [ rsp + 0x310 ]
adox r13, [ rsp + 0x518 ]
seto r9b
movzx rbx, byte [ rsp + 0x540 ]
mov byte [ rsp + 0x598 ], r11b
mov r11, 0x0 
dec r11
adox rbx, r11
adox r12, [ rsp + 0x248 ]
adcx r10, [ rsp + 0x340 ]
adox r14, [ rsp + 0x250 ]
adcx r15, [ rsp + 0x338 ]
adox r13, [ rsp + 0x260 ]
adcx rcx, [ rsp + 0x3b8 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r11
adcx rbp, r8
seto r8b
movzx rdi, byte [ rsp + 0x598 ]
inc r11
mov r11, -0x1 
adox rdi, r11
adox r12, [ rsp + 0x580 ]
seto dil
inc r11
adox r12, [ rsp + 0x160 ]
seto r11b
mov byte [ rsp + 0x5a0 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r9, r9b
adox r9, rbx
adox r10, [ rsp + 0x510 ]
adox r15, [ rsp + 0x548 ]
seto r9b
inc rbx
mov rbx, -0x1 
movzx r8, r8b
adox r8, rbx
adox r10, [ rsp + 0x268 ]
seto r8b
inc rbx
mov rbx, -0x1 
movzx rdi, dil
adox rdi, rbx
adox r14, [ rsp + 0x590 ]
setc dil
clc
movzx r9, r9b
adcx r9, rbx
adcx rcx, [ rsp + 0x570 ]
mov r9, 0x7bc65c783158aea3 
xchg rdx, r12
mov [ rsp + 0x5a8 ], r10
mulx r10, rbx, r9
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x5b0 ], rcx
mov [ rsp + 0x5b8 ], r15
mulx r15, rcx, r9
adox rbp, r13
movzx r13, byte [ rsp + 0x5a0 ]
mov r9, 0x0 
adcx r13, r9
mov r9, 0x2341f27177344 
mov [ rsp + 0x5c0 ], r13
mov byte [ rsp + 0x5c8 ], r8b
mulx r8, r13, r9
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x5d0 ], r8
mov [ rsp + 0x5d8 ], r13
mulx r13, r8, r9
clc
mov r9, -0x1 
movzx r11, r11b
adcx r11, r9
adcx r14, [ rsp + 0x168 ]
adcx rbp, [ rsp + 0x1a0 ]
mov r11, r8
seto r9b
mov [ rsp + 0x5e0 ], rbp
mov rbp, -0x2 
inc rbp
adox r11, r13
mov rbp, r8
adox rbp, r13
adox rcx, r13
mov r13, [ rsp + 0x588 ]
mov [ rsp + 0x5e8 ], rcx
setc cl
clc
mov [ rsp + 0x5f0 ], rbp
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx r13, [ rsp + 0x558 ]
mov rdi, [ rsp + 0x550 ]
adcx rdi, [ rsp + 0x568 ]
mov rbp, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x5f8 ], cl
mov [ rsp + 0x600 ], r11
mulx r11, rcx, rbp
adox rbx, r15
adox rcx, r10
mov r10, 0x2341f27177344 
xchg rdx, r10
mulx rbp, r15, r12
adcx r15, [ rsp + 0x560 ]
adox r11, [ rsp + 0x5d8 ]
mov r12, [ rsp + 0x5b8 ]
setc dl
mov [ rsp + 0x608 ], r11
movzx r11, byte [ rsp + 0x5c8 ]
clc
mov [ rsp + 0x610 ], rcx
mov rcx, -0x1 
adcx r11, rcx
adcx r12, [ rsp + 0x2b0 ]
mov r11, [ rsp + 0x318 ]
adcx r11, [ rsp + 0x5b0 ]
seto cl
mov [ rsp + 0x618 ], rbx
mov rbx, 0x0 
dec rbx
movzx r9, r9b
adox r9, rbx
adox r13, [ rsp + 0x5a8 ]
mov r9, [ rsp + 0x5c0 ]
adcx r9, [ rsp + 0x328 ]
adox rdi, r12
adox r15, r11
movzx r12, cl
mov r11, [ rsp + 0x5d0 ]
lea r12, [ r12 + r11 ]
setc r11b
clc
adcx r8, r10
movzx r8, dl
lea r8, [ r8 + rbp ]
adcx r14, [ rsp + 0x600 ]
seto r10b
movzx rbp, byte [ rsp + 0x5f8 ]
inc rbx
mov rdx, -0x1 
adox rbp, rdx
adox r13, [ rsp + 0x2d8 ]
adox rdi, [ rsp + 0x2f8 ]
mov rbp, [ rsp + 0x5e0 ]
adcx rbp, [ rsp + 0x5f0 ]
adox r15, [ rsp + 0x2e0 ]
adcx r13, [ rsp + 0x5e8 ]
seto cl
inc rdx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox r9, r8
movzx r10, r11b
adox r10, rdx
setc r11b
mov r8, r14
mov rbx, 0xffffffffffffffff 
sub r8, rbx
mov rdx, rbp
sbb rdx, rbx
mov [ rsp + 0x620 ], r8
mov r8, r13
sbb r8, rbx
mov rbx, 0x0 
dec rbx
movzx rcx, cl
adox rcx, rbx
adox r9, [ rsp + 0x2e8 ]
adox r10, [ rsp + 0x2f0 ]
seto cl
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox rdi, [ rsp + 0x618 ]
seto r11b
mov rbx, rdi
mov [ rsp + 0x628 ], r8
mov r8, 0xfdc1767ae2ffffff 
sbb rbx, r8
mov r8, 0x0 
dec r8
movzx r11, r11b
adox r11, r8
adox r15, [ rsp + 0x610 ]
seto r11b
mov r8, r15
mov [ rsp + 0x630 ], rbx
mov rbx, 0x7bc65c783158aea3 
sbb r8, rbx
mov rbx, 0x0 
dec rbx
movzx r11, r11b
adox r11, rbx
adox r9, [ rsp + 0x608 ]
seto r11b
mov rbx, r9
mov [ rsp + 0x638 ], rdx
mov rdx, 0x6cfc5fd681c52056 
sbb rbx, rdx
mov rdx, 0x0 
dec rdx
movzx r11, r11b
adox r11, rdx
adox r10, r12
movzx r12, cl
mov r11, 0x0 
adox r12, r11
mov rcx, r10
mov r11, 0x2341f27177344 
sbb rcx, r11
sbb r12, 0x00000000
cmovc rbx, r9
cmovc r8, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x28 ], rbx
mov r15, [ rsp + 0x638 ]
cmovc r15, rbp
mov [ r12 + 0x8 ], r15
mov rbp, [ rsp + 0x628 ]
cmovc rbp, r13
cmovc rcx, r10
mov r13, [ rsp + 0x630 ]
cmovc r13, rdi
mov [ r12 + 0x18 ], r13
mov [ r12 + 0x20 ], r8
mov [ r12 + 0x30 ], rcx
mov rdi, [ rsp + 0x620 ]
cmovc rdi, r14
mov [ r12 + 0x10 ], rbp
mov [ r12 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1728
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.5519
; seed 1150715237846205 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 63415 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=38, initial num_batches=31): 1049 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01654182764330206
; number reverted permutation / tried permutation: 325 / 507 =64.103%
; number reverted decision / tried decision: 305 / 492 =61.992%
; validated in 244.873s
