SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1720
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rdi
mulx rdi, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], rbp
mulx rbp, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r8
mulx r8, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rbp
mulx rbp, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], rbp
mulx rbp, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r15
mulx r15, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], r8
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r15
mulx r15, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r15
mulx r15, r11, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r11
mulx r11, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r15
mulx r15, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r8
mulx r8, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0xd8 ], rdi
mov [ rsp + 0xe0 ], r14
mulx r14, rdi, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe8 ], r14
mov [ rsp + 0xf0 ], rdi
mulx rdi, r14, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], rdi
mov [ rsp + 0x100 ], r14
mulx r14, rdi, [ rax + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x108 ], r14
mov [ rsp + 0x110 ], rdi
mulx rdi, r14, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x118 ], rdi
mov [ rsp + 0x120 ], r14
mulx r14, rdi, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x128 ], r13
mov [ rsp + 0x130 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x138 ], r12
mov [ rsp + 0x140 ], r10
mulx r10, r12, r9
test al, al
adox rdi, rbp
adcx r13, rbx
adox r15, r14
mov rdx, [ rax + 0x8 ]
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x148 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x150 ], rdi
mov [ rsp + 0x158 ], r14
mulx r14, rdi, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], rdi
mulx rdi, r14, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x170 ], r10
mov [ rsp + 0x178 ], r12
mulx r12, r10, [ rsi + 0x20 ]
adox r14, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x180 ], r14
mulx r14, r8, [ rax + 0x28 ]
setc dl
clc
adcx r11, r15
setc r15b
clc
adcx rcx, [ rsp + 0x140 ]
mov [ rsp + 0x188 ], r11
mov r11b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x190 ], rcx
mov [ rsp + 0x198 ], r13
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1a0 ], rbx
mov [ rsp + 0x1a8 ], rbp
mulx rbp, rbx, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1b0 ], r14
mov [ rsp + 0x1b8 ], r8
mulx r8, r14, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x1c0 ], r13
mov r13, -0x2 
inc r13
adox r14, [ rsp + 0x130 ]
mov r13b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], r8
mulx r8, r14, [ rsi + 0x20 ]
mov rdx, rbx
mov [ rsp + 0x1d8 ], r8
setc r8b
clc
adcx rdx, r9
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x1e0 ], r8b
mov [ rsp + 0x1e8 ], rbp
mulx rbp, r8, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x1f0 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox r8, [ rsp + 0x138 ]
adox rbp, [ rsp + 0x128 ]
adox rcx, [ rsp + 0xe0 ]
mov r11b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1f8 ], rcx
mulx rcx, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x200 ], r14
mov [ rsp + 0x208 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x210 ], rbp
mov [ rsp + 0x218 ], r8
mulx r8, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x220 ], r14
mov byte [ rsp + 0x228 ], r11b
mulx r11, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x230 ], r14
mov [ rsp + 0x238 ], r11
mulx r11, r14, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x240 ], r11
mov r11, 0x0 
dec r11
movzx r13, r13b
adox r13, r11
adox rdi, [ rsp + 0xd8 ]
setc r13b
clc
adcx rcx, [ rsp + 0xc0 ]
adox rbp, [ rsp + 0xb0 ]
adcx r14, [ rsp + 0xa8 ]
adox r8, [ rsp + 0xa0 ]
setc r11b
clc
mov [ rsp + 0x248 ], r8
mov r8, -0x1 
movzx r15, r15b
adcx r15, r8
adcx r10, [ rsp + 0x98 ]
mov r15b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x250 ], rbp
mulx rbp, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x258 ], rdi
mov [ rsp + 0x260 ], r10
mulx r10, rdi, [ rax + 0x18 ]
adcx r12, [ rsp + 0x1f0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x268 ], r12
mov [ rsp + 0x270 ], r14
mulx r14, r12, [ rax + 0x28 ]
mov rdx, rbx
mov [ rsp + 0x278 ], rcx
setc cl
clc
adcx rdx, [ rsp + 0x1e8 ]
mov [ rsp + 0x280 ], rbp
setc bpl
clc
mov byte [ rsp + 0x288 ], cl
mov rcx, -0x1 
movzx r11, r11b
adcx r11, rcx
adcx rdi, [ rsp + 0x240 ]
mov r11, [ rsp + 0x70 ]
mov rcx, 0x0 
adox r11, rcx
mov rcx, [ rsp + 0x68 ]
mov [ rsp + 0x290 ], r11
movzx r11, byte [ rsp + 0x1e0 ]
mov [ rsp + 0x298 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r11, rdi
adox rcx, [ rsp + 0x40 ]
adcx r10, [ rsp + 0x90 ]
mov r11, [ rsp + 0x38 ]
seto dil
mov [ rsp + 0x2a0 ], r10
movzx r10, byte [ rsp + 0x228 ]
mov [ rsp + 0x2a8 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox r10, rcx
adox r11, [ rsp + 0x1d0 ]
setc r10b
clc
movzx rbp, bpl
adcx rbp, rcx
adcx rbx, [ rsp + 0x1e8 ]
setc bpl
clc
movzx r15, r15b
adcx r15, rcx
adcx r12, [ rsp + 0x1c0 ]
mov r15, [ rsp + 0x30 ]
adox r15, [ rsp + 0x28 ]
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2b0 ], r15
mov [ rsp + 0x2b8 ], r11
mulx r11, r15, [ rsi + 0x30 ]
adox r15, [ rsp + 0x20 ]
mov rdx, [ rsp + 0x1b8 ]
mov [ rsp + 0x2c0 ], r15
setc r15b
clc
mov [ rsp + 0x2c8 ], r12
mov r12, -0x1 
movzx r10, r10b
adcx r10, r12
adcx rdx, [ rsp + 0x88 ]
mov r10, [ rsp + 0x1b0 ]
adcx r10, [ rsp + 0x100 ]
adox r11, [ rsp + 0x10 ]
mov r12, [ rsp + 0x1a8 ]
mov [ rsp + 0x2d0 ], r11
setc r11b
clc
adcx r12, [ rsp + 0x238 ]
mov byte [ rsp + 0x2d8 ], r11b
seto r11b
mov [ rsp + 0x2e0 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r15, r15b
adox r15, r10
adox r14, [ rsp - 0x10 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r9
mov [ rsp + 0x2e8 ], r9
mulx r9, r10, r15
mov rdx, [ rsp - 0x20 ]
mov r15, 0x0 
adox rdx, r15
adcx r8, [ rsp + 0x1a0 ]
dec r15
movzx r13, r13b
adox r13, r15
adox rcx, [ rsp + 0x198 ]
mov r13, [ rsp + 0x1e8 ]
setc r15b
clc
mov [ rsp + 0x2f0 ], r8
mov r8, -0x1 
movzx rbp, bpl
adcx rbp, r8
adcx r13, [ rsp + 0x120 ]
mov rbp, [ rsp - 0x18 ]
setc r8b
clc
mov [ rsp + 0x2f8 ], r12
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx rbp, [ rsp + 0x220 ]
adox rbx, [ rsp + 0x218 ]
mov rdi, [ rsp + 0x118 ]
setc r12b
clc
mov [ rsp + 0x300 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx rdi, [ rsp + 0x178 ]
adcx r10, [ rsp + 0x170 ]
adox r13, [ rsp + 0x208 ]
mov r8, [ rsp + 0x210 ]
seto bpl
mov [ rsp + 0x308 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r12, r12b
adox r12, r13
adox r8, [ rsp + 0xd0 ]
setc r12b
clc
movzx rbp, bpl
adcx rbp, r13
adcx rdi, [ rsp + 0x1f8 ]
setc bpl
clc
movzx r12, r12b
adcx r12, r13
adcx r9, [ rsp + 0xf0 ]
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x310 ], r8
mulx r8, r13, [ rax + 0x28 ]
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x318 ], rdi
setc dil
clc
mov [ rsp + 0x320 ], rbx
mov rbx, -0x1 
movzx r11, r11b
adcx r11, rbx
adcx rdx, [ rsp + 0x168 ]
mov r11, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x328 ], rcx
mulx rcx, rbx, [ rsi + 0x8 ]
adox r13, [ rsp + 0xc8 ]
seto dl
mov [ rsp + 0x330 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rbp, bpl
adox rbp, r11
adox r10, [ rsp + 0x2c8 ]
setc bpl
clc
movzx rdx, dl
adcx rdx, r11
adcx r8, rbx
movzx rbx, bpl
mov rdx, [ rsp + 0x160 ]
lea rbx, [ rbx + rdx ]
mov rdx, [ rsp - 0x28 ]
setc bpl
movzx r11, byte [ rsp + 0x288 ]
clc
mov [ rsp + 0x338 ], rbx
mov rbx, -0x1 
adcx r11, rbx
adcx rdx, [ rsp + 0x1d8 ]
movzx r11, dil
mov rbx, [ rsp + 0xe8 ]
lea r11, [ r11 + rbx ]
mov rbx, [ rsp + 0x0 ]
adcx rbx, [ rsp - 0x40 ]
movzx rdi, bpl
lea rdi, [ rdi + rcx ]
adox r9, r14
mov r14, [ rsp + 0x110 ]
adcx r14, [ rsp - 0x8 ]
mov rcx, [ rsp + 0x280 ]
setc bpl
clc
mov [ rsp + 0x340 ], r14
mov r14, -0x1 
movzx r15, r15b
adcx r15, r14
adcx rcx, [ rsp + 0x60 ]
adox r11, r12
mov r12, [ rsp + 0x58 ]
adcx r12, [ rsp - 0x30 ]
mov r15, [ rsp - 0x38 ]
adcx r15, [ rsp + 0x50 ]
mov r14, [ rsp + 0x48 ]
adcx r14, [ rsp + 0x80 ]
mov [ rsp + 0x348 ], rbx
mov rbx, [ rsp + 0x18 ]
mov [ rsp + 0x350 ], rdx
setc dl
clc
adcx rbx, [ rsp + 0x328 ]
mov [ rsp + 0x358 ], r14
movzx r14, dl
mov [ rsp + 0x360 ], r15
mov r15, [ rsp + 0x78 ]
lea r14, [ r14 + r15 ]
mov r15, 0xfdc1767ae2ffffff 
mov rdx, rbx
mov [ rsp + 0x368 ], r14
mulx r14, rbx, r15
movzx r15, bpl
mov [ rsp + 0x370 ], r12
mov r12, [ rsp + 0x108 ]
lea r15, [ r15 + r12 ]
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x378 ], r15
mulx r15, rbp, r12
mov r12, [ rsp + 0x320 ]
adcx r12, [ rsp + 0x190 ]
mov [ rsp + 0x380 ], rcx
mov rcx, rbp
mov [ rsp + 0x388 ], rdi
setc dil
clc
adcx rcx, rdx
mov rcx, [ rsp + 0x308 ]
mov [ rsp + 0x390 ], r8
setc r8b
clc
mov [ rsp + 0x398 ], r11
mov r11, -0x1 
movzx rdi, dil
adcx rdi, r11
adcx rcx, [ rsp + 0x2a8 ]
mov rdi, [ rsp + 0x318 ]
adcx rdi, [ rsp + 0x300 ]
mov r11, 0x6cfc5fd681c52056 
mov [ rsp + 0x3a0 ], rdi
mov [ rsp + 0x3a8 ], r14
mulx r14, rdi, r11
adcx r10, [ rsp + 0x310 ]
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x3b0 ], r14
mov [ rsp + 0x3b8 ], rdi
mulx rdi, r14, r11
adcx r13, r9
mov r9, rbp
seto r11b
mov [ rsp + 0x3c0 ], r13
mov r13, -0x2 
inc r13
adox r9, r15
setc r13b
clc
mov byte [ rsp + 0x3c8 ], r11b
mov r11, -0x1 
movzx r8, r8b
adcx r8, r11
adcx r12, r9
adox rbp, r15
adox rbx, r15
adcx rbp, rcx
setc r15b
clc
adcx r12, [ rsp + 0x200 ]
adox r14, [ rsp + 0x3a8 ]
seto r8b
inc r11
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox rbx, [ rsp + 0x3a0 ]
adox r14, r10
setc r10b
clc
movzx r8, r8b
adcx r8, rcx
adcx rdi, [ rsp + 0x3b8 ]
mov r9, 0x2341f27177344 
mulx r8, r15, r9
adcx r15, [ rsp + 0x3b0 ]
mov rdx, r9
mulx r11, r9, r12
mov rcx, 0x7bc65c783158aea3 
mov rdx, r12
mov [ rsp + 0x3d0 ], r14
mulx r14, r12, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x3d8 ], r15
mov [ rsp + 0x3e0 ], r11
mulx r11, r15, rcx
adox rdi, [ rsp + 0x3c0 ]
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0x3e8 ], rdi
mov [ rsp + 0x3f0 ], r9
mulx r9, rdi, rcx
mov rcx, r15
mov [ rsp + 0x3f8 ], r9
setc r9b
clc
adcx rcx, rdx
mov rcx, r15
mov [ rsp + 0x400 ], r8
setc r8b
clc
adcx rcx, r11
mov byte [ rsp + 0x408 ], r9b
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x410 ], rcx
mov byte [ rsp + 0x418 ], r8b
mulx r8, rcx, r9
mov rdx, [ rsp + 0x398 ]
setc r9b
clc
mov [ rsp + 0x420 ], rbx
mov rbx, -0x1 
movzx r13, r13b
adcx r13, rbx
adcx rdx, [ rsp + 0x390 ]
mov r13, [ rsp + 0x388 ]
movzx rbx, byte [ rsp + 0x3c8 ]
adcx rbx, r13
mov r13, r11
mov [ rsp + 0x428 ], rbx
setc bl
clc
mov [ rsp + 0x430 ], rdx
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx r13, r15
adcx rcx, r11
adcx r12, r8
adcx rdi, r14
seto r14b
inc rdx
mov r15, -0x1 
movzx r10, r10b
adox r10, r15
adox rbp, [ rsp + 0x278 ]
mov r10, [ rsp + 0x420 ]
adox r10, [ rsp + 0x270 ]
setc r11b
movzx r9, byte [ rsp + 0x418 ]
clc
adcx r9, r15
adcx rbp, [ rsp + 0x410 ]
setc r9b
clc
adcx rbp, [ rsp + 0x230 ]
setc r8b
clc
movzx r9, r9b
adcx r9, r15
adcx r10, r13
movzx r13, byte [ rsp + 0x408 ]
mov r9, [ rsp + 0x400 ]
lea r13, [ r13 + r9 ]
mov r9, 0x7bc65c783158aea3 
mov rdx, rbp
mulx r15, rbp, r9
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x438 ], r15
mov [ rsp + 0x440 ], rbp
mulx rbp, r15, r9
mov r9, 0x6cfc5fd681c52056 
mov [ rsp + 0x448 ], rbp
mov [ rsp + 0x450 ], rdi
mulx rdi, rbp, r9
mov r9, 0x2341f27177344 
mov [ rsp + 0x458 ], rdi
mov [ rsp + 0x460 ], rbp
mulx rbp, rdi, r9
mov r9, [ rsp + 0x3f8 ]
mov [ rsp + 0x468 ], rbp
setc bpl
clc
mov [ rsp + 0x470 ], rdi
mov rdi, -0x1 
movzx r11, r11b
adcx r11, rdi
adcx r9, [ rsp + 0x3f0 ]
mov r11, [ rsp + 0x3e0 ]
mov rdi, 0x0 
adcx r11, rdi
mov rdi, [ rsp + 0x430 ]
clc
mov [ rsp + 0x478 ], r11
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx rdi, [ rsp + 0x3d8 ]
adcx r13, [ rsp + 0x428 ]
movzx r14, bl
mov r11, 0x0 
adcx r14, r11
clc
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx r10, [ rsp + 0x2f8 ]
mov r8, 0xffffffffffffffff 
mulx rbx, r11, r8
mov r8, [ rsp + 0x3d0 ]
adox r8, [ rsp + 0x298 ]
mov [ rsp + 0x480 ], r9
mov r9, [ rsp + 0x3e8 ]
adox r9, [ rsp + 0x2a0 ]
mov [ rsp + 0x488 ], r14
mov r14, r11
mov [ rsp + 0x490 ], r10
seto r10b
mov [ rsp + 0x498 ], r13
mov r13, -0x2 
inc r13
adox r14, rdx
setc r14b
clc
movzx rbp, bpl
adcx rbp, r13
adcx r8, rcx
mov rcx, r11
seto dl
inc r13
adox rcx, rbx
adox r11, rbx
adcx r12, r9
seto bpl
dec r13
movzx r14, r14b
adox r14, r13
adox r8, [ rsp + 0x2f0 ]
seto r14b
inc r13
mov r9, -0x1 
movzx rbp, bpl
adox rbp, r9
adox rbx, r15
seto r15b
dec r13
movzx r10, r10b
adox r10, r13
adox rdi, [ rsp + 0x2e8 ]
adcx rdi, [ rsp + 0x450 ]
seto r9b
inc r13
mov r10, -0x1 
movzx r14, r14b
adox r14, r10
adox r12, [ rsp + 0x380 ]
mov rbp, [ rsp + 0x498 ]
setc r14b
clc
movzx r9, r9b
adcx r9, r10
adcx rbp, [ rsp + 0x2e0 ]
adox rdi, [ rsp + 0x370 ]
seto r9b
inc r10
mov r13, -0x1 
movzx rdx, dl
adox rdx, r13
adox rcx, [ rsp + 0x490 ]
setc dl
clc
adcx rcx, [ rsp + 0x158 ]
adox r11, r8
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mulx r13, r10, rcx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4a0 ], rdi
mov byte [ rsp + 0x4a8 ], r15b
mulx r15, rdi, rcx
movzx rdx, byte [ rsp + 0x2d8 ]
mov [ rsp + 0x4b0 ], r13
mov r13, [ rsp + 0xf8 ]
lea rdx, [ rdx + r13 ]
adcx r11, [ rsp + 0x188 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x4b8 ], r11
mov [ rsp + 0x4c0 ], r10
mulx r10, r11, rcx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x4c8 ], r15
mov [ rsp + 0x4d0 ], rdi
mulx rdi, r15, rcx
mov rdx, r11
mov [ rsp + 0x4d8 ], rdi
seto dil
mov [ rsp + 0x4e0 ], r15
mov r15, -0x2 
inc r15
adox rdx, r10
setc r15b
clc
mov [ rsp + 0x4e8 ], rdx
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx r13, [ rsp + 0x488 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, rdx
adcx r12, rbx
setc bl
clc
movzx r14, r14b
adcx r14, rdx
adcx rbp, [ rsp + 0x480 ]
mov r14, 0x7bc65c783158aea3 
mov rdx, rcx
mulx rdi, rcx, r14
seto r14b
mov byte [ rsp + 0x4f0 ], bl
mov rbx, 0x0 
dec rbx
movzx r9, r9b
adox r9, rbx
adox rbp, [ rsp + 0x360 ]
mov r9, r11
seto bl
mov [ rsp + 0x4f8 ], rbp
mov rbp, -0x2 
inc rbp
adox r9, rdx
mov r9, r10
seto dl
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox r9, r11
adox r10, [ rsp + 0x4d0 ]
adox rcx, [ rsp + 0x4c8 ]
adcx r13, [ rsp + 0x478 ]
movzx r11, r8b
mov r14, 0x0 
adcx r11, r14
adox rdi, [ rsp + 0x4c0 ]
clc
movzx rbx, bl
adcx rbx, rbp
adcx r13, [ rsp + 0x358 ]
mov r8, [ rsp + 0x4e0 ]
adox r8, [ rsp + 0x4b0 ]
mov rbx, [ rsp + 0x4d8 ]
adox rbx, r14
mov r14, [ rsp + 0x448 ]
movzx rbp, byte [ rsp + 0x4a8 ]
mov [ rsp + 0x500 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rbp, rbx
adox r14, [ rsp + 0x440 ]
setc bpl
clc
movzx r15, r15b
adcx r15, rbx
adcx r12, [ rsp + 0x260 ]
mov r15, [ rsp + 0x4b8 ]
seto bl
mov [ rsp + 0x508 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rdx, dl
adox rdx, r8
adox r15, [ rsp + 0x4e8 ]
adox r9, r12
mov rdx, [ rsp + 0x460 ]
seto r12b
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox rdx, [ rsp + 0x438 ]
setc bl
movzx r8, byte [ rsp + 0x4f0 ]
clc
mov [ rsp + 0x510 ], rdi
mov rdi, -0x1 
adcx r8, rdi
adcx r14, [ rsp + 0x4a0 ]
mov r8, [ rsp + 0x458 ]
adox r8, [ rsp + 0x470 ]
setc dil
clc
adcx r15, [ rsp + 0xb8 ]
mov [ rsp + 0x518 ], r8
seto r8b
mov [ rsp + 0x520 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbp, bpl
adox rbp, r13
adox r11, [ rsp + 0x368 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov [ rsp + 0x528 ], r11
mulx r11, r13, r15
adcx r9, [ rsp + 0x150 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x530 ], r11
mov [ rsp + 0x538 ], r13
mulx r13, r11, r15
mov rdx, r11
mov [ rsp + 0x540 ], rcx
setc cl
clc
adcx rdx, r13
mov [ rsp + 0x548 ], rbp
mov rbp, r11
mov byte [ rsp + 0x550 ], dil
seto dil
mov byte [ rsp + 0x558 ], cl
mov rcx, -0x2 
inc rcx
adox rbp, r15
mov rbp, 0x2341f27177344 
xchg rdx, rbp
mov byte [ rsp + 0x560 ], dil
mulx rdi, rcx, r15
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x568 ], rdi
mov [ rsp + 0x570 ], rcx
mulx rcx, rdi, r15
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x578 ], rcx
mov [ rsp + 0x580 ], rdi
mulx rdi, rcx, r15
movzx r15, r8b
mov rdx, [ rsp + 0x468 ]
lea r15, [ r15 + rdx ]
adox rbp, r9
adcx r11, r13
seto dl
mov r8, -0x1 
inc r8
mov r9, -0x1 
movzx rbx, bl
adox rbx, r9
adox r14, [ rsp + 0x268 ]
seto bl
dec r8
movzx r12, r12b
adox r12, r8
adox r14, r10
seto r9b
movzx r10, byte [ rsp + 0x558 ]
inc r8
mov r12, -0x1 
adox r10, r12
adox r14, [ rsp + 0x148 ]
adcx r13, [ rsp + 0x580 ]
adcx rcx, [ rsp + 0x578 ]
mov r10, [ rsp + 0x4f8 ]
seto r8b
movzx r12, byte [ rsp + 0x550 ]
mov [ rsp + 0x588 ], rcx
mov rcx, 0x0 
dec rcx
adox r12, rcx
adox r10, [ rsp + 0x548 ]
setc r12b
clc
movzx rbx, bl
adcx rbx, rcx
adcx r10, [ rsp + 0x350 ]
setc bl
clc
movzx r9, r9b
adcx r9, rcx
adcx r10, [ rsp + 0x540 ]
setc r9b
clc
adcx rbp, [ rsp - 0x48 ]
seto cl
mov byte [ rsp + 0x590 ], r9b
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox r10, [ rsp + 0x180 ]
mov r8, [ rsp + 0x518 ]
seto r9b
mov [ rsp + 0x598 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rcx, cl
adox rcx, r13
adox r8, [ rsp + 0x520 ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov byte [ rsp + 0x5a0 ], r9b
mulx r9, r13, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x5a8 ], r9
mov [ rsp + 0x5b0 ], r13
mulx r13, r9, rcx
mov rcx, 0x2341f27177344 
mov [ rsp + 0x5b8 ], r13
mov [ rsp + 0x5c0 ], r10
mulx r10, r13, rcx
seto cl
mov [ rsp + 0x5c8 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbx, bl
adox rbx, r10
adox r8, [ rsp + 0x348 ]
mov rbx, r9
setc r10b
clc
adcx rbx, rdx
mov rbx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x5d0 ], r13
mov [ rsp + 0x5d8 ], r8
mulx r8, r13, rbx
seto bl
mov [ rsp + 0x5e0 ], r8
mov r8, 0x0 
dec r8
movzx rcx, cl
adox rcx, r8
adox r15, [ rsp + 0x528 ]
mov rcx, 0x7bc65c783158aea3 
mov [ rsp + 0x5e8 ], r15
mulx r15, r8, rcx
setc dl
clc
mov rcx, -0x1 
movzx r12, r12b
adcx r12, rcx
adcx rdi, [ rsp + 0x538 ]
seto r12b
inc rcx
mov rcx, -0x1 
movzx rbp, bpl
adox rbp, rcx
adox r14, r11
seto bpl
inc rcx
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox r14, [ rsp + 0x1c8 ]
mov r10, [ rsp + 0x598 ]
setc cl
clc
movzx rbp, bpl
adcx rbp, r11
adcx r10, [ rsp + 0x5c0 ]
mov rbp, [ rsp + 0x530 ]
setc r11b
clc
mov [ rsp + 0x5f0 ], rdi
mov rdi, -0x1 
movzx rcx, cl
adcx rcx, rdi
adcx rbp, [ rsp + 0x570 ]
movzx rcx, r12b
movzx rdi, byte [ rsp + 0x560 ]
lea rcx, [ rcx + rdi ]
adox r10, [ rsp + 0x2b8 ]
mov rdi, r9
seto r12b
mov [ rsp + 0x5f8 ], r10
mov r10, -0x2 
inc r10
adox rdi, [ rsp + 0x5b8 ]
seto r10b
mov byte [ rsp + 0x600 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox r14, rdi
seto dl
inc r12
mov rdi, -0x1 
movzx r10, r10b
adox r10, rdi
adox r9, [ rsp + 0x5b8 ]
adox r13, [ rsp + 0x5b8 ]
mov r10, [ rsp + 0x5e8 ]
seto r12b
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r10, [ rsp + 0x340 ]
setc bl
clc
movzx r12, r12b
adcx r12, rdi
adcx r8, [ rsp + 0x5e0 ]
adox rcx, [ rsp + 0x378 ]
mov r12, [ rsp + 0x5d8 ]
seto dil
mov [ rsp + 0x608 ], r14
movzx r14, byte [ rsp + 0x590 ]
mov byte [ rsp + 0x610 ], bl
mov rbx, 0x0 
dec rbx
adox r14, rbx
adox r12, [ rsp + 0x510 ]
seto r14b
movzx rbx, byte [ rsp + 0x5a0 ]
mov [ rsp + 0x618 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox rbx, r8
adox r12, [ rsp + 0x258 ]
adcx r15, [ rsp + 0x5b0 ]
setc bl
clc
movzx r14, r14b
adcx r14, r8
adcx r10, [ rsp + 0x508 ]
adcx rcx, [ rsp + 0x500 ]
adox r10, [ rsp + 0x250 ]
adox rcx, [ rsp + 0x248 ]
setc r14b
clc
movzx r11, r11b
adcx r11, r8
adcx r12, [ rsp + 0x588 ]
mov r11, [ rsp + 0x5d0 ]
seto r8b
mov [ rsp + 0x620 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rbx, bl
adox rbx, r15
adox r11, [ rsp + 0x5a8 ]
adcx r10, [ rsp + 0x5f0 ]
adcx rbp, rcx
setc bl
movzx rcx, byte [ rsp + 0x600 ]
clc
adcx rcx, r15
adcx r12, [ rsp + 0x2b0 ]
movzx rcx, r14b
movzx rdi, dil
lea rcx, [ rcx + rdi ]
seto dil
inc r15
mov r14, -0x1 
movzx r8, r8b
adox r8, r14
adox rcx, [ rsp + 0x290 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, r14
adcx r9, [ rsp + 0x5f8 ]
seto dl
dec r15
movzx r8, r8b
adox r8, r15
adox r10, [ rsp + 0x2c0 ]
movzx r14, dil
mov r8, [ rsp + 0x5c8 ]
lea r14, [ r14 + r8 ]
adcx r13, r12
adcx r10, [ rsp + 0x618 ]
movzx r8, byte [ rsp + 0x610 ]
mov rdi, [ rsp + 0x568 ]
lea r8, [ r8 + rdi ]
adox rbp, [ rsp + 0x2d0 ]
setc dil
seto r12b
mov r15, [ rsp + 0x608 ]
mov [ rsp + 0x628 ], r10
mov r10, 0xffffffffffffffff 
sub r15, r10
mov [ rsp + 0x630 ], r15
mov r15, r9
sbb r15, r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbx, bl
adox rbx, r10
adox rcx, r8
seto bl
inc r10
mov r8, -0x1 
movzx r12, r12b
adox r12, r8
adox rcx, [ rsp + 0x330 ]
movzx r12, bl
movzx rdx, dl
lea r12, [ r12 + rdx ]
setc dl
clc
movzx rdi, dil
adcx rdi, r8
adcx rbp, [ rsp + 0x620 ]
adox r12, [ rsp + 0x338 ]
adcx r11, rcx
adcx r14, r12
seto dil
adc dil, 0x0
movzx rdi, dil
movzx rbx, dl
add rbx, -0x1
mov rdx, r13
mov rbx, 0xffffffffffffffff 
sbb rdx, rbx
mov rcx, [ rsp + 0x628 ]
mov r12, 0xfdc1767ae2ffffff 
sbb rcx, r12
mov r10, rbp
mov r8, 0x7bc65c783158aea3 
sbb r10, r8
mov r8, r11
mov rbx, 0x6cfc5fd681c52056 
sbb r8, rbx
mov r12, r14
mov rbx, 0x2341f27177344 
sbb r12, rbx
movzx rbx, dil
sbb rbx, 0x00000000
mov rbx, [ rsp + 0x630 ]
cmovc rbx, [ rsp + 0x608 ]
cmovc r12, r14
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x30 ], r12
cmovc r8, r11
cmovc rcx, [ rsp + 0x628 ]
mov [ r14 + 0x0 ], rbx
cmovc rdx, r13
cmovc r10, rbp
mov [ r14 + 0x10 ], rdx
mov [ r14 + 0x28 ], r8
cmovc r15, r9
mov [ r14 + 0x8 ], r15
mov [ r14 + 0x18 ], rcx
mov [ r14 + 0x20 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1720
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3879
; seed 3705239160001646 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56479 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=45, initial num_batches=31): 969 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.017156819348784505
; number reverted permutation / tried permutation: 287 / 488 =58.811%
; number reverted decision / tried decision: 284 / 511 =55.577%
; validated in 200.173s
