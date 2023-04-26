SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1824
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], rdi
mulx rdi, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r12
mulx r12, rbx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rbx
mulx rbx, r12, [ rax + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r8
mulx r8, rbp, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rbp
mulx rbp, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], r14
mulx r14, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x18 ], r14
mov [ rsp + 0x20 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r13
mulx r13, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
test al, al
adox r12, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], r12
mulx r12, r11, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x50 ], rbx
mov [ rsp + 0x58 ], r13
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x60 ], r13
mov [ rsp + 0x68 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], r13
mulx r13, rbx, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x80 ], r13
mov [ rsp + 0x88 ], rbx
mulx rbx, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], r13
mov [ rsp + 0xa8 ], rbx
mulx rbx, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xb0 ], rbx
mov [ rsp + 0xb8 ], r13
mulx r13, rbx, [ rsi + 0x0 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0xc0 ], r13
mov [ rsp + 0xc8 ], rbx
mulx rbx, r13, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], rbx
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x100 ], rbx
mov [ rsp + 0x108 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x110 ], rbp
mov [ rsp + 0x118 ], rbx
mulx rbx, rbp, [ rax + 0x0 ]
adcx r11, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], r11
mulx r11, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], rbp
mulx rbp, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x138 ], rbp
mov [ rsp + 0x140 ], r11
mulx r11, rbp, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x148 ], r12
mov [ rsp + 0x150 ], r8
mulx r8, r12, rcx
seto dl
mov [ rsp + 0x158 ], r11
mov r11, -0x2 
inc r11
adox r14, r15
setc r15b
clc
adcx r10, r13
mov r13b, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x160 ], r10
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, r12
mov [ rsp + 0x168 ], r11
setc r11b
clc
adcx rdx, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x170 ], r14
mov byte [ rsp + 0x178 ], r13b
mulx r13, r14, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x180 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r11, r11b
adox r11, r13
adox rdi, r9
mov r9, r12
setc r11b
clc
adcx r9, r8
seto r13b
mov [ rsp + 0x188 ], rdi
mov rdi, -0x2 
inc rdi
adox rbp, r10
adcx r12, r8
mov r10b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x190 ], rbp
mulx rbp, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x198 ], rbp
mov [ rsp + 0x1a0 ], r14
mulx r14, rbp, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x1a8 ], r14
mov [ rsp + 0x1b0 ], rbp
mulx rbp, r14, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b8 ], r14
mov [ rsp + 0x1c0 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
setc dl
clc
adcx rbx, rbp
mov rbp, [ rsp + 0x158 ]
adox rbp, [ rsp + 0x150 ]
mov [ rsp + 0x1c8 ], rbx
seto bl
mov [ rsp + 0x1d0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r15, r15b
adox r15, rbp
adox r14, [ rsp + 0x148 ]
mov r15, [ rsp + 0xe8 ]
setc bpl
clc
mov [ rsp + 0x1d8 ], r14
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx r15, [ rsp + 0x140 ]
mov rbx, [ rsp + 0x30 ]
seto r14b
mov [ rsp + 0x1e0 ], r15
movzx r15, byte [ rsp + 0x178 ]
mov byte [ rsp + 0x1e8 ], bpl
mov rbp, 0x0 
dec rbp
adox r15, rbp
adox rbx, [ rsp + 0x40 ]
mov r15b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1f0 ], rbx
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x8 ]
adox rdx, [ rsp + 0x10 ]
mov [ rsp + 0x1f8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x200 ], rbp
mov byte [ rsp + 0x208 ], r10b
mulx r10, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x210 ], rbx
mov [ rsp + 0x218 ], r12
mulx r12, rbx, [ rsi + 0x28 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x220 ], r12
seto r12b
mov byte [ rsp + 0x228 ], r13b
mov r13, -0x2 
inc r13
adox rdx, [ rsp - 0x10 ]
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x230 ], r12b
mov [ rsp + 0x238 ], r9
mulx r9, r12, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x138 ]
mov rdx, [ rsp - 0x30 ]
adox rdx, [ rsp + 0x20 ]
mov [ rsp + 0x240 ], rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x248 ], rcx
mov [ rsp + 0x250 ], r13
mulx r13, rcx, rbx
setc dl
clc
mov rbx, -0x1 
movzx r14, r14b
adcx r14, rbx
adcx rdi, r12
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mulx rbx, r12, [ rax + 0x28 ]
adox rbp, [ rsp + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x258 ], rdi
mov [ rsp + 0x260 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
adox r10, [ rsp + 0x58 ]
adcx rdi, r9
seto dl
mov r9, 0x0 
dec r9
movzx r15, r15b
adox r15, r9
adox r8, rcx
mov r15b, dl
mov rdx, [ rax + 0x30 ]
mulx r9, rcx, [ rsi + 0x28 ]
adox r13, [ rsp + 0xf8 ]
mov rdx, [ rsp + 0x238 ]
mov [ rsp + 0x268 ], rdi
setc dil
clc
mov [ rsp + 0x270 ], r13
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx rdx, [ rsp + 0x250 ]
seto r11b
inc r13
adox rdx, [ rsp + 0x130 ]
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x278 ], r10
mov [ rsp + 0x280 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x38 ]
mov byte [ rsp + 0x288 ], r11b
setc r11b
mov [ rsp + 0x290 ], r9
movzx r9, byte [ rsp + 0x228 ]
clc
mov byte [ rsp + 0x298 ], r15b
mov r15, -0x1 
adcx r9, r15
adcx rdx, [ rsp + 0xa8 ]
mov r9, 0x2341f27177344 
xchg rdx, r13
mov [ rsp + 0x2a0 ], r13
mulx r13, r15, r9
mov r9, [ rsp + 0x248 ]
mov [ rsp + 0x2a8 ], r13
seto r13b
mov [ rsp + 0x2b0 ], r15
mov r15, 0x0 
dec r15
movzx r11, r11b
adox r11, r15
adox r9, [ rsp + 0x218 ]
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x2b8 ], r9
mulx r9, r15, r11
seto r11b
mov byte [ rsp + 0x2c0 ], r13b
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox r12, [ rsp + 0x220 ]
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2c8 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x2d0 ], r11b
mov [ rsp + 0x2d8 ], r12
mulx r12, r11, [ rax + 0x20 ]
adcx r13, [ rsp + 0xa0 ]
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x2e0 ], r13
seto r13b
mov [ rsp + 0x2e8 ], r12
movzx r12, byte [ rsp + 0x208 ]
mov [ rsp + 0x2f0 ], r11
mov r11, 0x0 
dec r11
adox r12, r11
adox rdx, [ rsp + 0x68 ]
setc r12b
clc
movzx r13, r13b
adcx r13, r11
adcx rbx, rcx
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mulx r11, r13, [ rsi + 0x8 ]
adox r10, [ rsp + 0x60 ]
setc dl
clc
mov [ rsp + 0x2f8 ], rbx
mov rbx, -0x1 
movzx rdi, dil
adcx rdi, rbx
adcx rbp, r13
mov rdi, r15
seto r13b
inc rbx
adox rdi, r9
mov rbx, r15
adox rbx, r9
mov [ rsp + 0x300 ], r10
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov [ rsp + 0x308 ], rcx
mov [ rsp + 0x310 ], rbx
mulx rbx, rcx, r14
adox rcx, r9
setc r9b
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r8, [ rsp + 0x2f0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x318 ], r8
mulx r8, r13, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x78 ]
mov [ rsp + 0x320 ], rcx
setc cl
mov [ rsp + 0x328 ], rbp
movzx rbp, byte [ rsp + 0x298 ]
clc
mov [ rsp + 0x330 ], rdi
mov rdi, -0x1 
adcx rbp, rdi
adcx rdx, [ rsp + 0x50 ]
mov rbp, [ rsp + 0x108 ]
setc dil
clc
mov [ rsp + 0x338 ], rdx
mov rdx, -0x1 
movzx rcx, cl
adcx rcx, rdx
adcx rbp, [ rsp + 0x2e8 ]
movzx rcx, r10b
mov rdx, [ rsp + 0x290 ]
lea rcx, [ rcx + rdx ]
setc dl
movzx r10, byte [ rsp + 0x1e8 ]
clc
mov [ rsp + 0x340 ], rcx
mov rcx, -0x1 
adcx r10, rcx
adcx r13, [ rsp + 0x128 ]
mov r10, [ rsp + 0x200 ]
seto cl
mov [ rsp + 0x348 ], r13
mov r13, 0x0 
dec r13
movzx rdx, dl
adox rdx, r13
adox r10, [ rsp + 0x100 ]
setc dl
clc
movzx r9, r9b
adcx r9, r13
adcx r11, [ rsp + 0x118 ]
mov r9, [ rsp + 0xf0 ]
setc r13b
mov [ rsp + 0x350 ], r10
movzx r10, byte [ rsp + 0x288 ]
clc
mov [ rsp + 0x358 ], rbp
mov rbp, -0x1 
adcx r10, rbp
adcx r9, [ rsp + 0xd8 ]
movzx r10, r13b
mov rbp, [ rsp + 0x110 ]
lea r10, [ r10 + rbp ]
mov rbp, [ rsp + 0x70 ]
seto r13b
mov [ rsp + 0x360 ], r10
mov r10, 0x0 
dec r10
movzx rdi, dil
adox rdi, r10
adox rbp, [ rsp + 0xc8 ]
mov rdi, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0x0 ]
mov r10, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x368 ], r11
mov [ rsp + 0x370 ], rdi
mulx rdi, r11, r10
mov r10, [ rsp - 0x40 ]
mov [ rsp + 0x378 ], rbp
setc bpl
mov [ rsp + 0x380 ], r9
movzx r9, byte [ rsp + 0x230 ]
clc
mov byte [ rsp + 0x388 ], r13b
mov r13, -0x1 
adcx r9, r13
adcx r10, [ rsp + 0x1c0 ]
mov r9, [ rsp + 0x1a0 ]
seto r13b
mov [ rsp + 0x390 ], r10
mov r10, 0x0 
dec r10
movzx r12, r12b
adox r12, r10
adox r9, [ rsp + 0x2d8 ]
mov r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x398 ], r9
mulx r9, r10, [ rax + 0x20 ]
movzx rdx, r13b
mov byte [ rsp + 0x3a0 ], bpl
mov rbp, [ rsp + 0xc0 ]
lea rdx, [ rdx + rbp ]
seto bpl
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox rbx, r11
mov rcx, [ rsp + 0xb8 ]
seto r11b
inc r13
mov r13, -0x1 
movzx rbp, bpl
adox rbp, r13
adox rcx, [ rsp + 0x180 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x3a8 ], rcx
mulx rcx, r13, rbp
seto bpl
mov [ rsp + 0x3b0 ], rbx
mov rbx, 0x0 
dec rbx
movzx r14, r14b
adox r14, rbx
adox r8, [ rsp + 0x1b0 ]
seto r14b
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox rdi, r13
adox rcx, [ rsp + 0x2b0 ]
setc r11b
clc
movzx r14, r14b
adcx r14, rbx
adcx r10, [ rsp + 0x1a8 ]
adcx r9, [ rsp - 0x20 ]
movzx r13, byte [ rsp + 0x388 ]
mov r14, [ rsp + 0x1f8 ]
lea r13, [ r13 + r14 ]
mov r14, [ rsp + 0x260 ]
seto bl
mov [ rsp + 0x3b8 ], r9
movzx r9, byte [ rsp + 0x2d0 ]
mov [ rsp + 0x3c0 ], r10
mov r10, 0x0 
dec r10
adox r9, r10
adox r14, [ rsp + 0x280 ]
movzx r9, bpl
mov r10, [ rsp + 0xb0 ]
lea r9, [ r9 + r10 ]
setc r10b
clc
adcx r15, rdx
movzx r15, bl
mov rdx, [ rsp + 0x2a8 ]
lea r15, [ r15 + rdx ]
mov rdx, [ rsp + 0x2b8 ]
setc bpl
movzx rbx, byte [ rsp + 0x2c0 ]
clc
mov [ rsp + 0x3c8 ], r8
mov r8, -0x1 
adcx rbx, r8
adcx rdx, [ rsp + 0x120 ]
adcx r14, [ rsp + 0x1d8 ]
mov rbx, [ rsp + 0x270 ]
adox rbx, [ rsp + 0x278 ]
adcx rbx, [ rsp + 0x258 ]
setc r8b
clc
mov [ rsp + 0x3d0 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rdx, [ rsp + 0x330 ]
setc bpl
clc
adcx rdx, [ rsp + 0x28 ]
movzx r9, byte [ rsp + 0x3a0 ]
mov [ rsp + 0x3d8 ], r13
mov r13, [ rsp - 0x8 ]
lea r9, [ r9 + r13 ]
mov r13, [ rsp + 0x338 ]
adox r13, [ rsp + 0x380 ]
mov byte [ rsp + 0x3e0 ], r11b
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x3e8 ], r15
mov [ rsp + 0x3f0 ], rcx
mulx rcx, r15, r11
mov r11, [ rsp + 0x370 ]
adox r11, [ rsp + 0x378 ]
mov [ rsp + 0x3f8 ], rdi
mov rdi, [ rsp - 0x28 ]
mov [ rsp + 0x400 ], rbx
setc bl
clc
mov [ rsp + 0x408 ], r14
mov r14, -0x1 
movzx r10, r10b
adcx r10, r14
adcx rdi, [ rsp + 0x88 ]
adox r9, r12
setc r12b
clc
movzx r8, r8b
adcx r8, r14
adcx r13, [ rsp + 0x268 ]
adcx r11, [ rsp + 0x328 ]
mov r10, 0x7bc65c783158aea3 
mulx r14, r8, r10
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x410 ], rdi
mov [ rsp + 0x418 ], r14
mulx r14, rdi, r10
mov r10, r15
mov [ rsp + 0x420 ], r8
setc r8b
clc
adcx r10, rcx
mov [ rsp + 0x428 ], r14
mov r14, r15
adcx r14, rcx
mov [ rsp + 0x430 ], r14
mov r14, 0x2341f27177344 
mov [ rsp + 0x438 ], r10
mov [ rsp + 0x440 ], r9
mulx r9, r10, r14
movzx r14, r12b
mov [ rsp + 0x448 ], r9
mov r9, [ rsp + 0x80 ]
lea r14, [ r14 + r9 ]
adcx rdi, rcx
mov r9, [ rsp + 0x408 ]
seto cl
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r9, [ rsp + 0x310 ]
mov rbp, [ rsp + 0x400 ]
adox rbp, [ rsp + 0x320 ]
adox r13, [ rsp + 0x3b0 ]
adox r11, [ rsp + 0x3f8 ]
seto r12b
mov [ rsp + 0x450 ], r14
mov r14, 0x0 
dec r14
movzx rbx, bl
adox rbx, r14
adox r9, [ rsp + 0x170 ]
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x458 ], rdi
mulx rdi, r14, rbx
setc bl
clc
adcx r15, rdx
mov r15, [ rsp + 0x368 ]
seto dl
mov [ rsp + 0x460 ], r11
mov r11, 0x0 
dec r11
movzx r8, r8b
adox r8, r11
adox r15, [ rsp + 0x440 ]
adcx r9, [ rsp + 0x438 ]
setc r8b
clc
adcx r9, [ rsp + 0xe0 ]
movzx rcx, cl
movzx r11, cl
adox r11, [ rsp + 0x360 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mov byte [ rsp + 0x468 ], r8b
mov [ rsp + 0x470 ], r13
mulx r13, r8, r9
mov rdx, r8
mov [ rsp + 0x478 ], rbp
setc bpl
clc
adcx rdx, r13
mov [ rsp + 0x480 ], rdx
mov rdx, r8
adcx rdx, r13
mov [ rsp + 0x488 ], rdx
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x490 ], bpl
mov byte [ rsp + 0x498 ], cl
mulx rcx, rbp, r9
setc dl
clc
mov [ rsp + 0x4a0 ], rcx
mov rcx, -0x1 
movzx r12, r12b
adcx r12, rcx
adcx r15, [ rsp + 0x3f0 ]
adcx r11, [ rsp + 0x3e8 ]
mov r12, [ rsp + 0x420 ]
setc cl
clc
mov [ rsp + 0x4a8 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r12, [ rsp + 0x428 ]
adcx r14, [ rsp + 0x418 ]
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov [ rsp + 0x4b0 ], r14
mulx r14, r11, rbx
adcx r10, rdi
seto dil
mov rbx, 0x0 
dec rbx
movzx r9, r9b
adox r9, rbx
adox r13, r11
adox rbp, r14
mov r9, 0x2341f27177344 
mulx r14, r11, r9
mov rbx, [ rsp + 0x448 ]
mov r9, 0x0 
adcx rbx, r9
mov r9, 0x6cfc5fd681c52056 
mov [ rsp + 0x4b8 ], rbx
mov [ rsp + 0x4c0 ], rbp
mulx rbp, rbx, r9
adox rbx, [ rsp + 0x4a0 ]
mov r9, [ rsp + 0x478 ]
mov [ rsp + 0x4c8 ], rbx
movzx rbx, byte [ rsp + 0x498 ]
clc
mov [ rsp + 0x4d0 ], r13
mov r13, -0x1 
adcx rbx, r13
adcx r9, [ rsp + 0x308 ]
movzx rbx, cl
movzx rdi, dil
lea rbx, [ rbx + rdi ]
adox r11, rbp
mov rdi, [ rsp + 0x470 ]
adcx rdi, [ rsp + 0x300 ]
mov rcx, 0x0 
adox r14, rcx
mov rbp, [ rsp + 0x318 ]
adcx rbp, [ rsp + 0x460 ]
movzx rcx, byte [ rsp + 0x468 ]
inc r13
mov r13, -0x1 
adox rcx, r13
adox r9, [ rsp + 0x430 ]
adox rdi, [ rsp + 0x458 ]
setc cl
movzx r13, byte [ rsp + 0x490 ]
clc
mov [ rsp + 0x4d8 ], r14
mov r14, -0x1 
adcx r13, r14
adcx r9, [ rsp + 0x160 ]
adcx rdi, [ rsp + 0x188 ]
setc r13b
clc
movzx rcx, cl
adcx rcx, r14
adcx r15, [ rsp + 0x358 ]
adox r12, rbp
setc cl
clc
movzx r13, r13b
adcx r13, r14
adcx r12, [ rsp + 0x2a0 ]
mov rbp, [ rsp + 0x350 ]
setc r13b
clc
movzx rcx, cl
adcx rcx, r14
adcx rbp, [ rsp + 0x4a8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x4e0 ], r11
mulx r11, r14, [ rax + 0x28 ]
adox r15, [ rsp + 0x4b0 ]
setc dl
clc
adcx r8, rcx
adox r10, rbp
seto r8b
mov rcx, 0x0 
dec rcx
movzx r13, r13b
adox r13, rcx
adox r15, [ rsp + 0x2e0 ]
adcx r9, [ rsp + 0x480 ]
adcx rdi, [ rsp + 0x488 ]
adcx r12, [ rsp + 0x4d0 ]
seto r13b
movzx rbp, byte [ rsp + 0x3e0 ]
inc rcx
mov rcx, -0x1 
adox rbp, rcx
adox r14, [ rsp + 0x198 ]
seto bpl
inc rcx
mov rcx, -0x1 
movzx r13, r13b
adox r13, rcx
adox r10, [ rsp + 0x398 ]
seto r13b
inc rcx
adox r9, [ rsp - 0x48 ]
adcx r15, [ rsp + 0x4c0 ]
adox rdi, [ rsp + 0x48 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x4e8 ], r14
mov [ rsp + 0x4f0 ], r15
mulx r15, r14, r9
mov rdx, r14
mov [ rsp + 0x4f8 ], r12
seto r12b
mov [ rsp + 0x500 ], r11
mov r11, -0x2 
inc r11
adox rdx, r15
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov byte [ rsp + 0x508 ], r12b
mov byte [ rsp + 0x510 ], bpl
mulx rbp, r12, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x518 ], rbp
mov [ rsp + 0x520 ], r12
mulx r12, rbp, r11
seto r11b
mov [ rsp + 0x528 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox rbx, [ rsp + 0x3d8 ]
mov rcx, r14
seto r12b
mov [ rsp + 0x530 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, rdx
adox r9, rdi
seto cl
inc rbp
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox rbx, [ rsp + 0x4b8 ]
adcx r10, [ rsp + 0x4c8 ]
seto r8b
dec rbp
movzx r13, r13b
adox r13, rbp
adox rbx, [ rsp + 0x3a8 ]
adcx rbx, [ rsp + 0x4e0 ]
mov rdi, 0x6cfc5fd681c52056 
mulx rbp, r13, rdi
mov rdi, [ rsp + 0x98 ]
mov byte [ rsp + 0x538 ], cl
setc cl
mov [ rsp + 0x540 ], rbx
movzx rbx, byte [ rsp + 0x510 ]
clc
mov [ rsp + 0x548 ], r10
mov r10, -0x1 
adcx rbx, r10
adcx rdi, [ rsp + 0x500 ]
movzx rbx, r8b
movzx r12, r12b
lea rbx, [ rbx + r12 ]
adox rbx, [ rsp + 0x3d0 ]
setc r12b
clc
adcx r9, [ rsp + 0x168 ]
mov r8, r15
seto r10b
mov byte [ rsp + 0x550 ], r12b
mov r12, 0x0 
dec r12
movzx r11, r11b
adox r11, r12
adox r8, r14
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r9
mulx r12, r11, r14
setc r14b
clc
mov [ rsp + 0x558 ], r12
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx rbx, [ rsp + 0x4d8 ]
mov rcx, 0x2341f27177344 
mov byte [ rsp + 0x560 ], r14b
mulx r14, r12, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x568 ], r14
mov [ rsp + 0x570 ], r12
mulx r12, r14, rcx
movzx rcx, r10b
mov [ rsp + 0x578 ], r11
mov r11, 0x0 
adcx rcx, r11
mov r10, r14
clc
adcx r10, r12
mov r11, r14
adcx r11, r12
adox r15, [ rsp + 0x520 ]
mov [ rsp + 0x580 ], r11
mov r11, [ rsp + 0x530 ]
adox r11, [ rsp + 0x518 ]
adox r13, [ rsp + 0x528 ]
mov [ rsp + 0x588 ], r13
setc r13b
clc
adcx r14, rdx
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x590 ], r11
mov [ rsp + 0x598 ], r10
mulx r10, r11, r14
mov r14, [ rsp + 0x4f8 ]
mov [ rsp + 0x5a0 ], r10
setc r10b
mov [ rsp + 0x5a8 ], rcx
movzx rcx, byte [ rsp + 0x508 ]
clc
mov [ rsp + 0x5b0 ], r11
mov r11, -0x1 
adcx rcx, r11
adcx r14, [ rsp + 0x1f0 ]
mov rcx, 0x2341f27177344 
xchg rdx, rcx
mov byte [ rsp + 0x5b8 ], r10b
mulx r10, r11, r9
mov r9, [ rsp + 0x4f0 ]
adcx r9, [ rsp + 0x210 ]
adox r11, rbp
mov rbp, [ rsp + 0x390 ]
adcx rbp, [ rsp + 0x548 ]
mov rdx, [ rsp + 0x4e8 ]
adcx rdx, [ rsp + 0x540 ]
mov [ rsp + 0x5c0 ], r10
mov r10, 0x7bc65c783158aea3 
xchg rdx, r10
mov [ rsp + 0x5c8 ], r11
mov [ rsp + 0x5d0 ], r10
mulx r10, r11, rcx
adcx rdi, rbx
seto cl
movzx rbx, byte [ rsp + 0x538 ]
mov rdx, 0x0 
dec rdx
adox rbx, rdx
adox r14, r8
seto bl
inc rdx
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox r12, [ rsp + 0x578 ]
setc r13b
movzx rdx, byte [ rsp + 0x560 ]
clc
adcx rdx, r8
adcx r14, [ rsp + 0x190 ]
seto dl
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox r9, r15
movzx r15, byte [ rsp + 0x550 ]
mov rbx, [ rsp + 0x90 ]
lea r15, [ r15 + rbx ]
seto bl
inc r8
mov r8, -0x1 
movzx rdx, dl
adox rdx, r8
adox r11, [ rsp + 0x558 ]
adox r10, [ rsp + 0x5b0 ]
seto dl
inc r8
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox r15, [ rsp + 0x5a8 ]
mov r13, [ rsp + 0x5a0 ]
seto r8b
mov [ rsp + 0x5d8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox r13, [ rsp + 0x570 ]
seto dl
movzx r15, byte [ rsp + 0x5b8 ]
mov [ rsp + 0x5e0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r15, r13
adox r14, [ rsp + 0x598 ]
seto r15b
inc r13
adox r14, [ rsp + 0x1b8 ]
mov r13, 0x7bc65c783158aea3 
xchg rdx, r14
mov byte [ rsp + 0x5e8 ], r8b
mov [ rsp + 0x5f0 ], r10
mulx r10, r8, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x5f8 ], cl
mov [ rsp + 0x600 ], r11
mulx r11, rcx, r13
mov r13, 0x6cfc5fd681c52056 
mov [ rsp + 0x608 ], r10
mov [ rsp + 0x610 ], r8
mulx r8, r10, r13
seto r13b
mov [ rsp + 0x618 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox rbp, [ rsp + 0x590 ]
mov rbx, [ rsp + 0x5d0 ]
adox rbx, [ rsp + 0x588 ]
mov r8, 0x2341f27177344 
mov [ rsp + 0x620 ], r10
mov byte [ rsp + 0x628 ], r14b
mulx r14, r10, r8
adox rdi, [ rsp + 0x5c8 ]
adcx r9, [ rsp + 0x1d0 ]
adcx rbp, [ rsp + 0x1e0 ]
adcx rbx, [ rsp + 0x240 ]
mov r8, 0xfdc1767ae2ffffff 
mov [ rsp + 0x630 ], r14
mov [ rsp + 0x638 ], rbx
mulx rbx, r14, r8
seto r8b
mov [ rsp + 0x640 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r15, r15b
adox r15, r10
adox r9, [ rsp + 0x580 ]
mov r15, rcx
setc r10b
clc
adcx r15, r11
mov byte [ rsp + 0x648 ], r8b
mov r8, rcx
adcx r8, r11
mov [ rsp + 0x650 ], r8
setc r8b
clc
mov [ rsp + 0x658 ], rbx
mov rbx, -0x1 
movzx r10, r10b
adcx r10, rbx
adcx rdi, [ rsp + 0x2c8 ]
setc r10b
clc
adcx rcx, rdx
setc cl
clc
movzx r8, r8b
adcx r8, rbx
adcx r11, r14
setc dl
clc
movzx r13, r13b
adcx r13, rbx
adcx r9, [ rsp + 0x1c8 ]
setc r13b
clc
movzx rcx, cl
adcx rcx, rbx
adcx r9, r15
adox r12, rbp
setc bpl
seto r14b
mov r15, r9
mov r8, 0xffffffffffffffff 
sub r15, r8
movzx rcx, byte [ rsp + 0x628 ]
mov rbx, [ rsp + 0x568 ]
lea rcx, [ rcx + rbx ]
mov rbx, [ rsp + 0x610 ]
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rdx, dl
adox rdx, r8
adox rbx, [ rsp + 0x658 ]
mov rdx, [ rsp + 0x608 ]
adox rdx, [ rsp + 0x620 ]
mov r8, [ rsp + 0x618 ]
adox r8, [ rsp + 0x640 ]
mov [ rsp + 0x660 ], r15
mov r15, [ rsp + 0x638 ]
mov [ rsp + 0x668 ], r8
setc r8b
clc
mov [ rsp + 0x670 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r15, [ rsp + 0x600 ]
movzx r14, byte [ rsp + 0x5f8 ]
mov rdx, [ rsp + 0x5c0 ]
lea r14, [ r14 + rdx ]
adcx rdi, [ rsp + 0x5f0 ]
setc dl
mov [ rsp + 0x678 ], rbx
movzx rbx, byte [ rsp + 0x648 ]
clc
mov [ rsp + 0x680 ], rdi
mov rdi, -0x1 
adcx rbx, rdi
adcx r14, [ rsp + 0x5d8 ]
movzx rbx, byte [ rsp + 0x5e8 ]
mov rdi, 0x0 
adcx rbx, rdi
mov rdi, [ rsp + 0x630 ]
mov byte [ rsp + 0x688 ], r8b
mov r8, 0x0 
adox rdi, r8
add r10b, 0x7F
adox r14, [ rsp + 0x2f8 ]
adox rbx, [ rsp + 0x340 ]
mov r10, -0x1 
movzx rdx, dl
adcx rdx, r10
adcx r14, [ rsp + 0x5e0 ]
setc dl
clc
movzx r13, r13b
adcx r13, r10
adcx r12, [ rsp + 0x348 ]
seto r13b
dec r8
movzx rbp, bpl
adox rbp, r8
adox r12, [ rsp + 0x650 ]
setc r10b
clc
movzx rdx, dl
adcx rdx, r8
adcx rbx, rcx
movzx rbp, r13b
mov rcx, 0x0 
adcx rbp, rcx
clc
movzx r10, r10b
adcx r10, r8
adcx r15, [ rsp + 0x3c8 ]
adox r11, r15
setc r13b
seto dl
movzx r10, byte [ rsp + 0x688 ]
add r10, -0x1
mov r10, r12
mov r15, 0xffffffffffffffff 
sbb r10, r15
mov rcx, r11
sbb rcx, r15
mov r8, [ rsp + 0x3c0 ]
mov r15, 0x0 
dec r15
movzx r13, r13b
adox r13, r15
adox r8, [ rsp + 0x680 ]
adox r14, [ rsp + 0x3b8 ]
seto r13b
inc r15
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox r8, [ rsp + 0x678 ]
adox r14, [ rsp + 0x670 ]
seto dl
mov r15, r8
mov [ rsp + 0x690 ], r10
mov r10, 0xfdc1767ae2ffffff 
sbb r15, r10
mov r10, r14
mov [ rsp + 0x698 ], r15
mov r15, 0x7bc65c783158aea3 
sbb r10, r15
mov r15, 0x0 
dec r15
movzx r13, r13b
adox r13, r15
adox rbx, [ rsp + 0x410 ]
adox rbp, [ rsp + 0x450 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, r15
adcx rbx, [ rsp + 0x668 ]
adcx rdi, rbp
seto dl
adc dl, 0x0
movzx rdx, dl
movzx rbp, r13b
add rbp, -0x1
mov rbp, rbx
mov r13, 0x6cfc5fd681c52056 
sbb rbp, r13
mov r15, rdi
mov r13, 0x2341f27177344 
sbb r15, r13
movzx r13, dl
sbb r13, 0x00000000
mov r13, [ rsp + 0x660 ]
cmovc r13, r9
cmovc rcx, r11
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rcx
cmovc rbp, rbx
mov [ r9 + 0x28 ], rbp
mov r11, [ rsp + 0x690 ]
cmovc r11, r12
mov [ r9 + 0x8 ], r11
mov r12, [ rsp + 0x698 ]
cmovc r12, r8
mov [ r9 + 0x18 ], r12
mov [ r9 + 0x0 ], r13
cmovc r10, r14
cmovc r15, rdi
mov [ r9 + 0x30 ], r15
mov [ r9 + 0x20 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1824
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3153
; seed 2128444020844024 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 81604 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=29, initial num_batches=31): 1172 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.014362041076417822
; number reverted permutation / tried permutation: 247 / 506 =48.814%
; number reverted decision / tried decision: 251 / 493 =50.913%
; validated in 372.737s
