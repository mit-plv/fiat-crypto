SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1416
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], rdi
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r9
mulx r9, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r15
mulx r15, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], r9
mulx r9, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], rbx
mulx rbx, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], rcx
mulx rcx, r14, r8
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x58 ], r13
mov [ rsp + 0x60 ], r9
mulx r9, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r13
mulx r13, r9, [ rax + 0x20 ]
mov rdx, r14
add rdx, rcx
mov [ rsp + 0x78 ], r13
mov r13, r14
adcx r13, rcx
mov [ rsp + 0x80 ], r9
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r9
mov [ rsp + 0x88 ], r15
mov [ rsp + 0x90 ], r11
mulx r11, r15, r8
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r15
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r15
mov [ rsp + 0xb0 ], r11
mulx r11, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], r15
mulx r15, r11, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], r11
mulx r11, r15, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rbp, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], rbx
mulx rbx, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rdi
mulx rdi, rbx, [ rax + 0x28 ]
seto dl
mov [ rsp + 0xf0 ], rdi
mov rdi, -0x2 
inc rdi
adox r14, r8
setc r14b
clc
movzx rdx, dl
adcx rdx, rdi
adcx r12, r15
adcx r10, r11
adox r9, rbp
adox r13, r12
setc r15b
clc
adcx r9, [ rsp + 0xd8 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, r11, [ rsi + 0x0 ]
mov rdx, 0xfdc1767ae2ffffff 
mulx rdi, r12, r8
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r13
mulx r13, rbx, r9
seto dl
mov [ rsp + 0x108 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox rcx, r12
mov r14, [ rsp + 0xd0 ]
setc r12b
clc
movzx r15, r15b
adcx r15, r13
adcx r14, [ rsp + 0x90 ]
adcx r11, [ rsp + 0xc8 ]
seto r15b
inc r13
mov r13, -0x1 
movzx rdx, dl
adox rdx, r13
adox r10, rcx
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x110 ], rcx
mov [ rsp + 0x118 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x120 ], r10
mov r10, -0x2 
inc r10
adox rcx, r13
adox rbx, [ rsp + 0x88 ]
mov r13b, dl
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x128 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x130 ], rcx
mov rcx, -0x2 
inc rcx
adox r10, [ rsp + 0x60 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r8
mov [ rsp + 0x138 ], r10
mov byte [ rsp + 0x140 ], r12b
mulx r12, r10, rcx
setc cl
clc
mov [ rsp + 0x148 ], r11
mov r11, -0x1 
movzx r15, r15b
adcx r15, r11
adcx rdi, r10
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
setc dl
clc
adcx r10, [ rsp + 0x58 ]
mov [ rsp + 0x150 ], r10
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], rdi
mov [ rsp + 0x160 ], r14
mulx r14, rdi, [ rax + 0x10 ]
adox rdi, rbx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x168 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
adox r14, [ rsp + 0x50 ]
adcx r11, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x170 ], rdi
mov [ rsp + 0x178 ], rbx
mulx rbx, rdi, [ rax + 0x30 ]
seto dl
mov [ rsp + 0x180 ], r14
mov r14, 0x0 
dec r14
movzx rcx, cl
adox rcx, r14
adox rbp, rdi
mov cl, dl
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, [ rax + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x188 ], r14
mov [ rsp + 0x190 ], r11
mulx r11, r14, r15
setc r15b
clc
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r12, [ rsp + 0xa0 ]
seto r10b
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox rdi, [ rsp + 0x40 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x198 ], rdi
mulx rdi, r8, [ rsi + 0x8 ]
adcx r14, [ rsp + 0x98 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rsp + 0x38 ]
clc
mov [ rsp + 0x1a0 ], r11
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx rdx, [ rsp + 0x30 ]
mov rcx, [ rsp + 0x160 ]
setc r11b
clc
mov [ rsp + 0x1a8 ], rdx
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx rcx, [ rsp + 0x158 ]
adcx r12, [ rsp + 0x148 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x1b0 ], r11b
mulx r11, r13, [ rax + 0x8 ]
adcx r14, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox r13, [ rsp + 0x28 ]
movzx rbp, r10b
lea rbp, [ rbp + rbx ]
setc bl
clc
mov r10, -0x1 
movzx r15, r15b
adcx r15, r10
adcx r8, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x80 ]
mov r15, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x78 ]
mov r10b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], r15
mulx r15, r13, [ rax + 0x30 ]
adcx r13, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x1c8 ], r10b
mov [ rsp + 0x1d0 ], r15
mulx r15, r10, [ rax + 0x10 ]
setc dl
clc
mov [ rsp + 0x1d8 ], r13
mov r13, -0x1 
movzx rbx, bl
adcx rbx, r13
adcx rbp, [ rsp + 0x1a0 ]
adox r10, r11
adox r15, [ rsp - 0x28 ]
mov r11, [ rsp + 0x100 ]
seto bl
movzx r13, byte [ rsp + 0x140 ]
mov [ rsp + 0x1e0 ], r15
mov r15, 0x0 
dec r15
adox r13, r15
adox r11, [ rsp + 0x150 ]
mov r13, [ rsp + 0x120 ]
adox r13, [ rsp + 0x190 ]
adox r8, rcx
adox rdi, r12
adox r14, [ rsp + 0x1c0 ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, r9
mulx r15, r12, rcx
mov rcx, 0xffffffffffffffff 
mov byte [ rsp + 0x1e8 ], r9b
mov [ rsp + 0x1f0 ], r10
mulx r10, r9, rcx
adox rbp, [ rsp + 0x1d8 ]
mov rcx, r9
mov [ rsp + 0x1f8 ], rbp
seto bpl
mov [ rsp + 0x200 ], r14
mov r14, -0x2 
inc r14
adox rcx, r10
mov r14, r9
adox r14, r10
adox r12, r10
mov r10, 0x7bc65c783158aea3 
mov byte [ rsp + 0x208 ], bpl
mov byte [ rsp + 0x210 ], bl
mulx rbx, rbp, r10
adox rbp, r15
seto r15b
mov r10, -0x2 
inc r10
adox r9, rdx
adox rcx, r11
adox r14, r13
adox r12, r8
seto r9b
inc r10
mov r11, -0x1 
movzx r15, r15b
adox r15, r11
adox rbx, [ rsp + 0x118 ]
setc r13b
clc
movzx r9, r9b
adcx r9, r11
adcx rdi, rbp
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mulx rbp, r15, [ rsi + 0x20 ]
setc dl
clc
adcx rcx, [ rsp + 0x8 ]
mov r9, 0x2341f27177344 
xchg rdx, r9
mulx r11, r10, rcx
mov [ rsp + 0x218 ], rbp
mov byte [ rsp + 0x220 ], r13b
mulx r13, rbp, r8
adox rbp, [ rsp + 0x108 ]
mov r8, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp + 0x228 ], rbp
mulx rbp, rcx, r8
mov r8, rcx
mov [ rsp + 0x230 ], r11
setc r11b
clc
adcx r8, rbp
mov [ rsp + 0x238 ], r10
seto r10b
mov [ rsp + 0x240 ], rdi
movzx rdi, byte [ rsp + 0x210 ]
mov [ rsp + 0x248 ], rbx
mov rbx, 0x0 
dec rbx
adox rdi, rbx
adox r15, [ rsp - 0x30 ]
seto dil
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r14, [ rsp + 0x138 ]
adox r12, [ rsp + 0x168 ]
mov r11, rcx
seto bl
mov [ rsp + 0x250 ], r15
mov r15, -0x2 
inc r15
adox r11, rdx
adox r8, r14
movzx r11, r10b
lea r11, [ r11 + r13 ]
mov r13, 0xfdc1767ae2ffffff 
mulx r14, r10, r13
adcx rcx, rbp
setc r15b
clc
adcx r8, [ rsp + 0x110 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r8
mov byte [ rsp + 0x258 ], dil
mov [ rsp + 0x260 ], r11
mulx r11, rdi, r13
mov r13, rdi
mov [ rsp + 0x268 ], rcx
setc cl
clc
adcx r13, rdx
seto r13b
mov byte [ rsp + 0x270 ], cl
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox rbp, r10
mov r10, 0x7bc65c783158aea3 
xchg rdx, r10
mulx rcx, r15, r8
adox r15, r14
mov r14, 0x6cfc5fd681c52056 
mov rdx, r8
mov [ rsp + 0x278 ], r15
mulx r15, r8, r14
adox r8, rcx
mov rdx, [ rsp + 0x200 ]
seto cl
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r9, r9b
adox r9, r14
adox rdx, [ rsp + 0x248 ]
mov r9, [ rsp + 0x240 ]
seto r14b
mov [ rsp + 0x280 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox r9, [ rsp + 0x180 ]
adox rdx, [ rsp + 0x1a8 ]
setc bl
clc
movzx rcx, cl
adcx rcx, r8
adcx r15, [ rsp + 0x238 ]
mov rcx, rdi
setc r8b
clc
adcx rcx, r11
adcx rdi, r11
mov [ rsp + 0x288 ], r15
seto r15b
mov byte [ rsp + 0x290 ], r14b
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r13, r13b
adox r13, r14
adox r12, [ rsp + 0x268 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r13
mov byte [ rsp + 0x298 ], r15b
mulx r15, r14, r10
adox rbp, r9
seto r9b
movzx rdx, byte [ rsp + 0x270 ]
mov [ rsp + 0x2a0 ], r15
mov r15, 0x0 
dec r15
adox rdx, r15
adox r12, [ rsp + 0x130 ]
movzx rdx, r8b
mov r15, [ rsp + 0x230 ]
lea rdx, [ rdx + r15 ]
adcx r14, r11
setc r15b
clc
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r12, rcx
adox rbp, [ rsp + 0x128 ]
adcx rdi, rbp
setc bl
clc
movzx r9, r9b
adcx r9, r11
adcx r13, [ rsp + 0x278 ]
adox r13, [ rsp + 0x198 ]
setc r8b
clc
adcx r12, [ rsp + 0x18 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mulx rbp, r9, r12
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mov [ rsp + 0x2a8 ], rcx
mulx rcx, r11, r12
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2b0 ], rcx
mov byte [ rsp + 0x2b8 ], r15b
mulx r15, rcx, r12
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2c0 ], r15
mov [ rsp + 0x2c8 ], rcx
mulx rcx, r15, [ rsi + 0x10 ]
seto dl
mov byte [ rsp + 0x2d0 ], r8b
movzx r8, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x2d8 ], r14
mov r14, 0x0 
dec r14
adox r8, r14
adox r15, [ rsp - 0x38 ]
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2e0 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, r9
mov byte [ rsp + 0x2e8 ], r8b
setc r8b
clc
adcx rdx, rbp
adox rcx, [ rsp - 0x40 ]
mov [ rsp + 0x2f0 ], rcx
setc cl
clc
mov [ rsp + 0x2f8 ], r15
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx rdi, [ rsp + 0x1b8 ]
mov r8, r9
setc r15b
clc
adcx r8, r12
mov r8, rbp
mov [ rsp + 0x300 ], r14
seto r14b
mov byte [ rsp + 0x308 ], r15b
mov r15, 0x0 
dec r15
movzx rcx, cl
adox rcx, r15
adox r8, r9
adcx rdx, rdi
adox r11, rbp
movzx r9, r14b
mov rbp, [ rsp - 0x48 ]
lea r9, [ r9 + rbp ]
seto bpl
inc r15
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox r13, [ rsp + 0x2d8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mulx rdi, r14, [ rax + 0x8 ]
seto dl
movzx r15, byte [ rsp + 0x308 ]
inc rcx
mov rcx, -0x1 
adox r15, rcx
adox r13, [ rsp + 0x1f0 ]
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x310 ], bpl
mulx rbp, rcx, [ rax + 0x0 ]
setc dl
clc
adcx rcx, rbx
movzx rbx, byte [ rsp + 0x1e8 ]
mov [ rsp + 0x318 ], r11
mov r11, [ rsp + 0x1d0 ]
lea rbx, [ rbx + r11 ]
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x320 ], r8
mov [ rsp + 0x328 ], r13
mulx r13, r8, r11
mov r11, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x330 ], cl
mov byte [ rsp + 0x338 ], r15b
mulx r15, rcx, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x340 ], r15
mov [ rsp + 0x348 ], rcx
mulx rcx, r15, r11
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x350 ], rcx
mov [ rsp + 0x358 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x360 ], r13
mov r13, -0x2 
inc r13
adox r14, rbp
adox rcx, rdi
adox r15, [ rsp + 0xc0 ]
mov rdi, [ rsp + 0x188 ]
setc bpl
movzx r13, byte [ rsp + 0x1c8 ]
clc
mov [ rsp + 0x368 ], r15
mov r15, -0x1 
adcx r13, r15
adcx rdi, [ rsp + 0x300 ]
mov r13, [ rsp + 0x2f8 ]
adcx r13, [ rsp + 0xb0 ]
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x370 ], rcx
mov [ rsp + 0x378 ], r14
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x380 ], bpl
mov [ rsp + 0x388 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
adcx rbp, [ rsp + 0xa8 ]
mov rdx, 0x0 
adcx r14, rdx
adox rcx, [ rsp + 0xb8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x390 ], rcx
mov [ rsp + 0x398 ], r14
mulx r14, rcx, r11
movzx rdx, byte [ rsp + 0x208 ]
clc
mov [ rsp + 0x3a0 ], rbp
mov rbp, -0x1 
mov byte [ rsp + 0x3a8 ], r15b
movzx r15, byte [ rsp + 0x220 ]
adcx rdx, rbp
adcx rbx, r15
mov r15, rcx
seto dl
inc rbp
adox r15, r11
mov r15, [ rsp + 0x1f8 ]
setc bpl
mov byte [ rsp + 0x3b0 ], dl
movzx rdx, byte [ rsp + 0x290 ]
clc
mov [ rsp + 0x3b8 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx r15, [ rsp + 0x228 ]
adcx rbx, [ rsp + 0x260 ]
mov rdx, rcx
setc r13b
clc
adcx rdx, r14
mov [ rsp + 0x3c0 ], rdx
movzx rdx, r13b
movzx rbp, bpl
lea rdx, [ rdx + rbp ]
seto bpl
movzx r13, byte [ rsp + 0x298 ]
mov [ rsp + 0x3c8 ], rdi
mov rdi, 0x0 
dec rdi
adox r13, rdi
adox r15, [ rsp + 0x2e0 ]
adox rbx, [ rsp + 0x2f0 ]
adcx rcx, r14
setc r13b
movzx rdi, byte [ rsp + 0x2d0 ]
clc
mov [ rsp + 0x3d0 ], rcx
mov rcx, -0x1 
adcx rdi, rcx
adcx r15, [ rsp + 0x280 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, r10
mov byte [ rsp + 0x3d8 ], bpl
mulx rbp, rcx, rdi
mov rdi, 0x7bc65c783158aea3 
mov [ rsp + 0x3e0 ], r15
mov [ rsp + 0x3e8 ], rbp
mulx rbp, r15, rdi
seto dil
mov [ rsp + 0x3f0 ], rbx
movzx rbx, byte [ rsp + 0x2b8 ]
mov [ rsp + 0x3f8 ], r8
mov r8, 0x0 
dec r8
adox rbx, r8
adox r15, [ rsp + 0x2a0 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r8
adcx r10, r9
adox rcx, rbp
mov r9, 0x2341f27177344 
mulx rbp, rdi, r9
seto dl
inc r8
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox r14, [ rsp + 0x3f8 ]
mov r13, [ rsp + 0x3f0 ]
setc r8b
clc
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx r13, [ rsp + 0x288 ]
seto bl
inc r9
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox rdi, [ rsp + 0x3e8 ]
mov rdx, [ rsp + 0x358 ]
setc r9b
clc
mov [ rsp + 0x400 ], r14
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx rdx, [ rsp + 0x360 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x408 ], r8b
mulx r8, r14, [ rax + 0x30 ]
mov rdx, [ rsp + 0x3e0 ]
mov [ rsp + 0x410 ], rbx
setc bl
mov [ rsp + 0x418 ], r8
movzx r8, byte [ rsp + 0x2e8 ]
clc
mov [ rsp + 0x420 ], rdi
mov rdi, -0x1 
adcx r8, rdi
adcx rdx, [ rsp + 0x3c8 ]
seto r8b
movzx rdi, byte [ rsp + 0x338 ]
mov byte [ rsp + 0x428 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rdi, rbx
adox rdx, r15
adcx r13, [ rsp + 0x3b8 ]
movzx rdi, r8b
lea rdi, [ rdi + rbp ]
adox rcx, r13
mov r15, 0x2341f27177344 
xchg rdx, r11
mulx r8, rbp, r15
setc dl
movzx r13, byte [ rsp + 0x3a8 ]
clc
adcx r13, rbx
adcx r11, [ rsp + 0x1e0 ]
mov r13, [ rsp + 0xf8 ]
seto bl
movzx r15, byte [ rsp + 0x258 ]
mov [ rsp + 0x430 ], r8
mov r8, 0x0 
dec r8
adox r15, r8
adox r13, [ rsp + 0x218 ]
adox r14, [ rsp + 0xf0 ]
adcx rcx, [ rsp + 0x250 ]
mov r15, [ rsp + 0x328 ]
seto r8b
mov [ rsp + 0x438 ], r14
movzx r14, byte [ rsp + 0x330 ]
mov [ rsp + 0x440 ], r13
mov r13, 0x0 
dec r13
adox r14, r13
adox r15, [ rsp + 0x320 ]
seto r14b
inc r13
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox r10, [ rsp + 0x2a8 ]
setc r9b
clc
movzx rdx, dl
adcx rdx, r13
adcx r10, [ rsp + 0x3a0 ]
setc dl
clc
movzx rbx, bl
adcx rbx, r13
adcx r10, [ rsp + 0x420 ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, rbx
mov [ rsp + 0x448 ], r15
mulx r15, r13, r12
movzx rdx, r8b
mov [ rsp + 0x450 ], r10
mov r10, [ rsp + 0x418 ]
lea rdx, [ rdx + r10 ]
mov r10, 0x2341f27177344 
xchg rdx, r10
mov [ rsp + 0x458 ], r10
mulx r10, r8, r12
mov r12, [ rsp + 0x350 ]
seto dl
mov byte [ rsp + 0x460 ], r9b
movzx r9, byte [ rsp + 0x428 ]
mov [ rsp + 0x468 ], rdi
mov rdi, 0x0 
dec rdi
adox r9, rdi
adox r12, [ rsp + 0x348 ]
adox rbp, [ rsp + 0x340 ]
setc r9b
clc
movzx r14, r14b
adcx r14, rdi
adcx r11, [ rsp + 0x318 ]
seto r14b
movzx rdi, byte [ rsp + 0x310 ]
mov [ rsp + 0x470 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox rdi, rbp
adox r13, [ rsp + 0x2b0 ]
adox r15, [ rsp + 0x2c8 ]
adcx r13, rcx
adox r8, [ rsp + 0x2c0 ]
movzx rdi, dl
movzx rcx, byte [ rsp + 0x408 ]
lea rdi, [ rdi + rcx ]
mov rcx, 0x0 
adox r10, rcx
inc rbp
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox rdi, [ rsp + 0x398 ]
seto dl
inc rcx
mov rbp, -0x1 
movzx r9, r9b
adox r9, rbp
adox rdi, [ rsp + 0x468 ]
movzx rbx, dl
adox rbx, rcx
mov r9, [ rsp + 0x450 ]
movzx rdx, byte [ rsp + 0x460 ]
dec rcx
adox rdx, rcx
adox r9, [ rsp + 0x440 ]
adcx r15, r9
adox rdi, [ rsp + 0x438 ]
adcx r8, rdi
adox rbx, [ rsp + 0x458 ]
adcx r10, rbx
mov rbp, [ rsp + 0x70 ]
seto dl
movzx r9, byte [ rsp + 0x3b0 ]
inc rcx
mov rdi, -0x1 
adox r9, rdi
adox rbp, [ rsp + 0x388 ]
mov r9, [ rsp + 0x68 ]
adox r9, [ rsp + 0x0 ]
mov bl, dl
mov rdx, [ rsi + 0x30 ]
mulx rdi, rcx, [ rax + 0x0 ]
movzx rdx, bl
mov byte [ rsp + 0x478 ], r14b
mov r14, 0x0 
adcx rdx, r14
mov rbx, [ rsp + 0x378 ]
movzx r14, byte [ rsp + 0x380 ]
clc
mov [ rsp + 0x480 ], rdx
mov rdx, -0x1 
adcx r14, rdx
adcx rbx, [ rsp + 0x448 ]
adcx r11, [ rsp + 0x370 ]
adcx r13, [ rsp + 0x368 ]
setc r14b
clc
adcx rdi, [ rsp + 0xe8 ]
mov rdx, [ rsp - 0x8 ]
mov [ rsp + 0x488 ], rdi
mov rdi, 0x0 
adox rdx, rdi
movzx rdi, byte [ rsp + 0x3d8 ]
mov [ rsp + 0x490 ], rdx
mov rdx, 0x0 
dec rdx
adox rdi, rdx
adox rbx, [ rsp + 0x3c0 ]
adox r11, [ rsp + 0x3d0 ]
adox r13, [ rsp + 0x400 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x498 ], r13
mulx r13, rdi, [ rax + 0x30 ]
setc dl
clc
adcx rcx, rbx
setc bl
clc
mov [ rsp + 0x4a0 ], r13
mov r13, -0x1 
movzx r14, r14b
adcx r14, r13
adcx r15, [ rsp + 0x390 ]
adcx rbp, r8
adox r15, [ rsp + 0x410 ]
mov r8, 0x2341f27177344 
xchg rdx, rcx
mulx r13, r14, r8
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x4a8 ], r13
mov [ rsp + 0x4b0 ], r14
mulx r14, r13, r8
adox r12, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x4b8 ], r12
mulx r12, r8, [ rax + 0x20 ]
adcx r9, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x4c0 ], r9
mulx r9, r10, [ rax + 0x10 ]
setc dl
clc
mov [ rsp + 0x4c8 ], rdi
mov rdi, -0x1 
movzx rcx, cl
adcx rcx, rdi
adcx r10, [ rsp + 0xe0 ]
seto cl
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r11, [ rsp + 0x488 ]
adcx r9, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
adox r10, [ rsp + 0x498 ]
adox r9, r15
adcx r12, [ rsp + 0x178 ]
mov rbx, r13
seto r15b
inc rdi
adox rbx, r14
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov [ rsp + 0x4d0 ], r12
mov [ rsp + 0x4d8 ], r8
mulx r8, r12, rdi
mov rdi, r13
adox rdi, r14
adox r12, r14
seto r14b
mov byte [ rsp + 0x4e0 ], r15b
mov r15, -0x2 
inc r15
adox r13, rdx
adox rbx, r11
mov r13, [ rsp + 0x170 ]
adcx r13, [ rsp + 0x4c8 ]
adox rdi, r10
adox r12, r9
mov r11, 0x6cfc5fd681c52056 
mulx r9, r10, r11
movzx r15, byte [ rsp + 0x478 ]
mov r11, [ rsp + 0x430 ]
lea r15, [ r15 + r11 ]
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x4e8 ], r12
mov [ rsp + 0x4f0 ], rdi
mulx rdi, r12, r11
mov rdx, [ rsp + 0x4c0 ]
setc r11b
clc
mov [ rsp + 0x4f8 ], rbx
mov rbx, -0x1 
movzx rcx, cl
adcx rcx, rbx
adcx rdx, [ rsp + 0x470 ]
seto cl
inc rbx
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox r8, r12
mov r14, [ rsp + 0x490 ]
seto r12b
inc rbx
mov rbx, -0x1 
movzx rbp, bpl
adox rbp, rbx
adox r14, [ rsp + 0x480 ]
setc bpl
clc
movzx r12, r12b
adcx r12, rbx
adcx rdi, r10
adcx r9, [ rsp + 0x4b0 ]
setc r10b
clc
movzx rbp, bpl
adcx rbp, rbx
adcx r14, r15
seto r15b
adc r15b, 0x0
movzx r15, r15b
mov rbp, [ rsp + 0x4b8 ]
add byte [ rsp + 0x4e0 ], 0x7F
adox rbp, [ rsp + 0x4d8 ]
adox rdx, [ rsp + 0x4d0 ]
adox r13, r14
movzx rcx, cl
adcx rcx, rbx
adcx rbp, r8
adcx rdi, rdx
setc cl
seto r8b
mov r12, [ rsp + 0x4f8 ]
mov r14, 0xffffffffffffffff 
sub r12, r14
movzx rdx, r11b
mov rbx, [ rsp + 0x4a0 ]
lea rdx, [ rdx + rbx ]
mov rbx, [ rsp + 0x4f0 ]
sbb rbx, r14
mov r11, [ rsp + 0x4e8 ]
sbb r11, r14
mov r14, rbp
mov [ rsp + 0x500 ], r12
mov r12, 0xfdc1767ae2ffffff 
sbb r14, r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox r13, r9
seto r9b
inc r12
mov rcx, -0x1 
movzx r15, r15b
movzx r8, r8b
adox r8, rcx
adox rdx, r15
movzx r15, r10b
mov r8, [ rsp + 0x4a8 ]
lea r15, [ r15 + r8 ]
setc r8b
clc
movzx r9, r9b
adcx r9, rcx
adcx rdx, r15
setc r10b
seto r9b
movzx r15, r8b
add r15, -0x1
mov r8, rdi
mov r15, 0x7bc65c783158aea3 
sbb r8, r15
movzx r12, r10b
movzx r9, r9b
lea r12, [ r12 + r9 ]
mov r9, r13
mov r10, 0x6cfc5fd681c52056 
sbb r9, r10
mov rcx, rdx
mov r10, 0x2341f27177344 
sbb rcx, r10
sbb r12, 0x00000000
cmovc rcx, rdx
cmovc r11, [ rsp + 0x4e8 ]
cmovc r8, rdi
cmovc r9, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x28 ], r9
mov [ r12 + 0x30 ], rcx
cmovc rbx, [ rsp + 0x4f0 ]
mov [ r12 + 0x8 ], rbx
mov rdi, [ rsp + 0x500 ]
cmovc rdi, [ rsp + 0x4f8 ]
mov [ r12 + 0x20 ], r8
mov [ r12 + 0x0 ], rdi
cmovc r14, rbp
mov [ r12 + 0x18 ], r14
mov [ r12 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1416
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1548
; seed 0286743768697920 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 18336755 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=21, initial num_batches=31): 328582 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.017919310150569173
; number reverted permutation / tried permutation: 66997 / 90088 =74.368%
; number reverted decision / tried decision: 55098 / 89911 =61.281%
; validated in 449.544s
