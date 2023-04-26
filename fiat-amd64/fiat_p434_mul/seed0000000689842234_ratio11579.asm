SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1472
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, rbp
test al, al
adox rdx, r12
mov [ rsp - 0x48 ], rdi
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rbx
mulx rbx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r9
mulx r9, r14, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r8
mulx r8, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r8
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rcx
mulx rcx, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rcx
mulx rcx, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], rbx
mulx rbx, rcx, [ rsi + 0x28 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], rcx
mulx rcx, rbx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], rbx
mulx rbx, rcx, [ rax + 0x0 ]
adcx r14, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r14
mulx r14, rbx, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x88 ], r14
mov [ rsp + 0x90 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r14
mulx r14, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], rbx
mulx rbx, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r14
mulx r14, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], rcx
mov [ rsp + 0xd0 ], r13
mulx r13, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], rcx
mulx rcx, r13, [ rax + 0x8 ]
adcx rbx, r8
setc dl
clc
adcx r13, r9
mov r9b, dl
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xe8 ], r13
mulx r13, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf0 ], rcx
mov [ rsp + 0xf8 ], r13
mulx r13, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], rcx
mov [ rsp + 0x108 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x110 ], rbx
mov rbx, -0x2 
inc rbx
adox r8, r13
setc r13b
clc
adcx r15, r11
mov r11, rbp
seto bl
mov [ rsp + 0x118 ], r8
mov r8, -0x2 
inc r8
adox r11, r10
adox rdi, r15
seto r11b
inc r8
mov r15, -0x1 
movzx r9, r9b
adox r9, r15
adox r14, [ rsp + 0xd0 ]
mov r9, [ rsp + 0x18 ]
adcx r9, [ rsp + 0x10 ]
mov r8, [ rsp - 0x18 ]
adcx r8, [ rsp - 0x28 ]
seto r15b
mov [ rsp + 0x120 ], r14
mov r14, -0x2 
inc r14
adox rdi, [ rsp + 0xc8 ]
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x128 ], r13b
mov byte [ rsp + 0x130 ], bl
mulx rbx, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x138 ], rbx
mov [ rsp + 0x140 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp + 0x148 ], rcx
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rbx, [ rsp - 0x30 ]
mov r15b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x150 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, r12
mov byte [ rsp + 0x158 ], r15b
seto r15b
mov [ rsp + 0x160 ], rbx
mov rbx, 0x0 
dec rbx
movzx r14, r14b
adox r14, rbx
adox rdx, rbp
adox r12, [ rsp + 0x78 ]
setc bpl
clc
movzx r11, r11b
adcx r11, rbx
adcx r9, rdx
adcx r12, r8
setc r14b
clc
movzx r15, r15b
adcx r15, rbx
adcx r9, [ rsp + 0x80 ]
mov rdx, [ rax + 0x0 ]
mulx r8, r11, [ rsi + 0x10 ]
adcx r12, [ rsp + 0x108 ]
mov rdx, 0xfdc1767ae2ffffff 
mulx rbx, r15, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], r15
mulx r15, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x178 ], r11
mov [ rsp + 0x180 ], r12
mulx r12, r11, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x188 ], r12
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox r13, rcx
adox r11, [ rsp + 0x160 ]
mov rbp, 0x2341f27177344 
xchg rdx, rbp
mulx r12, rcx, rdi
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x190 ], r11
mov [ rsp + 0x198 ], r12
mulx r12, r11, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x1a0 ], r11
mov r11, -0x2 
inc r11
adox rbx, r8
adox r15, [ rsp + 0x48 ]
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1a8 ], r15
mulx r15, r11, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x40 ]
adox rdx, [ rsp - 0x8 ]
adox r11, [ rsp - 0x10 ]
mov byte [ rsp + 0x1b0 ], r8b
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r11
mov [ rsp + 0x1c0 ], rcx
mulx rcx, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1c8 ], r8
mov [ rsp + 0x1d0 ], r13
mulx r13, r8, [ rsi + 0x10 ]
setc dl
clc
adcx r11, r12
adox r8, r15
adcx rcx, [ rsp + 0x148 ]
mov r12b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1d8 ], rcx
mulx rcx, r15, [ rax + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1e0 ], rcx
mov [ rsp + 0x1e8 ], r11
mulx r11, rcx, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1f0 ], r13
mov [ rsp + 0x1f8 ], r8
mulx r8, r13, [ rax + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x200 ], rbx
mov [ rsp + 0x208 ], r9
mulx r9, rbx, r10
seto r10b
movzx rdx, byte [ rsp + 0x130 ]
mov byte [ rsp + 0x210 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox rdx, r12
adox r13, [ rsp + 0xf8 ]
adox r8, [ rsp + 0x68 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x218 ], r8
mulx r8, r12, rdi
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x220 ], r13
mov byte [ rsp + 0x228 ], r10b
mulx r10, r13, [ rsi + 0x0 ]
mov rdx, r12
mov byte [ rsp + 0x230 ], r14b
setc r14b
clc
adcx rdx, r8
mov byte [ rsp + 0x238 ], r14b
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x240 ], r10
mov [ rsp + 0x248 ], r13
mulx r13, r10, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x250 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbp, bpl
adox rbp, r13
adox rcx, [ rsp + 0x70 ]
seto bpl
inc r13
mov r13, -0x1 
movzx rdx, dl
adox rdx, r13
adox r10, [ rsp + 0x60 ]
seto dl
movzx r13, byte [ rsp + 0x128 ]
mov [ rsp + 0x258 ], r10
mov r10, 0x0 
dec r10
adox r13, r10
adox r15, [ rsp + 0xf0 ]
mov r13, [ rsp - 0x38 ]
seto r10b
mov [ rsp + 0x260 ], r15
movzx r15, byte [ rsp + 0x158 ]
mov byte [ rsp + 0x268 ], dl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r15, rdx
adox r13, [ rsp + 0x38 ]
seto r15b
inc rdx
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox r11, rbx
adox r9, [ rsp - 0x40 ]
mov rbx, r12
adcx rbx, r8
mov rbp, [ rsp + 0x30 ]
setc dl
clc
mov byte [ rsp + 0x270 ], r10b
mov r10, -0x1 
movzx r15, r15b
adcx r15, r10
adcx rbp, [ rsp + 0x248 ]
mov r15b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x278 ], rbx
mulx rbx, r10, [ rax + 0x30 ]
adcx r10, [ rsp + 0x240 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0x280 ], rbx
mov rbx, 0x0 
adox rdx, rbx
movzx rbx, byte [ rsp + 0x230 ]
mov [ rsp + 0x288 ], rdx
mov rdx, 0x0 
dec rdx
adox rbx, rdx
adox r13, rcx
setc bl
movzx rcx, byte [ rsp + 0x210 ]
clc
adcx rcx, rdx
adcx r13, [ rsp + 0x120 ]
adox r11, rbp
mov rdx, [ rsi + 0x28 ]
mulx rbp, rcx, [ rax + 0x28 ]
adcx r11, [ rsp + 0x150 ]
adox r9, r10
setc dl
clc
adcx r12, rdi
adcx r14, [ rsp + 0x208 ]
mov r12, [ rsp + 0x180 ]
adcx r12, [ rsp + 0x278 ]
seto r10b
mov [ rsp + 0x290 ], rbp
movzx rbp, byte [ rsp + 0x268 ]
mov byte [ rsp + 0x298 ], bl
mov rbx, 0x0 
dec rbx
adox rbp, rbx
adox rcx, [ rsp + 0x250 ]
seto bpl
inc rbx
adox r14, [ rsp + 0x178 ]
adox r12, [ rsp + 0x200 ]
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x2a0 ], rcx
mov byte [ rsp + 0x2a8 ], bpl
mulx rbp, rcx, r14
seto dl
mov [ rsp + 0x2b0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r15, r15b
adox r15, r12
adox r8, [ rsp + 0x170 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x2b8 ], rbp
mulx rbp, r12, rdi
adox r12, [ rsp + 0x168 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2c0 ], rcx
mov byte [ rsp + 0x2c8 ], r10b
mulx r10, rcx, r14
adcx r8, r13
mov [ rsp + 0x2d0 ], r10
mulx r10, r13, rdi
mov rdi, 0x2341f27177344 
mov rdx, rdi
mov [ rsp + 0x2d8 ], rcx
mulx rcx, rdi, r14
adox r13, rbp
adcx r12, r11
seto r11b
mov rbp, 0x0 
dec rbp
movzx rbx, bl
adox rbx, rbp
adox r9, [ rsp + 0x1d0 ]
seto bl
inc rbp
mov rbp, -0x1 
movzx r11, r11b
adox r11, rbp
adox r10, [ rsp + 0x1c0 ]
adcx r13, r9
mov r11, [ rsp + 0x198 ]
mov r9, 0x0 
adox r11, r9
movzx r9, byte [ rsp + 0x298 ]
mov rbp, [ rsp + 0x280 ]
lea r9, [ r9 + rbp ]
mov rbp, 0x0 
dec rbp
movzx r15, r15b
adox r15, rbp
adox r8, [ rsp + 0x1a8 ]
adox r12, [ rsp + 0x1c8 ]
mov rdx, [ rax + 0x30 ]
mulx rbp, r15, [ rsi + 0x10 ]
adox r13, [ rsp + 0x1b8 ]
movzx rdx, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x2e0 ], rcx
mov rcx, [ rsp + 0x188 ]
lea rdx, [ rdx + rcx ]
mov rcx, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0x2e8 ], rdi
mov [ rsp + 0x2f0 ], r11
mulx r11, rdi, rcx
seto cl
mov [ rsp + 0x2f8 ], r13
movzx r13, byte [ rsp + 0x2c8 ]
mov [ rsp + 0x300 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r13, r12
adox r9, [ rsp + 0x288 ]
mov r13, rdi
setc r12b
clc
adcx r13, r11
mov [ rsp + 0x308 ], rbp
seto bpl
mov [ rsp + 0x310 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox r9, [ rsp + 0x190 ]
mov rbx, rdi
adcx rbx, r11
movzx r8, bpl
adox r8, r14
adcx r11, [ rsp + 0x2c0 ]
mov r14, 0x7bc65c783158aea3 
mov [ rsp + 0x318 ], r8
mulx r8, rbp, r14
adcx rbp, [ rsp + 0x2b8 ]
seto r14b
mov [ rsp + 0x320 ], r8
mov r8, 0x0 
dec r8
movzx r12, r12b
adox r12, r8
adox r9, r10
setc r10b
clc
adcx rdi, rdx
adcx r13, [ rsp + 0x2b0 ]
setc dil
clc
movzx rcx, cl
adcx rcx, r8
adcx r9, [ rsp + 0x1f8 ]
setc dl
movzx r12, byte [ rsp + 0x228 ]
clc
adcx r12, r8
adcx r15, [ rsp + 0x1f0 ]
seto r12b
inc r8
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox rbx, [ rsp + 0x310 ]
mov rdi, [ rsp + 0x308 ]
adcx rdi, r8
adox r11, [ rsp + 0x300 ]
clc
adcx r13, [ rsp + 0x1a0 ]
adcx rbx, [ rsp + 0x1e8 ]
mov r8, 0x7bc65c783158aea3 
xchg rdx, r13
mov [ rsp + 0x328 ], rdi
mulx rdi, rcx, r8
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x330 ], rdi
mov [ rsp + 0x338 ], rcx
mulx rcx, rdi, [ rsi + 0x20 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x340 ], r15
mov byte [ rsp + 0x348 ], r13b
mulx r13, r15, r8
adcx r11, [ rsp + 0x1d8 ]
mov rdx, [ rsp + 0x8 ]
mov [ rsp + 0x350 ], r13
setc r13b
mov [ rsp + 0x358 ], r15
movzx r15, byte [ rsp + 0x238 ]
clc
mov [ rsp + 0x360 ], r11
mov r11, -0x1 
adcx r15, r11
adcx rdx, [ rsp + 0x110 ]
adox rbp, [ rsp + 0x2f8 ]
seto r15b
inc r11
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rbp, rdx
mov r13, [ rsp + 0x0 ]
adcx r13, [ rsp + 0xa0 ]
mov rdx, [ rsp + 0x320 ]
seto r11b
mov [ rsp + 0x368 ], rbp
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox rdx, [ rsp + 0x2d8 ]
setc r10b
clc
movzx r15, r15b
adcx r15, rbp
adcx r9, rdx
mov r15, [ rsp + 0x98 ]
setc dl
clc
movzx r10, r10b
adcx r10, rbp
adcx r15, [ rsp + 0x90 ]
mov r10, [ rsp + 0x318 ]
setc bpl
clc
mov [ rsp + 0x370 ], r15
mov r15, -0x1 
movzx r12, r12b
adcx r12, r15
adcx r10, [ rsp + 0x2f0 ]
movzx r12, r14b
mov r15, 0x0 
adcx r12, r15
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mov byte [ rsp + 0x378 ], bpl
mulx rbp, r15, r8
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x380 ], r14b
mov [ rsp + 0x388 ], r12
mulx r12, r14, [ rsi + 0x20 ]
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r9, r13
mov r11, r15
setc r13b
clc
adcx r11, rbp
mov rdx, r15
mov [ rsp + 0x390 ], r9
seto r9b
mov byte [ rsp + 0x398 ], r13b
mov r13, -0x2 
inc r13
adox rdx, r8
adox r11, rbx
seto dl
inc r13
adox rdi, r11
adcx r15, rbp
setc bl
clc
adcx r14, rcx
setc cl
clc
mov r11, -0x1 
movzx rdx, dl
adcx rdx, r11
adcx r15, [ rsp + 0x360 ]
mov rdx, [ rsp + 0x2d0 ]
setc r13b
clc
movzx r9, r9b
adcx r9, r11
adcx rdx, [ rsp + 0x2e8 ]
mov r9, [ rsp + 0x2e0 ]
mov r11, 0x0 
adcx r9, r11
movzx r11, byte [ rsp + 0x348 ]
clc
mov [ rsp + 0x3a0 ], r14
mov r14, -0x1 
adcx r11, r14
adcx r10, [ rsp + 0x340 ]
mov r11, [ rsp + 0x388 ]
adcx r11, [ rsp + 0x328 ]
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x3a8 ], r15
mov byte [ rsp + 0x3b0 ], r13b
mulx r13, r15, r14
xchg rdx, rdi
mov [ rsp + 0x3b8 ], r13
mov [ rsp + 0x3c0 ], r15
mulx r15, r13, r14
mov r14, 0x7bc65c783158aea3 
mov [ rsp + 0x3c8 ], r15
mov [ rsp + 0x3d0 ], r13
mulx r13, r15, r14
mov r14, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x3d8 ], r13
mov [ rsp + 0x3e0 ], r15
mulx r15, r13, [ rsi + 0x20 ]
seto dl
mov byte [ rsp + 0x3e8 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx rcx, cl
adox rcx, rbx
adox r12, [ rsp + 0xe0 ]
adox r13, [ rsp + 0xd8 ]
adox r15, [ rsp + 0x28 ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x3f0 ], r15
mulx r15, rbx, rdi
seto dil
movzx rdx, byte [ rsp + 0x380 ]
mov [ rsp + 0x3f8 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox r10, r8
adox r9, r11
seto dl
movzx r8, byte [ rsp + 0x3e8 ]
inc r13
mov r11, -0x1 
adox r8, r11
adox rbp, rbx
movzx r8, dl
adcx r8, r13
adox r15, [ rsp + 0x338 ]
mov rbx, [ rsp + 0x330 ]
adox rbx, [ rsp + 0x3c0 ]
mov rdx, [ rax + 0x30 ]
mulx r11, r13, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x3b8 ]
adox rdx, [ rsp + 0x358 ]
mov [ rsp + 0x400 ], r8
mov r8, [ rsp + 0xb0 ]
clc
mov [ rsp + 0x408 ], rdx
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx r8, [ rsp + 0x20 ]
seto dil
movzx rdx, byte [ rsp + 0x398 ]
mov [ rsp + 0x410 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox rdx, r8
adox r10, [ rsp + 0x370 ]
adcx r13, [ rsp + 0xa8 ]
seto dl
movzx r8, byte [ rsp + 0x3b0 ]
mov [ rsp + 0x418 ], r13
mov r13, 0x0 
dec r13
adox r8, r13
adox rbp, [ rsp + 0x368 ]
adox r15, [ rsp + 0x390 ]
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mov byte [ rsp + 0x420 ], dil
mulx rdi, r13, r14
mov rdx, 0x0 
adcx r11, rdx
adox rbx, r10
mov r10, [ rsp + 0x3a8 ]
clc
mov rdx, -0x1 
movzx rcx, cl
adcx rcx, rdx
adcx r10, [ rsp + 0x3a0 ]
adcx r12, rbp
mov rdx, [ rax + 0x30 ]
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, r13
mov [ rsp + 0x428 ], r11
seto r11b
mov [ rsp + 0x430 ], rbp
mov rbp, -0x2 
inc rbp
adox rdx, rdi
adcx r15, [ rsp + 0x3f8 ]
mov rbp, r13
adox rbp, rdi
mov [ rsp + 0x438 ], rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov byte [ rsp + 0x440 ], r11b
mov [ rsp + 0x448 ], r15
mulx r15, r11, r14
adox r11, rdi
setc dil
movzx rdx, byte [ rsp + 0x378 ]
clc
mov [ rsp + 0x450 ], r15
mov r15, -0x1 
adcx rdx, r15
adcx rcx, [ rsp + 0x88 ]
setc dl
clc
movzx r8, r8b
adcx r8, r15
adcx r9, rcx
setc r8b
clc
adcx r13, r14
adcx rbx, r10
adcx rbp, r12
setc r13b
clc
adcx rbx, [ rsp + 0x100 ]
seto r10b
inc r15
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox r11, [ rsp + 0x448 ]
setc cl
movzx r13, byte [ rsp + 0x440 ]
clc
adcx r13, r12
adcx r9, [ rsp + 0x408 ]
mov r13, [ rsp + 0x438 ]
setc r15b
clc
movzx rdi, dil
adcx rdi, r12
adcx r13, [ rsp + 0x3f0 ]
adcx r9, [ rsp + 0x410 ]
mov rdi, 0x2341f27177344 
xchg rdx, rdi
mov [ rsp + 0x458 ], r9
mulx r9, r12, r14
setc r14b
clc
mov rdx, -0x1 
movzx rcx, cl
adcx rcx, rdx
adcx rbp, [ rsp + 0x118 ]
mov rcx, [ rsp + 0x3e0 ]
seto dl
mov byte [ rsp + 0x460 ], r14b
mov r14, 0x0 
dec r14
movzx r10, r10b
adox r10, r14
adox rcx, [ rsp + 0x450 ]
adcx r11, [ rsp + 0x220 ]
mov r10, [ rsp + 0x3d8 ]
adox r10, [ rsp + 0x3d0 ]
adox r12, [ rsp + 0x3c8 ]
setc r14b
clc
mov [ rsp + 0x468 ], r12
mov r12, -0x1 
movzx rdx, dl
adcx rdx, r12
adcx r13, rcx
movzx rdx, dil
mov rcx, [ rsp + 0x430 ]
lea rdx, [ rdx + rcx ]
movzx rcx, byte [ rsp + 0x420 ]
mov rdi, [ rsp + 0x350 ]
lea rcx, [ rcx + rdi ]
setc dil
clc
movzx r8, r8b
adcx r8, r12
adcx rdx, [ rsp + 0x400 ]
setc r8b
clc
movzx r15, r15b
adcx r15, r12
adcx rdx, rcx
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mulx r12, rcx, [ rsi + 0x30 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x470 ], r12
mov [ rsp + 0x478 ], rcx
mulx rcx, r12, rbx
mov rdx, r12
mov [ rsp + 0x480 ], r9
mov r9, -0x2 
inc r9
adox rdx, rcx
movzx r9, r8b
mov [ rsp + 0x488 ], r10
mov r10, 0x0 
adcx r9, r10
mov r8, r12
clc
adcx r8, rbx
adcx rdx, rbp
adox r12, rcx
adcx r12, r11
mov r8, [ rsp + 0x290 ]
seto bpl
movzx r11, byte [ rsp + 0x2a8 ]
dec r10
adox r11, r10
adox r8, [ rsp + 0x140 ]
seto r11b
movzx r10, byte [ rsp + 0x460 ]
mov [ rsp + 0x490 ], r8
mov r8, 0x0 
dec r8
adox r10, r8
adox r15, [ rsp + 0x418 ]
movzx r10, r11b
mov r8, [ rsp + 0x138 ]
lea r10, [ r10 + r8 ]
adox r9, [ rsp + 0x428 ]
mov r8, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x498 ], r10
mulx r10, r11, r8
seto r8b
mov [ rsp + 0x4a0 ], r9
mov r9, -0x2 
inc r9
adox rbx, [ rsp - 0x20 ]
setc r9b
clc
mov byte [ rsp + 0x4a8 ], r8b
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx r13, [ rsp + 0x218 ]
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x4b0 ], r13
mulx r13, r8, r14
xchg rdx, r14
mov byte [ rsp + 0x4b8 ], r9b
mov [ rsp + 0x4c0 ], r15
mulx r15, r9, rbx
adox r12, [ rsp + 0xe8 ]
mov rdx, [ rsp + 0x488 ]
mov [ rsp + 0x4c8 ], r15
seto r15b
mov [ rsp + 0x4d0 ], r9
mov r9, 0x0 
dec r9
movzx rdi, dil
adox rdi, r9
adox rdx, [ rsp + 0x458 ]
adcx rdx, [ rsp + 0x258 ]
setc dil
clc
movzx rbp, bpl
adcx rbp, r9
adcx rcx, r11
mov rbp, 0x7bc65c783158aea3 
xchg rdx, rbp
mulx r9, r11, r14
adcx r11, r10
adcx r8, r9
mov r10, 0x2341f27177344 
mov rdx, r14
mulx r9, r14, r10
adcx r14, r13
mov rdx, [ rsp + 0x468 ]
adox rdx, [ rsp + 0x4c0 ]
mov r13, 0x0 
adcx r9, r13
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x4d8 ], r12
mulx r12, r10, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x4a0 ]
adox rdx, [ rsp + 0x480 ]
clc
mov byte [ rsp + 0x4e0 ], r15b
mov r15, -0x1 
movzx rdi, dil
adcx rdi, r15
adcx r13, [ rsp + 0x2a0 ]
movzx rdi, byte [ rsp + 0x4a8 ]
mov r15, 0x0 
adox rdi, r15
adcx rdx, [ rsp + 0x490 ]
movzx r15, byte [ rsp + 0x4b8 ]
mov [ rsp + 0x4e8 ], r9
mov r9, 0x0 
dec r9
adox r15, r9
adox rcx, [ rsp + 0x4b0 ]
adox r11, rbp
adox r8, r13
mov r15, [ rsp + 0x1e0 ]
setc bpl
movzx r13, byte [ rsp + 0x270 ]
clc
adcx r13, r9
adcx r15, [ rsp + 0xc0 ]
mov r13, [ rsp + 0xb8 ]
adcx r13, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x50 ]
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mov [ rsp + 0x4f0 ], r10
mov [ rsp + 0x4f8 ], r13
mulx r13, r10, rbx
adcx r12, [ rsp + 0x478 ]
setc dl
clc
mov [ rsp + 0x500 ], r12
mov r12, -0x1 
movzx rbp, bpl
adcx rbp, r12
adcx rdi, [ rsp + 0x498 ]
adox r14, r9
adox rdi, [ rsp + 0x4e8 ]
seto bpl
adc bpl, 0x0
movzx rbp, bpl
add byte [ rsp + 0x4e0 ], 0x7F
adox rcx, [ rsp + 0x260 ]
adox r15, r11
adox r8, [ rsp + 0x4f8 ]
adox r14, [ rsp + 0x4f0 ]
mov r9, r10
adcx r9, r13
mov r11, 0x7bc65c783158aea3 
xchg rdx, r11
mov byte [ rsp + 0x508 ], bpl
mulx rbp, r12, rbx
mov rdx, r10
adcx rdx, r13
mov byte [ rsp + 0x510 ], r11b
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r11
mov [ rsp + 0x518 ], r14
mov [ rsp + 0x520 ], rdi
mulx rdi, r14, rbx
adcx r14, r13
adcx r12, rdi
seto r13b
mov rdi, -0x2 
inc rdi
adox r10, rbx
adox r9, [ rsp + 0x4d8 ]
adox r11, rcx
adcx rbp, [ rsp + 0x4d0 ]
mov r10, 0x2341f27177344 
mov rdx, r10
mulx rcx, r10, rbx
adcx r10, [ rsp + 0x4c8 ]
adox r14, r15
adox r12, r8
mov rbx, 0x0 
adcx rcx, rbx
mov r15, [ rsp + 0x500 ]
clc
movzx r13, r13b
adcx r13, rdi
adcx r15, [ rsp + 0x520 ]
adox rbp, [ rsp + 0x518 ]
adox r10, r15
movzx r8, byte [ rsp + 0x510 ]
mov r13, [ rsp + 0x470 ]
lea r8, [ r8 + r13 ]
movzx r13, byte [ rsp + 0x508 ]
adcx r13, r8
adox rcx, r13
setc r15b
seto r8b
mov r13, r9
mov rdi, 0xffffffffffffffff 
sub r13, rdi
mov rbx, r11
sbb rbx, rdi
movzx rdi, r8b
movzx r15, r15b
lea rdi, [ rdi + r15 ]
mov r15, r14
mov r8, 0xffffffffffffffff 
sbb r15, r8
mov r8, r12
mov rdx, 0xfdc1767ae2ffffff 
sbb r8, rdx
mov rdx, rbp
mov [ rsp + 0x528 ], r8
mov r8, 0x7bc65c783158aea3 
sbb rdx, r8
mov r8, r10
mov [ rsp + 0x530 ], r15
mov r15, 0x6cfc5fd681c52056 
sbb r8, r15
mov r15, rcx
mov [ rsp + 0x538 ], rdx
mov rdx, 0x2341f27177344 
sbb r15, rdx
sbb rdi, 0x00000000
cmovc rbx, r11
cmovc r8, r10
cmovc r13, r9
mov rdi, [ rsp + 0x538 ]
cmovc rdi, rbp
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r13
mov [ r9 + 0x8 ], rbx
mov r11, [ rsp + 0x530 ]
cmovc r11, r14
mov [ r9 + 0x10 ], r11
mov r14, [ rsp + 0x528 ]
cmovc r14, r12
mov [ r9 + 0x18 ], r14
cmovc r15, rcx
mov [ r9 + 0x30 ], r15
mov [ r9 + 0x28 ], r8
mov [ r9 + 0x20 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1472
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1579
; seed 2479698403212129 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 17766443 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=21, initial num_batches=31): 307946 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01733301370454401
; number reverted permutation / tried permutation: 71622 / 89917 =79.653%
; number reverted decision / tried decision: 61782 / 90082 =68.584%
; validated in 449.032s
