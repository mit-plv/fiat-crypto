SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1888
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rax + 0x0 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rbx
mulx rbx, r9, rdi
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r13
mulx r13, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], r13
mulx r13, r8, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r8
mulx r8, r13, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r14
mulx r14, rcx, [ rax + 0x18 ]
mov rdx, r13
mov [ rsp + 0x48 ], r14
xor r14, r14
adox rdx, rdi
mov rdx, 0x2341f27177344 
mov [ rsp + 0x50 ], rcx
mulx rcx, r14, rdi
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x58 ], rcx
mov [ rsp + 0x60 ], r14
mulx r14, rcx, rdi
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x68 ], rbx
mov [ rsp + 0x70 ], r11
mulx r11, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], r11
mov [ rsp + 0x80 ], rbx
mulx rbx, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], r11
mulx r11, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], rbx
mulx rbx, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], r11
mulx r11, rbx, [ rsi + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], rbx
mulx rbx, r11, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r9
mulx r9, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], r11
mulx r11, rbx, [ rsi + 0x28 ]
mov rdx, r13
adcx rdx, r8
mov [ rsp + 0xe0 ], r11
mov r11, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r14
mulx r14, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xf8 ], r14
mov [ rsp + 0x100 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], r14
mulx r14, rbx, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x118 ], r14
mov [ rsp + 0x120 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x128 ], rbx
mov rbx, -0x2 
inc rbx
adox rbp, r15
adcx r13, r8
adcx rcx, r8
adox rdi, r12
adox r10, r9
seto r12b
inc rbx
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox rbp, r11
mov r8, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0xf0 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x20 ]
mov rdx, [ rsp + 0xd0 ]
adcx rdx, [ rsp + 0xc8 ]
setc bl
clc
movzx r12, r12b
adcx r12, r15
adcx r9, [ rsp + 0x70 ]
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r14
mulx r14, r15, [ rax + 0x28 ]
seto dl
mov [ rsp + 0x138 ], r14
mov r14, -0x2 
inc r14
adox rbp, [ rsp + 0x110 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rbp
mov [ rsp + 0x140 ], r12
mov byte [ rsp + 0x148 ], bl
mulx rbx, r12, r14
adcx r15, r11
mov r11, 0x6cfc5fd681c52056 
mov [ rsp + 0x150 ], r12
mulx r12, r14, r11
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r12
mov [ rsp + 0x160 ], r14
mulx r14, r12, [ rax + 0x8 ]
setc dl
clc
mov [ rsp + 0x168 ], rbx
mov rbx, -0x1 
movzx rbp, bpl
adcx rbp, rbx
adcx rdi, r13
adcx rcx, r10
mov r13b, dl
mov rdx, [ rax + 0x10 ]
mulx rbp, r10, [ rsi + 0x8 ]
adcx r8, r9
mov rdx, [ rsp + 0x68 ]
seto r9b
movzx rbx, byte [ rsp + 0x148 ]
mov byte [ rsp + 0x170 ], r13b
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rbx, r13
adox rdx, [ rsp + 0x60 ]
mov rbx, [ rsp + 0x58 ]
mov r13, 0x0 
adox rbx, r13
adcx r15, [ rsp + 0x140 ]
mov [ rsp + 0x178 ], rbx
mov rbx, -0x3 
inc rbx
adox r12, [ rsp + 0x108 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r13
mov [ rsp + 0x180 ], r13
mulx r13, rbx, r11
setc dl
clc
mov [ rsp + 0x188 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx rdi, r12
adox r10, r14
mov r9, [ rsp + 0x150 ]
mov r14, r9
setc r12b
clc
adcx r14, [ rsp + 0x168 ]
adox rbp, [ rsp + 0x50 ]
mov r13, r9
adcx r13, [ rsp + 0x168 ]
adcx rbx, [ rsp + 0x168 ]
mov byte [ rsp + 0x190 ], dl
setc dl
clc
adcx r9, r11
adcx r14, rdi
mov r9b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x198 ], r15
mulx r15, rdi, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], r15
mov byte [ rsp + 0x1a8 ], r9b
mulx r9, r15, [ rax + 0x0 ]
setc dl
clc
adcx r15, r14
mov r14, 0x2341f27177344 
xchg rdx, r15
mov [ rsp + 0x1b0 ], r9
mov [ rsp + 0x1b8 ], rbx
mulx rbx, r9, r14
setc r14b
clc
mov [ rsp + 0x1c0 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx rcx, r10
adcx rbp, r8
mov r8, 0xffffffffffffffff 
mulx r10, r12, r8
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1c8 ], r9
mulx r9, r8, rbx
mov rbx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1d0 ], r9
mov [ rsp + 0x1d8 ], r8
mulx r8, r9, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1e0 ], r8
mov [ rsp + 0x1e8 ], r9
mulx r9, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1f0 ], r12
mov [ rsp + 0x1f8 ], r10
mulx r10, r12, [ rax + 0x10 ]
adox r8, [ rsp + 0x48 ]
adox rdi, r9
setc dl
clc
mov r9, -0x1 
movzx r15, r15b
adcx r15, r9
adcx rcx, r13
adcx rbp, [ rsp + 0x1b8 ]
mov r13, 0x7bc65c783158aea3 
xchg rdx, r11
mulx r9, r15, r13
setc r13b
clc
mov [ rsp + 0x200 ], rdi
mov rdi, -0x1 
movzx r11, r11b
adcx r11, rdi
adcx r8, [ rsp + 0x198 ]
setc r11b
movzx rdi, byte [ rsp + 0x1a8 ]
clc
mov [ rsp + 0x208 ], r8
mov r8, -0x1 
adcx rdi, r8
adcx r15, [ rsp + 0x188 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x210 ], r11b
mulx r11, r8, [ rsi + 0x18 ]
adcx r9, [ rsp + 0x160 ]
setc dl
clc
adcx r8, [ rsp + 0x40 ]
mov byte [ rsp + 0x218 ], dl
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x220 ], r11
seto r11b
mov [ rsp + 0x228 ], r9
mov r9, -0x2 
inc r9
adox rdx, [ rsp + 0x1b0 ]
mov r9, [ rsp + 0x100 ]
mov [ rsp + 0x230 ], r8
setc r8b
mov byte [ rsp + 0x238 ], r11b
movzx r11, byte [ rsp + 0x170 ]
clc
mov [ rsp + 0x240 ], r15
mov r15, -0x1 
adcx r11, r15
adcx r9, [ rsp + 0x138 ]
setc r11b
movzx r15, byte [ rsp + 0x190 ]
clc
mov byte [ rsp + 0x248 ], r8b
mov r8, -0x1 
adcx r15, r8
adcx r9, [ rsp + 0x180 ]
adox r12, [ rsp - 0x10 ]
adox r10, [ rsp + 0xb0 ]
seto r15b
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rcx, rdx
adox r12, rbp
mov r14, [ rsp + 0x208 ]
setc bpl
clc
movzx r13, r13b
adcx r13, r8
adcx r14, [ rsp + 0x240 ]
mov r13, [ rsp + 0x1f8 ]
mov rdx, r13
setc r8b
clc
adcx rdx, [ rsp + 0x1f0 ]
mov byte [ rsp + 0x250 ], r8b
mov r8, r13
adcx r8, [ rsp + 0x1f0 ]
mov byte [ rsp + 0x258 ], r15b
mov r15, rbx
mov [ rsp + 0x260 ], r8
setc r8b
clc
adcx r15, [ rsp + 0x1f0 ]
mov r15, rdx
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x268 ], r8b
mov [ rsp + 0x270 ], r12
mulx r12, r8, [ rsi + 0x8 ]
adox r10, r14
adcx r15, rcx
movzx rdx, r11b
mov rcx, [ rsp + 0xf8 ]
lea rdx, [ rdx + rcx ]
setc cl
clc
adcx r15, [ rsp - 0x18 ]
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r11
mov [ rsp + 0x278 ], r10
mulx r10, r14, r15
setc dl
mov [ rsp + 0x280 ], r10
movzx r10, byte [ rsp + 0x238 ]
clc
mov [ rsp + 0x288 ], r12
mov r12, -0x1 
adcx r10, r12
adcx r8, [ rsp + 0x1a0 ]
seto r10b
inc r12
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r11, [ rsp + 0x178 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mov byte [ rsp + 0x290 ], r10b
mulx r10, r12, r15
mov rdx, r12
mov [ rsp + 0x298 ], r8
seto r8b
mov [ rsp + 0x2a0 ], r11
mov r11, -0x2 
inc r11
adox rdx, r15
mov rdx, r12
setc r11b
clc
adcx rdx, r10
mov byte [ rsp + 0x2a8 ], r8b
setc r8b
mov byte [ rsp + 0x2b0 ], r11b
movzx r11, byte [ rsp + 0x210 ]
clc
mov [ rsp + 0x2b8 ], r14
mov r14, -0x1 
adcx r11, r14
adcx r9, [ rsp + 0x200 ]
mov r11, [ rsp + 0x260 ]
seto r14b
mov [ rsp + 0x2c0 ], r9
mov r9, 0x0 
dec r9
movzx rcx, cl
adox rcx, r9
adox r11, [ rsp + 0x270 ]
setc cl
clc
movzx rbp, bpl
adcx rbp, r9
adcx r11, [ rsp + 0x230 ]
seto bpl
inc r9
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox r11, rdx
mov r14, r10
seto dl
inc r9
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox r14, r12
setc r12b
clc
adcx r11, [ rsp + 0x20 ]
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x2c8 ], r14
mulx r14, r9, r11
adox r10, [ rsp + 0x2b8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x2d0 ], r14
mov [ rsp + 0x2d8 ], r9
mulx r9, r14, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x2e0 ], r9
movzx r9, byte [ rsp + 0x268 ]
mov [ rsp + 0x2e8 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r9, r10
adox r13, [ rsp + 0x1e8 ]
mov r9, 0x7bc65c783158aea3 
xchg rdx, rbx
mov byte [ rsp + 0x2f0 ], bl
mulx rbx, r10, r9
adox r10, [ rsp + 0x1e0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x2f8 ], r10
mulx r10, r9, r11
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x300 ], r8b
mov byte [ rsp + 0x308 ], r12b
mulx r12, r8, [ rax + 0x8 ]
mov rdx, r9
mov [ rsp + 0x310 ], r13
setc r13b
clc
adcx rdx, r10
mov [ rsp + 0x318 ], rdx
mov rdx, [ rsp + 0x2a0 ]
mov byte [ rsp + 0x320 ], r13b
setc r13b
clc
mov byte [ rsp + 0x328 ], bpl
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx rdx, [ rsp + 0x298 ]
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x330 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x338 ], rbp
mov [ rsp + 0x340 ], rcx
mulx rcx, rbp, [ rsi + 0x20 ]
adox rbx, [ rsp + 0x1d8 ]
mov rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x348 ], rcx
seto cl
mov [ rsp + 0x350 ], rbx
movzx rbx, byte [ rsp + 0x258 ]
mov [ rsp + 0x358 ], r12
mov r12, 0x0 
dec r12
adox rbx, r12
adox rdx, [ rsp + 0x120 ]
mov rbx, [ rsp + 0x2c0 ]
seto r12b
mov byte [ rsp + 0x360 ], cl
movzx rcx, byte [ rsp + 0x250 ]
mov [ rsp + 0x368 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox rcx, rdx
adox rbx, [ rsp + 0x228 ]
movzx rcx, byte [ rsp + 0x2b0 ]
mov rdx, [ rsp + 0x288 ]
lea rcx, [ rcx + rdx ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x370 ], rcx
mov byte [ rsp + 0x378 ], r12b
mulx r12, rcx, [ rsi + 0x28 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x380 ], r12
mov [ rsp + 0x388 ], rcx
mulx rcx, r12, rdi
mov rdi, 0xfdc1767ae2ffffff 
mov rdx, r11
mov [ rsp + 0x390 ], rcx
mulx rcx, r11, rdi
mov rdi, r10
mov [ rsp + 0x398 ], rcx
seto cl
mov [ rsp + 0x3a0 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox rdi, r9
mov r13, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x3a8 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
setc dl
clc
adcx r8, [ rsp + 0x18 ]
adox r11, r10
setc r10b
mov [ rsp + 0x3b0 ], r11
movzx r11, byte [ rsp + 0x248 ]
clc
mov byte [ rsp + 0x3b8 ], dl
mov rdx, -0x1 
adcx r11, rdx
adcx rbx, [ rsp + 0x220 ]
adcx r14, rdi
seto r11b
inc rdx
mov rdi, -0x1 
movzx r10, r10b
adox r10, rdi
adox rbp, [ rsp + 0x330 ]
mov r10, [ rsp + 0x310 ]
seto dl
movzx rdi, byte [ rsp + 0x328 ]
mov byte [ rsp + 0x3c0 ], r11b
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rdi, r11
adox r10, [ rsp + 0x278 ]
setc dil
movzx r11, byte [ rsp + 0x308 ]
clc
mov byte [ rsp + 0x3c8 ], dl
mov rdx, -0x1 
adcx r11, rdx
adcx r10, rbx
seto r11b
movzx rbx, byte [ rsp + 0x300 ]
inc rdx
mov rdx, -0x1 
adox rbx, rdx
adox r10, [ rsp + 0x2c8 ]
seto bl
movzx rdx, byte [ rsp + 0x218 ]
mov byte [ rsp + 0x3d0 ], dil
mov rdi, 0x0 
dec rdi
adox rdx, rdi
adox r12, [ rsp + 0x158 ]
mov rdx, [ rsp + 0x358 ]
seto dil
mov [ rsp + 0x3d8 ], rbp
mov rbp, -0x2 
inc rbp
adox rdx, [ rsp + 0x90 ]
setc bpl
mov [ rsp + 0x3e0 ], rdx
movzx rdx, byte [ rsp + 0x320 ]
clc
mov byte [ rsp + 0x3e8 ], dil
mov rdi, -0x1 
adcx rdx, rdi
adcx r10, r8
mov rdx, [ rsi + 0x28 ]
mulx rdi, r8, [ rax + 0x0 ]
mov rdx, [ rsp + 0x3a0 ]
mov [ rsp + 0x3f0 ], r8
setc r8b
mov byte [ rsp + 0x3f8 ], bl
movzx rbx, byte [ rsp + 0x290 ]
clc
mov [ rsp + 0x400 ], r10
mov r10, -0x1 
adcx rbx, r10
adcx rdx, [ rsp + 0x368 ]
mov rbx, [ rsp + 0xc0 ]
seto r10b
mov byte [ rsp + 0x408 ], r8b
movzx r8, byte [ rsp + 0x378 ]
mov [ rsp + 0x410 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r8, rdi
adox rbx, [ rsp + 0x118 ]
seto r8b
inc rdi
mov rdi, -0x1 
movzx rcx, cl
adox rcx, rdi
adox r12, [ rsp + 0x340 ]
adcx rbx, r12
seto cl
inc rdi
mov r12, -0x1 
movzx r11, r11b
adox r11, r12
adox rdx, [ rsp + 0x2f8 ]
adox rbx, [ rsp + 0x350 ]
seto r11b
inc r12
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox rdx, r14
mov r14, [ rsp + 0x388 ]
seto bpl
mov rdi, -0x3 
inc rdi
adox r14, [ rsp + 0x410 ]
seto dil
mov [ rsp + 0x418 ], rbx
mov rbx, -0x3 
inc rbx
adox r9, r13
mov r9, [ rsp + 0x318 ]
adox r9, [ rsp + 0x400 ]
setc r12b
movzx rbx, byte [ rsp + 0x3f8 ]
clc
mov byte [ rsp + 0x420 ], dil
mov rdi, -0x1 
adcx rbx, rdi
adcx rdx, [ rsp + 0x2e8 ]
seto bl
inc rdi
adox r9, [ rsp + 0x3f0 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov byte [ rsp + 0x428 ], bpl
mov [ rsp + 0x430 ], r14
mulx r14, rbp, rdi
setc dil
mov [ rsp + 0x438 ], r14
movzx r14, byte [ rsp + 0x408 ]
clc
mov [ rsp + 0x440 ], rbp
mov rbp, -0x1 
adcx r14, rbp
adcx r9, [ rsp + 0x3d8 ]
mov r14, 0x7bc65c783158aea3 
mov byte [ rsp + 0x448 ], dil
mulx rdi, rbp, r14
xchg rdx, r14
mov [ rsp + 0x450 ], rdi
mov [ rsp + 0x458 ], rbp
mulx rbp, rdi, r13
mov rdx, [ rsp + 0x348 ]
mov [ rsp + 0x460 ], r9
setc r9b
mov byte [ rsp + 0x468 ], bl
movzx rbx, byte [ rsp + 0x3c8 ]
clc
mov byte [ rsp + 0x470 ], r11b
mov r11, -0x1 
adcx rbx, r11
adcx rdx, [ rsp - 0x20 ]
mov rbx, [ rsp + 0xa0 ]
adcx rbx, [ rsp - 0x28 ]
mov r11, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x478 ], rbx
mov byte [ rsp + 0x480 ], r9b
mulx r9, rbx, [ rsi + 0x20 ]
adcx rbx, [ rsp + 0x98 ]
movzx rdx, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x488 ], r9
mov r9, [ rsp + 0x390 ]
lea rdx, [ rdx + r9 ]
setc r9b
mov [ rsp + 0x490 ], rbx
movzx rbx, byte [ rsp + 0x3c0 ]
clc
mov [ rsp + 0x498 ], r11
mov r11, -0x1 
adcx rbx, r11
adcx rdi, [ rsp + 0x398 ]
mov rbx, 0x2341f27177344 
xchg rdx, r13
mov byte [ rsp + 0x4a0 ], r9b
mulx r9, r11, rbx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x4a8 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
adcx rbp, [ rsp + 0x2d8 ]
adcx r11, [ rsp + 0x2d0 ]
mov rdx, [ rsp + 0x370 ]
mov [ rsp + 0x4b0 ], r11
setc r11b
mov [ rsp + 0x4b8 ], rbp
movzx rbp, byte [ rsp + 0x3b8 ]
clc
mov [ rsp + 0x4c0 ], rdi
mov rdi, -0x1 
mov [ rsp + 0x4c8 ], rbx
movzx rbx, byte [ rsp + 0x2a8 ]
adcx rbp, rdi
adcx rdx, rbx
mov rbx, [ rsp + 0xb8 ]
seto bpl
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox rbx, [ rsp + 0x30 ]
setc r8b
clc
movzx rcx, cl
adcx rcx, rdi
adcx rdx, r13
mov rcx, [ rsp + 0x28 ]
mov r13, 0x0 
adox rcx, r13
movzx r13, r11b
lea r13, [ r13 + r9 ]
movzx r9, r8b
adc r9, 0x0
mov r11, [ rsp - 0x30 ]
add r10b, 0xFF
adcx r11, [ rsp + 0x88 ]
mov r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r8, [ rsi + 0x30 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x4d0 ], r11
mov [ rsp + 0x4d8 ], r13
mulx r13, r11, r14
mov [ rsp + 0x4e0 ], r13
mov [ rsp + 0x4e8 ], r11
mulx r11, r13, r15
adcx r8, [ rsp - 0x38 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x4f0 ], r8
mov [ rsp + 0x4f8 ], r11
mulx r11, r8, r14
mov rdx, r8
adox rdx, r11
mov [ rsp + 0x500 ], rdi
seto dil
mov [ rsp + 0x508 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r12, r12b
adox r12, r13
adox r10, rbx
adox rcx, r9
mov r12, [ rsp + 0x1d0 ]
seto bl
movzx r9, byte [ rsp + 0x360 ]
inc r13
mov r13, -0x1 
adox r9, r13
adox r12, [ rsp + 0x1c8 ]
mov r9, r11
setc r13b
clc
mov byte [ rsp + 0x510 ], bl
mov rbx, -0x1 
movzx rdi, dil
adcx rdi, rbx
adcx r9, r8
setc dil
movzx rbx, byte [ rsp + 0x470 ]
clc
mov byte [ rsp + 0x518 ], r13b
mov r13, -0x1 
adcx rbx, r13
adcx r10, r12
mov rbx, [ rsp + 0x1c0 ]
mov r12, 0x0 
adox rbx, r12
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x520 ], dil
mulx rdi, r13, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x3a8 ]
mov [ rsp + 0x528 ], r9
movzx r9, byte [ rsp + 0x468 ]
mov [ rsp + 0x530 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r9, r10
adox rdx, [ rsp + 0x460 ]
mov r9, 0x7bc65c783158aea3 
xchg rdx, r9
mov [ rsp + 0x538 ], rdi
mulx rdi, r10, r15
adcx rbx, rcx
setc cl
movzx rdx, byte [ rsp + 0x3d0 ]
clc
mov [ rsp + 0x540 ], rdi
mov rdi, -0x1 
adcx rdx, rdi
adcx r13, [ rsp + 0x2e0 ]
seto dl
inc rdi
adox r8, r14
setc r8b
clc
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r9, [ rsp + 0x430 ]
setc bpl
movzx rdi, byte [ rsp + 0x428 ]
clc
mov byte [ rsp + 0x548 ], cl
mov rcx, -0x1 
adcx rdi, rcx
adcx r13, [ rsp + 0x418 ]
adox r12, r9
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx rcx, r9, r15
setc r15b
clc
adcx r12, [ rsp + 0x338 ]
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x550 ], bpl
mov byte [ rsp + 0x558 ], dil
mulx rdi, rbp, r12
mov rdx, [ rsp + 0x538 ]
mov [ rsp + 0x560 ], rdi
setc dil
clc
mov [ rsp + 0x568 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx rdx, [ rsp + 0x4c8 ]
setc r8b
clc
movzx r15, r15b
adcx r15, rbp
adcx rdx, [ rsp + 0x530 ]
seto r15b
movzx rbp, byte [ rsp + 0x2f0 ]
mov byte [ rsp + 0x570 ], dil
mov rdi, 0x0 
dec rdi
adox rbp, rdi
adox r10, [ rsp + 0x280 ]
mov rbp, 0x7bc65c783158aea3 
xchg rdx, rbp
mov byte [ rsp + 0x578 ], r15b
mulx r15, rdi, r12
mov rdx, [ rsp + 0x4c0 ]
mov [ rsp + 0x580 ], r15
seto r15b
mov [ rsp + 0x588 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox rdx, [ rsp + 0x130 ]
adcx rdx, rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, r12
mulx rdi, r8, rbx
setc bl
clc
mov [ rsp + 0x590 ], rdi
mov rdi, -0x1 
movzx r15, r15b
adcx r15, rdi
adcx r9, [ rsp + 0x540 ]
adcx rcx, [ rsp + 0x508 ]
setc r15b
movzx rdi, byte [ rsp + 0x448 ]
clc
mov [ rsp + 0x598 ], r8
mov r8, -0x1 
adcx rdi, r8
adcx r13, r10
adcx r9, rbp
seto dil
movzx rbp, byte [ rsp + 0x480 ]
inc r8
mov r10, -0x1 
adox rbp, r10
adox r13, [ rsp + 0x498 ]
adcx rcx, r12
adox r9, [ rsp + 0x478 ]
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mulx r8, r12, [ rax + 0x30 ]
mov rdx, [ rsp + 0x380 ]
setc r10b
mov [ rsp + 0x5a0 ], r8
movzx r8, byte [ rsp + 0x420 ]
clc
mov [ rsp + 0x5a8 ], r12
mov r12, -0x1 
adcx r8, r12
adcx rdx, [ rsp - 0x40 ]
mov r8, [ rsp - 0x48 ]
adcx r8, [ rsp + 0xe8 ]
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x5b0 ], r8
mov [ rsp + 0x5b8 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
adcx r8, [ rsp + 0xe0 ]
seto dl
mov [ rsp + 0x5c0 ], r8
movzx r8, byte [ rsp + 0x558 ]
mov byte [ rsp + 0x5c8 ], r10b
mov r10, 0x0 
dec r10
adox r8, r10
adox r13, [ rsp + 0x3b0 ]
adcx rcx, [ rsp + 0x80 ]
adox r9, [ rsp + 0x4a8 ]
seto r8b
movzx r10, byte [ rsp + 0x550 ]
mov [ rsp + 0x5d0 ], rcx
mov rcx, 0x0 
dec rcx
adox r10, rcx
adox r13, r12
setc r10b
movzx r12, byte [ rsp + 0x578 ]
clc
adcx r12, rcx
adcx r13, [ rsp + 0x528 ]
seto r12b
movzx rcx, byte [ rsp + 0x570 ]
mov [ rsp + 0x5d8 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox rcx, r9
adox r13, [ rsp + 0x3e0 ]
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x5e0 ], r12b
mulx r12, r9, [ rax + 0x30 ]
movzx rdx, dil
mov [ rsp + 0x5e8 ], r12
mov r12, [ rsp + 0x128 ]
lea rdx, [ rdx + r12 ]
mov r12, [ rsp + 0x500 ]
seto dil
mov byte [ rsp + 0x5f0 ], r8b
movzx r8, byte [ rsp + 0x518 ]
mov [ rsp + 0x5f8 ], r9
mov r9, 0x0 
dec r9
adox r8, r9
adox r12, [ rsp + 0x10 ]
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mov [ rsp + 0x600 ], r12
mulx r12, r9, rbp
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x608 ], dil
mov byte [ rsp + 0x610 ], r10b
mulx r10, rdi, [ rax + 0x28 ]
movzx rdx, byte [ rsp + 0x548 ]
mov [ rsp + 0x618 ], r10
movzx r10, byte [ rsp + 0x510 ]
lea rdx, [ rdx + r10 ]
mov r10, r9
mov [ rsp + 0x620 ], rdi
setc dil
clc
adcx r10, r12
mov byte [ rsp + 0x628 ], dil
seto dil
mov byte [ rsp + 0x630 ], cl
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox rdx, r8
movzx rbx, r15b
mov r8, [ rsp + 0x4f8 ]
lea rbx, [ rbx + r8 ]
seto r8b
movzx r15, byte [ rsp + 0x5c8 ]
inc rcx
mov rcx, -0x1 
adox r15, rcx
adox rdx, rbx
mov r15, r9
seto bl
inc rcx
adox r15, rbp
adox r10, r13
mov r15, [ rsp + 0x5b8 ]
seto r13b
movzx rcx, byte [ rsp + 0x630 ]
mov byte [ rsp + 0x638 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox rcx, rdi
adox r15, [ rsp + 0x490 ]
adcx r9, r12
mov rcx, [ rsp + 0x78 ]
setc dil
mov [ rsp + 0x640 ], r9
movzx r9, byte [ rsp + 0x610 ]
clc
mov byte [ rsp + 0x648 ], r13b
mov r13, -0x1 
adcx r9, r13
adcx rcx, [ rsp + 0x5f8 ]
seto r9b
movzx r13, byte [ rsp + 0x5f0 ]
mov byte [ rsp + 0x650 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r13, rdi
adox r15, [ rsp + 0x4b8 ]
setc r13b
seto dil
mov [ rsp + 0x658 ], rcx
mov rcx, r10
mov [ rsp + 0x660 ], r15
mov r15, 0xffffffffffffffff 
sub rcx, r15
mov r15, [ rsp + 0x488 ]
mov [ rsp + 0x668 ], rcx
movzx rcx, byte [ rsp + 0x4a0 ]
mov byte [ rsp + 0x670 ], r13b
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rcx, r13
adox r15, [ rsp + 0x0 ]
seto cl
inc r13
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox rdx, r15
movzx r9, cl
mov r15, [ rsp - 0x8 ]
lea r9, [ r9 + r15 ]
setc r15b
clc
movzx rdi, dil
adcx rdi, r13
adcx rdx, [ rsp + 0x4b0 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx r13, rcx, r14
movzx r14, bl
movzx r8, r8b
lea r14, [ r14 + r8 ]
adox r9, r14
adcx r9, [ rsp + 0x4d8 ]
seto r8b
adc r8b, 0x0
movzx r8, r8b
add byte [ rsp + 0x520 ], 0xFF
adcx r11, [ rsp + 0x440 ]
mov rbx, [ rsp + 0x458 ]
adcx rbx, [ rsp + 0x438 ]
mov r14, [ rsp + 0x5d8 ]
movzx rdx, byte [ rsp + 0x5e0 ]
mov byte [ rsp + 0x678 ], r15b
mov r15, -0x1 
adox rdx, r15
adox r14, [ rsp + 0x5b0 ]
mov rdx, [ rsp + 0x660 ]
adox rdx, [ rsp + 0x5c0 ]
adcx rcx, [ rsp + 0x450 ]
adcx r13, [ rsp + 0x4e8 ]
setc r15b
mov [ rsp + 0x680 ], r13
movzx r13, byte [ rsp + 0x628 ]
clc
mov [ rsp + 0x688 ], rcx
mov rcx, -0x1 
adcx r13, rcx
adcx r14, r11
mov r13, [ rsp + 0x8 ]
setc r11b
movzx rcx, byte [ rsp + 0x638 ]
clc
mov byte [ rsp + 0x690 ], r15b
mov r15, -0x1 
adcx rcx, r15
adcx r13, [ rsp + 0x620 ]
mov rcx, [ rsp + 0x618 ]
adcx rcx, [ rsp + 0x5a8 ]
seto r15b
mov [ rsp + 0x698 ], rcx
movzx rcx, byte [ rsp + 0x608 ]
mov [ rsp + 0x6a0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rcx, r13
adox r14, [ rsp + 0x4d0 ]
movzx rcx, byte [ rsp + 0x670 ]
mov r13, [ rsp + 0x5e8 ]
lea rcx, [ rcx + r13 ]
setc r13b
clc
mov [ rsp + 0x6a8 ], r14
mov r14, -0x1 
movzx r15, r15b
adcx r15, r14
adcx rdi, [ rsp + 0x5d0 ]
adcx r9, [ rsp + 0x658 ]
movzx r15, r8b
adcx r15, rcx
mov r8, 0x6cfc5fd681c52056 
xchg rdx, rbp
mulx r14, rcx, r8
seto dl
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r11, r11b
adox r11, r8
adox rbp, rbx
movzx rbx, r13b
mov r11, [ rsp + 0x5a0 ]
lea rbx, [ rbx + r11 ]
movzx r11, byte [ rsp + 0x690 ]
mov r13, [ rsp + 0x4e0 ]
lea r11, [ r11 + r13 ]
adox rdi, [ rsp + 0x688 ]
adox r9, [ rsp + 0x680 ]
adox r11, r15
setc r13b
movzx r15, byte [ rsp + 0x650 ]
clc
adcx r15, r8
adcx r12, [ rsp + 0x598 ]
mov r15, [ rsp + 0x590 ]
adcx r15, [ rsp + 0x588 ]
adcx rcx, [ rsp + 0x580 ]
adcx r14, [ rsp + 0x568 ]
movzx r8, r13b
mov [ rsp + 0x6b0 ], rbx
mov rbx, 0x0 
adox r8, rbx
mov r13, [ rsp + 0x560 ]
adc r13, 0x0
mov rbx, [ rsp + 0x6a8 ]
add byte [ rsp + 0x648 ], 0xFF
adcx rbx, [ rsp + 0x640 ]
mov [ rsp + 0x6b8 ], r13
setc r13b
mov [ rsp + 0x6c0 ], r8
movzx r8, byte [ rsp + 0x678 ]
add r8, -0x1
mov r8, rbx
mov [ rsp + 0x6c8 ], r14
mov r14, 0xffffffffffffffff 
sbb r8, r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox rbp, [ rsp + 0x4f0 ]
adox rdi, [ rsp + 0x600 ]
setc dl
clc
movzx r13, r13b
adcx r13, r14
adcx rbp, r12
adcx r15, rdi
adox r9, [ rsp + 0x6a0 ]
adox r11, [ rsp + 0x698 ]
adcx rcx, r9
adcx r11, [ rsp + 0x6c8 ]
setc r12b
seto r13b
movzx rdi, dl
add rdi, -0x1
mov rdi, rbp
mov rdx, 0xffffffffffffffff 
sbb rdi, rdx
mov r9, r15
mov r14, 0xfdc1767ae2ffffff 
sbb r9, r14
mov rdx, [ rsp + 0x6c0 ]
mov r14, 0x0 
dec r14
movzx r13, r13b
adox r13, r14
adox rdx, [ rsp + 0x6b0 ]
seto r13b
mov r14, rcx
mov [ rsp + 0x6d0 ], r9
mov r9, 0x7bc65c783158aea3 
sbb r14, r9
mov r9, r11
mov [ rsp + 0x6d8 ], rdi
mov rdi, 0x6cfc5fd681c52056 
sbb r9, rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r12, r12b
adox r12, rdi
adox rdx, [ rsp + 0x6b8 ]
movzx r12, r13b
mov rdi, 0x0 
adox r12, rdi
mov r13, rdx
mov rdi, 0x2341f27177344 
sbb r13, rdi
sbb r12, 0x00000000
cmovc r14, rcx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x20 ], r14
cmovc r8, rbx
mov rbx, [ rsp + 0x6d8 ]
cmovc rbx, rbp
mov [ r12 + 0x8 ], r8
cmovc r9, r11
mov rbp, [ rsp + 0x6d0 ]
cmovc rbp, r15
mov [ r12 + 0x28 ], r9
cmovc r13, rdx
mov [ r12 + 0x30 ], r13
mov r15, [ rsp + 0x668 ]
cmovc r15, r10
mov [ r12 + 0x0 ], r15
mov [ r12 + 0x10 ], rbx
mov [ r12 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1888
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1667
; seed 2087429285446546 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11607627 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 169141 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.014571539902169497
; number reverted permutation / tried permutation: 51242 / 90144 =56.845%
; number reverted decision / tried decision: 46060 / 89855 =51.260%
; validated in 281.733s
