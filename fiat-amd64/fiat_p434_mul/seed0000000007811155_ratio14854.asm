SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1528
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbp
mulx rbp, r8, r15
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r8
mulx r8, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rbx
mulx rbx, r8, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], rbx
mulx rbx, r8, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rbx
mov [ rsp + 0x40 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], r8
mov [ rsp + 0x50 ], rbx
mulx rbx, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rbx
mov [ rsp + 0x60 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rcx
mulx rcx, rbp, [ rax + 0x18 ]
xor rdx, rdx
adox r14, rdi
adox r10, r13
adox rbx, r11
mov rdx, [ rax + 0x0 ]
mulx rdi, r11, [ rsi + 0x28 ]
adox r9, r8
adcx r12, [ rsp + 0x70 ]
mov rdx, [ rsp + 0x68 ]
mov r13, rdx
setc r8b
clc
adcx r13, [ rsp - 0x20 ]
mov [ rsp + 0x78 ], rcx
mov rcx, rdx
adcx rcx, [ rsp - 0x20 ]
mov [ rsp + 0x80 ], rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x88 ], rbp
mov [ rsp + 0x90 ], r11
mulx r11, rbp, r15
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x98 ], r8b
mov [ rsp + 0xa0 ], r12
mulx r12, r8, r15
adcx rbp, rdi
mov rdi, r15
seto dl
mov [ rsp + 0xa8 ], r9
mov r9, -0x2 
inc r9
adox rdi, [ rsp - 0x20 ]
adcx r8, r11
adox r13, r14
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, r15
mulx r11, r14, rdi
adox rcx, r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r9, [ rax + 0x28 ]
adcx r14, r12
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xb0 ], r11
mulx r11, r12, [ rsi + 0x18 ]
setc dl
clc
adcx r13, [ rsp - 0x10 ]
mov [ rsp + 0xb8 ], r11
setc r11b
clc
mov [ rsp + 0xc0 ], r12
mov r12, -0x1 
movzx r15, r15b
adcx r15, r12
adcx r9, [ rsp - 0x28 ]
mov r15, 0x2341f27177344 
xchg rdx, r15
mov byte [ rsp + 0xc8 ], r15b
mulx r15, r12, r13
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], r12
mulx r12, r15, [ rsi + 0x28 ]
adox rbp, rbx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0xe0 ], r12
mulx r12, rbx, r13
adox r8, [ rsp + 0xa8 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xe8 ], r15
mov [ rsp + 0xf0 ], r12
mulx r12, r15, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], rbx
mov [ rsp + 0x100 ], r12
mulx r12, rbx, [ rax + 0x30 ]
adcx rbx, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, rdi, [ rax + 0x8 ]
adox r14, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x110 ], r15
mulx r15, r9, r13
seto dl
mov [ rsp + 0x118 ], r14
mov r14, -0x2 
inc r14
adox rdi, [ rsp - 0x18 ]
adox rbx, [ rsp + 0x0 ]
mov r14, 0x0 
adcx r12, r14
clc
mov r14, -0x1 
movzx r11, r11b
adcx r11, r14
adcx rcx, rdi
adcx rbx, rbp
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbp, [ rax + 0x28 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x120 ], r12
mulx r12, r14, r10
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x128 ], r11b
mulx r11, r10, [ rax + 0x18 ]
adox r10, [ rsp - 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r8
mulx r8, r10, [ rsi + 0x8 ]
adox r11, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x28 ]
setc dl
mov [ rsp + 0x140 ], rbp
movzx rbp, byte [ rsp + 0xc8 ]
clc
mov [ rsp + 0x148 ], r11
mov r11, -0x1 
adcx rbp, r11
adcx r14, [ rsp + 0xb0 ]
mov rbp, 0x0 
adcx r12, rbp
mov r11, r9
clc
adcx r11, r15
mov bpl, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x150 ], r12
mov [ rsp + 0x158 ], r14
mulx r14, r12, [ rsi + 0x20 ]
adox r10, rdi
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r14
mulx r14, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], r12
mov [ rsp + 0x170 ], r8
mulx r8, r12, [ rax + 0x8 ]
mov rdx, r9
mov [ rsp + 0x178 ], r10
mov r10, -0x2 
inc r10
adox rdx, r13
adox r11, rcx
adcx r9, r15
mov rdx, [ rax + 0x10 ]
mulx r10, rcx, [ rsi + 0x10 ]
adox r9, rbx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x180 ], r10
mulx r10, rbx, r13
adcx rbx, r15
setc r13b
clc
adcx rdi, r11
mov r15, 0xffffffffffffffff 
mov rdx, rdi
mulx r11, rdi, r15
mov r15, rdi
mov [ rsp + 0x188 ], r10
setc r10b
clc
adcx r15, r11
mov byte [ rsp + 0x190 ], r13b
mov r13, rdi
adcx r13, r11
mov [ rsp + 0x198 ], r13
setc r13b
clc
adcx r12, r14
adcx rcx, r8
mov r14, [ rsp + 0x138 ]
setc r8b
clc
mov byte [ rsp + 0x1a0 ], r13b
mov r13, -0x1 
movzx rbp, bpl
adcx rbp, r13
adcx r14, [ rsp + 0x130 ]
adox rbx, r14
mov rbp, 0x6cfc5fd681c52056 
mulx r13, r14, rbp
mov rbp, [ rsp + 0x118 ]
adcx rbp, [ rsp + 0x148 ]
mov [ rsp + 0x1a8 ], r13
seto r13b
mov [ rsp + 0x1b0 ], r14
mov r14, 0x0 
dec r14
movzx r10, r10b
adox r10, r14
adox r9, r12
adox rcx, rbx
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r12, [ rax + 0x18 ]
seto dl
inc r14
adox rdi, r10
adox r15, r9
setc dil
clc
mov r9, -0x1 
movzx r8, r8b
adcx r8, r9
adcx r12, [ rsp + 0x180 ]
seto r8b
mov r9, -0x3 
inc r9
adox r15, [ rsp - 0x30 ]
mov r14, 0x2341f27177344 
xchg rdx, r15
mov [ rsp + 0x1b8 ], rbx
mulx rbx, r9, r14
setc r14b
clc
mov [ rsp + 0x1c0 ], rbx
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx rcx, [ rsp + 0x198 ]
adox rcx, [ rsp + 0xa0 ]
mov r8, [ rsp + 0x110 ]
setc bl
mov [ rsp + 0x1c8 ], r9
movzx r9, byte [ rsp + 0x190 ]
clc
mov byte [ rsp + 0x1d0 ], r14b
mov r14, -0x1 
adcx r9, r14
adcx r8, [ rsp + 0x188 ]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x1d8 ], bl
mulx rbx, r14, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x100 ]
adcx rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x1e0 ], rdx
seto dl
mov [ rsp + 0x1e8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox rbp, r8
mov r13, [ rsp + 0xf0 ]
adcx r13, [ rsp + 0xd8 ]
mov r8, [ rsp + 0xd0 ]
mov r12, 0x0 
adcx r8, r12
movzx r12, byte [ rsp + 0x98 ]
clc
mov [ rsp + 0x1f0 ], r8
mov r8, -0x1 
adcx r12, r8
adcx r14, [ rsp - 0x38 ]
mov r12, 0xfdc1767ae2ffffff 
xchg rdx, r12
mov [ rsp + 0x1f8 ], r13
mulx r13, r8, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x200 ], r14
mov byte [ rsp + 0x208 ], r12b
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x210 ], r12
mov [ rsp + 0x218 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x220 ], rbp
mov [ rsp + 0x228 ], r12
mulx r12, rbp, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x230 ], r12
mov [ rsp + 0x238 ], rbp
mulx rbp, r12, r9
adcx rbx, [ rsp + 0x50 ]
mov rdx, r12
mov [ rsp + 0x240 ], rbx
seto bl
mov byte [ rsp + 0x248 ], r15b
mov r15, -0x2 
inc r15
adox rdx, rbp
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov byte [ rsp + 0x250 ], bl
mov byte [ rsp + 0x258 ], dil
mulx rdi, rbx, r10
seto dl
mov [ rsp + 0x260 ], rdi
movzx rdi, byte [ rsp + 0x1a0 ]
mov [ rsp + 0x268 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rdi, r15
adox r11, r8
adox rbx, r13
mov dil, dl
mov rdx, [ rax + 0x0 ]
mulx r13, r8, [ rsi + 0x20 ]
mov rdx, r12
setc r15b
clc
adcx rdx, r9
setc dl
clc
adcx r14, r13
seto r13b
mov byte [ rsp + 0x270 ], r15b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox rcx, [ rsp + 0x268 ]
seto dl
inc r15
adox r8, rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov [ rsp + 0x278 ], rbx
mulx rbx, r15, rcx
mov rcx, [ rsp + 0x108 ]
mov byte [ rsp + 0x280 ], r13b
setc r13b
mov [ rsp + 0x288 ], rbx
movzx rbx, byte [ rsp + 0x128 ]
clc
mov [ rsp + 0x290 ], r14
mov r14, -0x1 
adcx rbx, r14
adcx rcx, [ rsp + 0x158 ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, r8
mov byte [ rsp + 0x298 ], r13b
mulx r13, r14, rbx
seto bl
mov [ rsp + 0x2a0 ], r13
movzx r13, byte [ rsp + 0x258 ]
mov [ rsp + 0x2a8 ], r14
mov r14, 0x0 
dec r14
adox r13, r14
adox rcx, [ rsp + 0x140 ]
mov r13, rbp
setc r14b
clc
mov [ rsp + 0x2b0 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx r13, r12
adcx r15, rbp
mov r12, [ rsp + 0x218 ]
seto bpl
movzx rdi, byte [ rsp + 0x248 ]
inc rcx
mov rcx, -0x1 
adox rdi, rcx
adox r12, [ rsp + 0x1e8 ]
setc dil
movzx rcx, byte [ rsp + 0x1d8 ]
clc
mov [ rsp + 0x2b8 ], r15
mov r15, -0x1 
adcx rcx, r15
adcx r12, r11
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x2c0 ], r15
movzx r15, byte [ rsp + 0x208 ]
mov [ rsp + 0x2c8 ], r11
mov r11, 0x0 
dec r11
adox r15, r11
adox r12, [ rsp + 0x200 ]
seto r15b
inc r11
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox r12, r13
mov r9, [ rsp + 0x120 ]
setc r13b
clc
movzx r14, r14b
adcx r14, r11
adcx r9, [ rsp + 0x150 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, r11
adcx r12, [ rsp + 0x290 ]
mov rbx, [ rsp + 0x288 ]
setc r11b
clc
mov [ rsp + 0x2d0 ], r12
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx rbx, [ rsp + 0x238 ]
seto dil
inc r12
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r9, [ rsp + 0x178 ]
mov rbp, [ rsp + 0x260 ]
seto r12b
mov [ rsp + 0x2d8 ], rbx
movzx rbx, byte [ rsp + 0x280 ]
mov byte [ rsp + 0x2e0 ], r11b
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rbx, r11
adox rbp, [ rsp + 0x1b0 ]
mov rbx, [ rsp + 0x228 ]
setc r11b
mov [ rsp + 0x2e8 ], rbp
movzx rbp, byte [ rsp + 0x1d0 ]
clc
mov byte [ rsp + 0x2f0 ], dil
mov rdi, -0x1 
adcx rbp, rdi
adcx rbx, [ rsp + 0x1b8 ]
mov rbp, [ rsp + 0x2b0 ]
setc dil
mov byte [ rsp + 0x2f8 ], r11b
movzx r11, byte [ rsp + 0x250 ]
clc
mov byte [ rsp + 0x300 ], r15b
mov r15, -0x1 
adcx r11, r15
adcx rbp, [ rsp + 0x1e0 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, r15
adcx rbp, rbx
movzx rdx, r14b
seto bl
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox rdx, [ rsp + 0x170 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rax + 0x28 ]
setc dl
clc
mov byte [ rsp + 0x308 ], bl
mov rbx, -0x1 
movzx r13, r13b
adcx r13, rbx
adcx rbp, [ rsp + 0x278 ]
seto r13b
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r9, [ rsp + 0x1f8 ]
adox r14, [ rsp + 0x1f0 ]
setc r11b
movzx rbx, byte [ rsp + 0x300 ]
clc
mov byte [ rsp + 0x310 ], r13b
mov r13, -0x1 
adcx rbx, r13
adcx rbp, [ rsp + 0x240 ]
seto bl
movzx r13, byte [ rsp + 0x2f0 ]
mov byte [ rsp + 0x318 ], r11b
mov r11, 0x0 
dec r11
adox r13, r11
adox rbp, [ rsp + 0x2b8 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mov byte [ rsp + 0x320 ], bl
mulx rbx, r11, rcx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x328 ], r14
mov [ rsp + 0x330 ], r9
mulx r9, r14, r8
mov r8, r11
seto dl
mov byte [ rsp + 0x338 ], r13b
mov r13, -0x2 
inc r13
adox r8, rbx
mov r13, r11
mov byte [ rsp + 0x340 ], dl
seto dl
mov [ rsp + 0x348 ], r15
mov r15, -0x2 
inc r15
adox r13, rcx
adox r8, [ rsp + 0x2d0 ]
seto r13b
movzx r15, byte [ rsp + 0x2f8 ]
mov [ rsp + 0x350 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r15, r12
adox r14, [ rsp + 0x230 ]
mov r15, rbx
setc r12b
clc
mov byte [ rsp + 0x358 ], r13b
mov r13, -0x1 
movzx rdx, dl
adcx rdx, r13
adcx r15, r11
adox r9, [ rsp + 0x1c8 ]
mov r11, [ rsp + 0x10 ]
seto dl
movzx r13, byte [ rsp + 0x298 ]
mov [ rsp + 0x360 ], r15
mov r15, 0x0 
dec r15
adox r13, r15
adox r11, [ rsp + 0x210 ]
mov r13b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x368 ], r9
mulx r9, r15, [ rax + 0x18 ]
setc dl
mov [ rsp + 0x370 ], r9
movzx r9, byte [ rsp + 0x2e0 ]
clc
mov [ rsp + 0x378 ], r14
mov r14, -0x1 
adcx r9, r14
adcx rbp, r11
setc r9b
clc
adcx r8, [ rsp + 0x90 ]
mov r11, 0xffffffffffffffff 
xchg rdx, r8
mov [ rsp + 0x380 ], rbp
mulx rbp, r14, r11
mov r11, r14
mov byte [ rsp + 0x388 ], r9b
setc r9b
clc
adcx r11, rbp
mov [ rsp + 0x390 ], r11
mov r11, r14
adcx r11, rbp
mov [ rsp + 0x398 ], r11
mov r11, 0x7bc65c783158aea3 
mov byte [ rsp + 0x3a0 ], r9b
mov byte [ rsp + 0x3a8 ], r13b
mulx r13, r9, r11
adox r15, [ rsp + 0x8 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x3b0 ], r15
mov byte [ rsp + 0x3b8 ], r12b
mulx r12, r15, [ rax + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x3c0 ], r8b
mov [ rsp + 0x3c8 ], r13
mulx r13, r8, r11
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x3d0 ], r12
mov [ rsp + 0x3d8 ], r9
mulx r9, r12, r11
adcx r8, rbp
mov rbp, [ rsp + 0x220 ]
setc dl
clc
mov [ rsp + 0x3e0 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx rbp, [ rsp + 0x350 ]
mov rdi, 0x2341f27177344 
xchg rdx, r11
mov [ rsp + 0x3e8 ], rbp
mulx rbp, r8, rdi
xchg rdx, r10
mov [ rsp + 0x3f0 ], rbp
mov [ rsp + 0x3f8 ], r8
mulx r8, rbp, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x400 ], r8
mulx r8, rdi, [ rax + 0x30 ]
adcx r15, [ rsp + 0x348 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x408 ], r8
mov [ rsp + 0x410 ], rdi
mulx rdi, r8, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x418 ], r15
movzx r15, byte [ rsp + 0x308 ]
mov [ rsp + 0x420 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r15, rdi
adox rbp, [ rsp + 0x1a8 ]
setc r15b
clc
adcx r14, r10
mov r14, [ rsp + 0x2c8 ]
setc r10b
movzx rdi, byte [ rsp + 0x270 ]
clc
mov byte [ rsp + 0x428 ], dl
mov rdx, -0x1 
adcx rdi, rdx
adcx r14, [ rsp + 0x48 ]
mov rdi, [ rsp + 0x2c0 ]
adcx rdi, [ rsp + 0xc0 ]
seto dl
mov byte [ rsp + 0x430 ], r10b
mov r10, 0x0 
dec r10
movzx r11, r11b
adox r11, r10
adox r13, [ rsp + 0x3d8 ]
movzx r11, r15b
mov r10, [ rsp + 0x3d0 ]
lea r11, [ r11 + r10 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov [ rsp + 0x438 ], r13
mulx r13, r15, rcx
adox r12, [ rsp + 0x3c8 ]
adox r9, [ rsp + 0x3f8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x440 ], r9
mov [ rsp + 0x448 ], r12
mulx r12, r9, rcx
adcx r8, [ rsp + 0xb8 ]
seto dl
mov [ rsp + 0x450 ], r8
movzx r8, byte [ rsp + 0x3c0 ]
mov [ rsp + 0x458 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r8, rdi
adox rbx, r15
mov r8, [ rsp + 0x420 ]
mov r15, 0x0 
adcx r8, r15
adox r13, [ rsp + 0x2a8 ]
movzx r15, dl
mov rdi, [ rsp + 0x3f0 ]
lea r15, [ r15 + rdi ]
adox r9, [ rsp + 0x2a0 ]
mov rdi, [ rsp + 0x3e8 ]
movzx rdx, byte [ rsp + 0x338 ]
clc
mov [ rsp + 0x460 ], r15
mov r15, -0x1 
adcx rdx, r15
adcx rdi, [ rsp + 0x330 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x468 ], r9
mulx r9, r15, rcx
adox r15, r12
mov rdx, [ rax + 0x0 ]
mulx r12, rcx, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x328 ]
adcx rdx, [ rsp + 0x418 ]
mov [ rsp + 0x470 ], rcx
movzx rcx, r10b
mov [ rsp + 0x478 ], r15
mov r15, [ rsp + 0x400 ]
lea rcx, [ rcx + r15 ]
mov r15, 0x0 
adox r9, r15
movzx r10, byte [ rsp + 0x318 ]
dec r15
adox r10, r15
adox rdi, [ rsp + 0x2e8 ]
movzx r10, byte [ rsp + 0x320 ]
movzx r15, byte [ rsp + 0x310 ]
lea r10, [ r10 + r15 ]
adox rbp, rdx
adcx r11, r10
mov rdx, [ rsi + 0x30 ]
mulx r10, r15, [ rax + 0x28 ]
adox rcx, r11
setc dl
movzx r11, byte [ rsp + 0x3b8 ]
clc
mov [ rsp + 0x480 ], r9
mov r9, -0x1 
adcx r11, r9
adcx rdi, r14
adcx rbp, [ rsp + 0x458 ]
movzx r11, dl
mov r14, 0x0 
adox r11, r14
movzx rdx, byte [ rsp + 0x3a8 ]
mov r14, [ rsp + 0x1c0 ]
lea rdx, [ rdx + r14 ]
movzx r14, byte [ rsp + 0x340 ]
inc r9
mov r9, -0x1 
adox r14, r9
adox rdi, [ rsp + 0x2d8 ]
adcx rcx, [ rsp + 0x450 ]
adcx r8, r11
adox rbp, [ rsp + 0x378 ]
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r11, [ rax + 0x28 ]
adox rcx, [ rsp + 0x368 ]
adox r14, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x488 ], r14
mulx r14, r8, [ rsi + 0x30 ]
setc dl
mov [ rsp + 0x490 ], r13
movzx r13, byte [ rsp + 0x388 ]
clc
mov [ rsp + 0x498 ], rbx
mov rbx, -0x1 
adcx r13, rbx
adcx rdi, [ rsp + 0x3b0 ]
setc r13b
clc
adcx r12, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x18 ]
adcx r14, [ rsp + 0x88 ]
mov rbx, [ rsp + 0x80 ]
mov [ rsp + 0x4a0 ], r14
setc r14b
clc
adcx rbx, [ rsp + 0xe8 ]
mov [ rsp + 0x4a8 ], r8
mov r8, [ rsp - 0x40 ]
mov [ rsp + 0x4b0 ], r12
setc r12b
clc
mov [ rsp + 0x4b8 ], rbx
mov rbx, -0x1 
movzx r14, r14b
adcx r14, rbx
adcx r8, [ rsp + 0x78 ]
movzx r14, dl
mov rbx, 0x0 
adox r14, rbx
mov rdx, [ rsp + 0x370 ]
movzx rbx, byte [ rsp + 0x428 ]
mov [ rsp + 0x4c0 ], r8
mov r8, 0x0 
dec r8
adox rbx, r8
adox rdx, [ rsp + 0x168 ]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x4c8 ], r12b
mulx r12, r8, [ rax + 0x28 ]
adox r11, [ rsp + 0x160 ]
adcx r15, [ rsp - 0x48 ]
adox r9, [ rsp + 0x410 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x4d0 ], r15
mov [ rsp + 0x4d8 ], r12
mulx r12, r15, [ rax + 0x30 ]
seto dl
mov [ rsp + 0x4e0 ], r12
mov r12, 0x0 
dec r12
movzx r13, r13b
adox r13, r12
adox rbp, rbx
adox r11, rcx
adcx r10, [ rsp + 0x40 ]
mov rcx, [ rsp + 0x360 ]
seto r13b
movzx rbx, byte [ rsp + 0x358 ]
inc r12
mov r12, -0x1 
adox rbx, r12
adox rcx, [ rsp + 0x380 ]
adox rdi, [ rsp + 0x498 ]
adox rbp, [ rsp + 0x490 ]
adox r11, [ rsp + 0x468 ]
movzx rbx, dl
mov r12, [ rsp + 0x408 ]
lea rbx, [ rbx + r12 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x4e8 ], r10
mulx r10, r12, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x4f0 ], r15
mov r15, 0x0 
dec r15
movzx r13, r13b
adox r13, r15
adox r9, [ rsp + 0x488 ]
mov r13, [ rsp + 0x38 ]
mov r15, 0x0 
adcx r13, r15
adox rbx, r14
clc
mov r14, -0x1 
movzx rdx, dl
adcx rdx, r14
adcx r9, [ rsp + 0x478 ]
adcx rbx, [ rsp + 0x480 ]
setc dl
movzx r15, byte [ rsp + 0x3a0 ]
clc
adcx r15, r14
adcx rcx, [ rsp + 0x4b8 ]
mov r15, [ rsp + 0xe0 ]
setc r14b
mov [ rsp + 0x4f8 ], r13
movzx r13, byte [ rsp + 0x4c8 ]
clc
mov [ rsp + 0x500 ], rbx
mov rbx, -0x1 
adcx r13, rbx
adcx r15, [ rsp + 0x60 ]
seto r13b
movzx rbx, byte [ rsp + 0x430 ]
mov [ rsp + 0x508 ], r9
mov r9, 0x0 
dec r9
adox rbx, r9
adox rcx, [ rsp + 0x390 ]
adcx r12, [ rsp + 0x58 ]
mov bl, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x510 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
adcx r9, r10
movzx rdx, bl
movzx r13, r13b
lea rdx, [ rdx + r13 ]
seto r10b
mov r13, 0x0 
dec r13
movzx r14, r14b
adox r14, r13
adox rdi, r15
adcx r8, rcx
setc bl
clc
movzx r10, r10b
adcx r10, r13
adcx rdi, [ rsp + 0x398 ]
adox r12, rbp
adcx r12, [ rsp + 0x3e0 ]
adox r9, r11
mov rbp, [ rsp + 0x510 ]
setc r11b
clc
adcx rbp, [ rsp + 0x470 ]
mov r14, 0x2341f27177344 
xchg rdx, rbp
mulx r10, r15, r14
mov rcx, 0xfdc1767ae2ffffff 
mulx r14, r13, rcx
mov rcx, [ rsp + 0x4f0 ]
mov [ rsp + 0x518 ], r10
seto r10b
mov [ rsp + 0x520 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rbx, bl
adox rbx, r15
adox rcx, [ rsp + 0x4d8 ]
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0x528 ], r14
mulx r14, r15, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x530 ], r14
mov [ rsp + 0x538 ], r15
mulx r15, r14, rbx
adcx rdi, [ rsp + 0x4b0 ]
adcx r12, [ rsp + 0x4a8 ]
seto bl
mov [ rsp + 0x540 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r11, r11b
adox r11, r12
adox r9, [ rsp + 0x438 ]
setc r11b
clc
movzx r10, r10b
adcx r10, r12
adcx r8, [ rsp + 0x508 ]
adox r8, [ rsp + 0x448 ]
movzx r10, bl
mov r12, [ rsp + 0x4e0 ]
lea r10, [ r10 + r12 ]
adcx rcx, [ rsp + 0x500 ]
adcx r10, rbp
mov r12, r14
seto bpl
mov rbx, -0x2 
inc rbx
adox r12, rdx
mov r12, r14
setc bl
clc
adcx r12, r15
adcx r14, r15
adox r12, rdi
seto dil
mov [ rsp + 0x548 ], r14
mov r14, 0x0 
dec r14
movzx rbp, bpl
adox rbp, r14
adox rcx, [ rsp + 0x440 ]
adcx r13, r15
adox r10, [ rsp + 0x460 ]
mov r15, [ rsp + 0x528 ]
adcx r15, [ rsp + 0x538 ]
mov rbp, 0x6cfc5fd681c52056 
mov [ rsp + 0x550 ], r15
mulx r15, r14, rbp
movzx rdx, bl
mov rbp, 0x0 
adox rdx, rbp
dec rbp
movzx r11, r11b
adox r11, rbp
adox r9, [ rsp + 0x4a0 ]
adox r8, [ rsp + 0x4c0 ]
adcx r14, [ rsp + 0x530 ]
adcx r15, [ rsp + 0x520 ]
adox rcx, [ rsp + 0x4d0 ]
adox r10, [ rsp + 0x4e8 ]
setc r11b
seto bl
mov rbp, r12
mov [ rsp + 0x558 ], rdx
mov rdx, 0xffffffffffffffff 
sub rbp, rdx
mov rdx, [ rsp + 0x548 ]
mov [ rsp + 0x560 ], rbp
mov rbp, 0x0 
dec rbp
movzx rdi, dil
adox rdi, rbp
adox rdx, [ rsp + 0x540 ]
adox r13, r9
adox r8, [ rsp + 0x550 ]
adox r14, rcx
adox r15, r10
seto dil
mov r9, rdx
mov rcx, 0xffffffffffffffff 
sbb r9, rcx
mov r10, r13
sbb r10, rcx
mov rbp, [ rsp + 0x4f8 ]
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox rbp, [ rsp + 0x558 ]
movzx rbx, r11b
mov rcx, [ rsp + 0x518 ]
lea rbx, [ rbx + rcx ]
seto cl
mov r11, 0x0 
dec r11
movzx rdi, dil
adox rdi, r11
adox rbp, rbx
seto dil
mov rbx, r8
mov r11, 0xfdc1767ae2ffffff 
sbb rbx, r11
movzx r11, dil
movzx rcx, cl
lea r11, [ r11 + rcx ]
mov rcx, r14
mov rdi, 0x7bc65c783158aea3 
sbb rcx, rdi
mov rdi, r15
mov [ rsp + 0x568 ], r9
mov r9, 0x6cfc5fd681c52056 
sbb rdi, r9
mov r9, rbp
mov [ rsp + 0x570 ], rbx
mov rbx, 0x2341f27177344 
sbb r9, rbx
sbb r11, 0x00000000
cmovc r10, r13
cmovc rcx, r14
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], r10
cmovc r9, rbp
mov [ r11 + 0x30 ], r9
cmovc rdi, r15
mov r13, [ rsp + 0x560 ]
cmovc r13, r12
mov [ r11 + 0x28 ], rdi
mov r12, [ rsp + 0x570 ]
cmovc r12, r8
mov [ r11 + 0x0 ], r13
mov [ r11 + 0x18 ], r12
mov r8, [ rsp + 0x568 ]
cmovc r8, rdx
mov [ r11 + 0x20 ], rcx
mov [ r11 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1528
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4854
; seed 1380958198792560 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11834053 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=32, initial num_batches=31): 198455 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016769825181617827
; number reverted permutation / tried permutation: 50918 / 89690 =56.771%
; number reverted decision / tried decision: 43483 / 90309 =48.149%
; validated in 378.123s
