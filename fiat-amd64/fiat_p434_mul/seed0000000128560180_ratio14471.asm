SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1736
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
xor rdx, rdx
adox rcx, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x48 ], rbx
mulx rbx, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r14
mulx r14, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rbx
mulx rbx, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r14
mulx r14, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], r14
mulx r14, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], rbx
mulx rbx, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], r14
mulx r14, rbx, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x40 ], r14
mov [ rsp + 0x48 ], rbx
mulx rbx, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x50 ], rbx
mov [ rsp + 0x58 ], r14
mulx r14, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], rbx
mulx rbx, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x70 ], rbx
mov [ rsp + 0x78 ], r14
mulx r14, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], r14
mulx r14, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa0 ], r9
mov [ rsp + 0xa8 ], r12
mulx r12, r9, [ rsi + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], r9
mulx r9, r12, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r9
mov [ rsp + 0xc8 ], r12
mulx r12, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r12
mov [ rsp + 0xd8 ], r9
mulx r9, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r14
mulx r14, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], r11
mulx r11, rbx, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r11
mov [ rsp + 0x108 ], rbx
mulx rbx, r11, [ rax + 0x8 ]
adox r10, r8
mov rdx, r15
adcx rdx, rdi
mov r8, r15
mov [ rsp + 0x110 ], rbx
seto bl
mov [ rsp + 0x118 ], r11
mov r11, -0x2 
inc r11
adox r8, r13
adcx r15, rdi
adox rdx, rcx
setc r8b
clc
adcx r12, rdx
seto cl
inc r11
adox rbp, r9
mov rdx, [ rsi + 0x8 ]
mulx r11, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], rbp
mulx rbp, r11, [ rax + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], r10
mulx r10, r15, r12
adox r11, r14
mov r14, 0x2341f27177344 
mov rdx, r12
mov [ rsp + 0x140 ], r10
mulx r10, r12, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x148 ], r10
mov [ rsp + 0x150 ], r12
mulx r12, r10, r14
adox r9, rbp
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x158 ], r12
mulx r12, r14, rbp
mov rbp, [ rsp + 0xf0 ]
mov [ rsp + 0x160 ], r10
setc r10b
clc
mov [ rsp + 0x168 ], r15
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx rbp, [ rsp + 0xf8 ]
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x170 ], r12
mulx r12, r15, rbx
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], r9
mulx r9, r14, [ rsi + 0x0 ]
adcx r14, [ rsp + 0xe8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x188 ], r11
mov byte [ rsp + 0x190 ], r10b
mulx r10, r11, r13
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x198 ], r10
mov [ rsp + 0x1a0 ], r14
mulx r14, r10, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a8 ], rbp
mov byte [ rsp + 0x1b0 ], cl
mulx rcx, rbp, [ rax + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1b8 ], rcx
mov [ rsp + 0x1c0 ], rbp
mulx rbp, rcx, r13
mov r13, r15
setc dl
clc
adcx r13, r12
mov [ rsp + 0x1c8 ], r13
mov r13, r15
adcx r13, r12
mov [ rsp + 0x1d0 ], r13
setc r13b
clc
mov [ rsp + 0x1d8 ], r11
mov r11, -0x1 
movzx r8, r8b
adcx r8, r11
adcx rdi, rcx
seto r8b
inc r11
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox r9, [ rsp + 0xe0 ]
setc dl
clc
adcx r15, rbx
seto r15b
dec r11
movzx rdx, dl
adox rdx, r11
adox rbp, [ rsp + 0xc8 ]
adox r10, [ rsp + 0xc0 ]
adox r14, [ rsp + 0x1d8 ]
mov rcx, [ rsp + 0x138 ]
setc bl
movzx rdx, byte [ rsp + 0x1b0 ]
clc
adcx rdx, r11
adcx rcx, [ rsp + 0x130 ]
adcx rdi, [ rsp + 0x1a8 ]
adcx rbp, [ rsp + 0x1a0 ]
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x1e0 ], r13b
mulx r13, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x1e8 ], r13
setc r13b
clc
mov [ rsp + 0x1f0 ], r11
mov r11, -0x1 
movzx r15, r15b
adcx r15, r11
adcx rdx, [ rsp + 0xa0 ]
setc r15b
clc
movzx r13, r13b
adcx r13, r11
adcx r9, r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r13, [ rax + 0x0 ]
adcx r14, r10
seto dl
movzx r10, byte [ rsp + 0x190 ]
mov byte [ rsp + 0x1f8 ], r15b
mov r15, 0x0 
dec r15
adox r10, r15
adox rcx, [ rsp + 0x128 ]
adox rdi, [ rsp + 0x188 ]
mov r10b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x200 ], r14
mulx r14, r15, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x208 ], r14
mov r14, 0x0 
dec r14
movzx rbx, bl
adox rbx, r14
adox rcx, [ rsp + 0x1c8 ]
adox rdi, [ rsp + 0x1d0 ]
seto bl
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox rbp, [ rsp + 0x180 ]
seto dl
inc r14
adox r13, rcx
mov cl, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x210 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x218 ], r10b
mov [ rsp + 0x220 ], rdi
mulx rdi, r10, r13
mov rdx, [ rsp + 0x120 ]
mov [ rsp + 0x228 ], rdi
seto dil
mov [ rsp + 0x230 ], r11
mov r11, 0x0 
dec r11
movzx r8, r8b
adox r8, r11
adox rdx, [ rsp + 0x1f0 ]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x238 ], dil
mulx rdi, r11, [ rax + 0x30 ]
adox r14, [ rsp + 0x1e8 ]
setc dl
mov [ rsp + 0x240 ], r14
movzx r14, byte [ rsp + 0x1e0 ]
clc
mov [ rsp + 0x248 ], r10
mov r10, -0x1 
adcx r14, r10
adcx r12, [ rsp + 0x178 ]
mov r14, [ rsp + 0x168 ]
adcx r14, [ rsp + 0x170 ]
mov r10, [ rsp + 0x140 ]
adcx r10, [ rsp + 0x160 ]
adox r11, r15
mov r15b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x250 ], r10
mov [ rsp + 0x258 ], r11
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x260 ], r15b
mov [ rsp + 0x268 ], r11
mulx r11, r15, r13
mov rdx, r15
mov [ rsp + 0x270 ], r10
setc r10b
clc
adcx rdx, r11
mov byte [ rsp + 0x278 ], r10b
seto r10b
mov [ rsp + 0x280 ], rdx
mov rdx, 0x0 
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r9, r8
seto cl
inc rdx
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox rbp, r12
adox r14, r9
mov rbx, 0xfdc1767ae2ffffff 
mov rdx, rbx
mulx r12, rbx, r13
mov r9, r15
adcx r9, r11
adcx rbx, r11
movzx r11, r10b
lea r11, [ r11 + rdi ]
adcx r12, [ rsp + 0x248 ]
mov rdi, [ rsp + 0x230 ]
seto r10b
inc r8
adox rdi, [ rsp + 0x28 ]
setc dl
clc
adcx r15, r13
mov r15, [ rsp + 0x20 ]
adox r15, [ rsp + 0x98 ]
seto r8b
mov [ rsp + 0x288 ], r12
movzx r12, byte [ rsp + 0x238 ]
mov [ rsp + 0x290 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r12, rbx
adox rdi, [ rsp + 0x220 ]
adcx rdi, [ rsp + 0x280 ]
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r13
mov [ rsp + 0x298 ], r11
mulx r11, rbx, r12
mov r12, [ rsp + 0x90 ]
mov byte [ rsp + 0x2a0 ], r10b
setc r10b
clc
mov byte [ rsp + 0x2a8 ], cl
mov rcx, -0x1 
movzx r8, r8b
adcx r8, rcx
adcx r12, [ rsp + 0x270 ]
seto r8b
inc rcx
adox rdi, [ rsp + 0x8 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rdi
mov [ rsp + 0x2b0 ], r11
mov [ rsp + 0x2b8 ], rbx
mulx rbx, r11, rcx
mov rcx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x2c0 ], r13b
mov [ rsp + 0x2c8 ], r11
mulx r11, r13, rcx
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2d0 ], r11
mov [ rsp + 0x2d8 ], r13
mulx r13, r11, rcx
seto cl
mov [ rsp + 0x2e0 ], r13
mov r13, 0x0 
dec r13
movzx r8, r8b
adox r8, r13
adox rbp, r15
adox r12, r14
seto r14b
inc r13
mov r15, -0x1 
movzx r10, r10b
adox r10, r15
adox rbp, r9
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r15, r13, [ rsi + 0x18 ]
mov rdx, rbx
mov [ rsp + 0x2e8 ], r10
setc r10b
clc
adcx rdx, [ rsp + 0x2c8 ]
mov [ rsp + 0x2f0 ], rdx
mov rdx, r9
mov [ rsp + 0x2f8 ], rbp
setc bpl
clc
adcx rdx, [ rsp + 0x2c8 ]
seto dl
mov byte [ rsp + 0x300 ], cl
mov rcx, -0x2 
inc rcx
adox r13, [ rsp + 0x0 ]
mov rcx, rbx
mov [ rsp + 0x308 ], r13
setc r13b
clc
mov [ rsp + 0x310 ], r11
mov r11, -0x1 
movzx rbp, bpl
adcx rbp, r11
adcx rcx, [ rsp + 0x2c8 ]
mov rbp, [ rsp + 0x150 ]
seto r11b
mov [ rsp + 0x318 ], rcx
movzx rcx, byte [ rsp + 0x278 ]
mov byte [ rsp + 0x320 ], r13b
mov r13, 0x0 
dec r13
adox rcx, r13
adox rbp, [ rsp + 0x158 ]
mov rcx, 0x2341f27177344 
xchg rdx, rdi
mov byte [ rsp + 0x328 ], r14b
mulx r14, r13, rcx
mov rdx, [ rsp + 0x228 ]
setc cl
mov [ rsp + 0x330 ], r14
movzx r14, byte [ rsp + 0x2c0 ]
clc
mov [ rsp + 0x338 ], r12
mov r12, -0x1 
adcx r14, r12
adcx rdx, [ rsp + 0x2b8 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x340 ], cl
mulx rcx, r12, [ rax + 0x30 ]
adcx r13, [ rsp + 0x2b0 ]
seto dl
mov [ rsp + 0x348 ], r13
mov r13, 0x0 
dec r13
movzx r11, r11b
adox r11, r13
adox r15, r8
movzx r8, byte [ rsp + 0x218 ]
mov r11, [ rsp + 0x198 ]
lea r8, [ r8 + r11 ]
mov r11, [ rsp + 0x200 ]
setc r13b
mov [ rsp + 0x350 ], r14
movzx r14, byte [ rsp + 0x2a8 ]
clc
mov [ rsp + 0x358 ], r15
mov r15, -0x1 
adcx r14, r15
adcx r11, [ rsp + 0x240 ]
movzx r14, byte [ rsp + 0x1f8 ]
mov r15, [ rsp - 0x48 ]
lea r14, [ r14 + r15 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r9
mov byte [ rsp + 0x360 ], r13b
mov [ rsp + 0x368 ], rcx
mulx rcx, r13, r15
mov r15, [ rsp + 0x268 ]
mov [ rsp + 0x370 ], rcx
seto cl
mov [ rsp + 0x378 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r10, r10b
adox r10, r13
adox r15, [ rsp + 0x78 ]
seto r10b
movzx r13, byte [ rsp + 0x260 ]
mov byte [ rsp + 0x380 ], cl
mov rcx, 0x0 
dec rcx
adox r13, rcx
adox r14, r8
mov r13, [ rsp + 0x70 ]
setc r8b
clc
movzx r10, r10b
adcx r10, rcx
adcx r13, [ rsp + 0x48 ]
setc r10b
clc
movzx r8, r8b
adcx r8, rcx
adcx r14, [ rsp + 0x258 ]
seto r8b
movzx rcx, byte [ rsp + 0x2a0 ]
mov [ rsp + 0x388 ], r12
mov r12, 0x0 
dec r12
adox rcx, r12
adox r11, [ rsp + 0x250 ]
movzx r8, r8b
movzx rcx, r8b
adcx rcx, [ rsp + 0x298 ]
adox rbp, r14
mov r8, [ rsp + 0x338 ]
seto r14b
inc r12
mov r12, -0x1 
movzx rdi, dil
adox rdi, r12
adox r8, [ rsp + 0x290 ]
seto dil
movzx r12, byte [ rsp + 0x328 ]
mov [ rsp + 0x390 ], r8
mov r8, 0x0 
dec r8
adox r12, r8
adox r11, r15
movzx r12, r9b
mov r15, [ rsp + 0x148 ]
lea r12, [ r12 + r15 ]
setc r15b
clc
movzx r14, r14b
adcx r14, r8
adcx rcx, r12
movzx r9, r15b
mov r14, 0x0 
adcx r9, r14
adox r13, rbp
mov r15, 0x2341f27177344 
mulx r12, rbp, r15
mov rdx, [ rax + 0x0 ]
mulx r8, r14, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x40 ]
clc
mov r15, -0x1 
movzx r10, r10b
adcx r10, r15
adcx rdx, [ rsp + 0x388 ]
mov r10, [ rsp + 0x368 ]
mov r15, 0x0 
adcx r10, r15
movzx r15, byte [ rsp + 0x340 ]
clc
mov [ rsp + 0x398 ], r12
mov r12, -0x1 
adcx r15, r12
adcx rbx, [ rsp + 0x310 ]
mov r15, [ rsp + 0x2e0 ]
adcx r15, [ rsp + 0x2d8 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x3a0 ], rbp
mov [ rsp + 0x3a8 ], r15
mulx r15, rbp, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x2d0 ]
adcx rdx, [ rsp + 0x378 ]
mov [ rsp + 0x3b0 ], rdx
mov rdx, [ rsp + 0x308 ]
mov [ rsp + 0x3b8 ], r13
setc r13b
mov [ rsp + 0x3c0 ], rbx
movzx rbx, byte [ rsp + 0x300 ]
clc
mov [ rsp + 0x3c8 ], r15
mov r15, -0x1 
adcx rbx, r15
adcx rdx, [ rsp + 0x2f8 ]
mov rbx, [ rsp + 0x390 ]
adcx rbx, [ rsp + 0x358 ]
setc r15b
clc
adcx r8, [ rsp + 0x118 ]
mov byte [ rsp + 0x3d0 ], r13b
mov r13, [ rsp - 0x8 ]
mov byte [ rsp + 0x3d8 ], r15b
setc r15b
mov [ rsp + 0x3e0 ], rbp
movzx rbp, byte [ rsp + 0x380 ]
clc
mov [ rsp + 0x3e8 ], r11
mov r11, -0x1 
adcx rbp, r11
adcx r13, [ rsp + 0x2e8 ]
mov rbp, [ rsp - 0x10 ]
adcx rbp, [ rsp + 0xb8 ]
seto r11b
mov [ rsp + 0x3f0 ], rbp
movzx rbp, byte [ rsp + 0x320 ]
mov [ rsp + 0x3f8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rbp, r13
adox rdx, [ rsp + 0x2f0 ]
setc bpl
clc
adcx r14, rdx
adox rbx, [ rsp + 0x318 ]
adcx r8, rbx
mov rdx, 0x7bc65c783158aea3 
mulx r13, rbx, r14
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x400 ], r13
mov byte [ rsp + 0x408 ], bpl
mulx rbp, r13, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x410 ], rbx
mov [ rsp + 0x418 ], rbp
mulx rbp, rbx, r14
setc dl
clc
mov [ rsp + 0x420 ], r13
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx rcx, r12
adcx r10, r9
mov r9b, dl
mov rdx, [ rsi + 0x20 ]
mulx r12, r11, [ rax + 0x30 ]
mov rdx, rbx
setc r13b
clc
adcx rdx, rbp
mov byte [ rsp + 0x428 ], r13b
mov r13, [ rsp + 0x288 ]
mov [ rsp + 0x430 ], r10
setc r10b
clc
mov [ rsp + 0x438 ], r12
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx r13, [ rsp + 0x3e8 ]
mov rdi, rbp
setc r12b
clc
mov [ rsp + 0x440 ], r11
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rdi, rbx
mov r10, [ rsp + 0x110 ]
setc r11b
clc
mov [ rsp + 0x448 ], rdi
mov rdi, -0x1 
movzx r15, r15b
adcx r15, rdi
adcx r10, [ rsp + 0x3e0 ]
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x450 ], r11b
mulx r11, rdi, [ rsi + 0x20 ]
mov rdx, [ rsp - 0x28 ]
adcx rdx, [ rsp + 0x3c8 ]
mov [ rsp + 0x458 ], rdx
setc dl
mov [ rsp + 0x460 ], r11
movzx r11, byte [ rsp + 0x3d8 ]
clc
mov [ rsp + 0x468 ], r10
mov r10, -0x1 
adcx r11, r10
adcx r13, [ rsp + 0x3f8 ]
adox r13, [ rsp + 0x3c0 ]
mov r11, [ rsp + 0x3b8 ]
seto r10b
mov [ rsp + 0x470 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r12, r12b
adox r12, r13
adox r11, [ rsp + 0x350 ]
mov r12, [ rsp + 0x18 ]
seto r13b
mov byte [ rsp + 0x478 ], r9b
mov r9, -0x2 
inc r9
adox r12, [ rsp + 0x38 ]
seto r9b
mov [ rsp + 0x480 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox rcx, [ rsp + 0x348 ]
adcx r11, [ rsp + 0x3f0 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, r12
adcx rdi, [ rsp - 0x30 ]
setc dl
clc
movzx r10, r10b
adcx r10, r12
adcx r11, [ rsp + 0x3a8 ]
setc r10b
clc
adcx rbx, r14
adcx r15, r8
mov rbx, [ rsp + 0x468 ]
seto r8b
movzx r12, byte [ rsp + 0x478 ]
mov [ rsp + 0x488 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r12, rdi
adox rbx, [ rsp + 0x470 ]
mov r12, [ rsp + 0x460 ]
seto dil
mov byte [ rsp + 0x490 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rdx, dl
adox rdx, r10
adox r12, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0x448 ]
mov rdx, [ rsp + 0x80 ]
adox rdx, [ rsp + 0x440 ]
setc r10b
clc
adcx r15, [ rsp + 0x10 ]
mov byte [ rsp + 0x498 ], r10b
mov r10, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x4a0 ], r15
mov [ rsp + 0x4a8 ], r12
mulx r12, r15, r10
mov r10, [ rsp + 0x438 ]
mov [ rsp + 0x4b0 ], rcx
mov rcx, 0x0 
adox r10, rcx
adcx rbx, [ rsp + 0x480 ]
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4b8 ], r10
mov [ rsp + 0x4c0 ], rbx
mulx rbx, r10, rcx
mov rcx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x4c8 ], rbx
mov byte [ rsp + 0x4d0 ], r13b
mulx r13, rbx, [ rsi + 0x28 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox r11, [ rsp + 0x458 ]
seto dil
inc rdx
mov rdx, -0x1 
movzx r9, r9b
adox r9, rdx
adox rbx, [ rsp + 0x30 ]
seto r9b
movzx rdx, byte [ rsp + 0x450 ]
mov [ rsp + 0x4d8 ], rbx
mov rbx, 0x0 
dec rbx
adox rdx, rbx
adox rbp, [ rsp + 0x420 ]
mov rdx, [ rsp + 0x418 ]
adox rdx, [ rsp + 0x410 ]
movzx rbx, byte [ rsp + 0x360 ]
mov [ rsp + 0x4e0 ], rdx
mov rdx, [ rsp + 0x330 ]
lea rbx, [ rbx + rdx ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4e8 ], rbp
mov [ rsp + 0x4f0 ], r11
mulx r11, rbp, r14
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x4f8 ], dil
mov [ rsp + 0x500 ], r10
mulx r10, rdi, r14
mov r14, 0x6cfc5fd681c52056 
mov rdx, r14
mov [ rsp + 0x508 ], r10
mulx r10, r14, rcx
mov rdx, [ rsp + 0xb0 ]
mov [ rsp + 0x510 ], r10
setc r10b
mov [ rsp + 0x518 ], r14
movzx r14, byte [ rsp + 0x408 ]
clc
mov [ rsp + 0x520 ], rbx
mov rbx, -0x1 
adcx r14, rbx
adcx rdx, [ rsp + 0x58 ]
adox rbp, [ rsp + 0x400 ]
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x528 ], r10b
mulx r10, rbx, [ rsi + 0x28 ]
adox rdi, r11
mov rdx, r15
setc r11b
clc
adcx rdx, r12
mov [ rsp + 0x530 ], r10
seto r10b
mov [ rsp + 0x538 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r13, [ rsp + 0xd8 ]
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x540 ], r13
mulx r13, rdi, [ rax + 0x0 ]
mov rdx, [ rsp + 0x68 ]
adox rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x548 ], rdx
mov rdx, [ rsp + 0x430 ]
mov [ rsp + 0x550 ], r13
setc r13b
clc
mov [ rsp + 0x558 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx rdx, [ rsp + 0x520 ]
mov r8, r12
seto bpl
mov byte [ rsp + 0x560 ], r10b
mov r10, 0x0 
dec r10
movzx r13, r13b
adox r13, r10
adox r8, r15
adox r12, [ rsp + 0x500 ]
setc r13b
clc
adcx r15, rcx
seto r15b
movzx r10, byte [ rsp + 0x4d0 ]
mov [ rsp + 0x568 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r10, r12
adox r14, [ rsp + 0x4b0 ]
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x570 ], r8
mulx r8, r12, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x210 ]
mov [ rsp + 0x578 ], r8
seto r8b
mov [ rsp + 0x580 ], r12
mov r12, 0x0 
dec r12
movzx r11, r11b
adox r11, r12
adox rdx, [ rsp + 0x50 ]
seto r11b
inc r12
mov r12, -0x1 
movzx r8, r8b
adox r8, r12
adox r10, rdx
movzx r8, r11b
mov rdx, [ rsp + 0x208 ]
lea r8, [ r8 + rdx ]
adcx r9, [ rsp + 0x4c0 ]
setc dl
clc
adcx rdi, r9
movzx r11, r13b
movzx r9, byte [ rsp + 0x428 ]
lea r11, [ r11 + r9 ]
mov r9, [ rsp + 0x3a0 ]
setc r13b
movzx r12, byte [ rsp + 0x3d0 ]
clc
mov [ rsp + 0x588 ], rdi
mov rdi, -0x1 
adcx r12, rdi
adcx r9, [ rsp + 0x370 ]
mov r12, [ rsp + 0x398 ]
mov rdi, 0x0 
adcx r12, rdi
adox r8, r11
mov r11, 0x7bc65c783158aea3 
xchg rdx, rcx
mov byte [ rsp + 0x590 ], r13b
mulx r13, rdi, r11
movzx r11, byte [ rsp + 0x490 ]
clc
mov byte [ rsp + 0x598 ], cl
mov rcx, -0x1 
adcx r11, rcx
adcx r14, [ rsp + 0x3b0 ]
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x5a0 ], r13
mulx r13, rcx, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x5a8 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r15, r15b
adox r15, r13
adox rdi, [ rsp + 0x4c8 ]
mov r15b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x5b0 ], rdi
mulx rdi, r13, [ rax + 0x28 ]
adcx r9, r10
adcx r12, r8
seto dl
mov r10, -0x1 
inc r10
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox r13, [ rsp + 0x60 ]
movzx rbp, r15b
adcx rbp, r10
adox rbx, rdi
movzx r15, byte [ rsp + 0x4f8 ]
clc
adcx r15, r8
adcx r14, [ rsp + 0x488 ]
adcx r9, [ rsp + 0x4a8 ]
mov r15, [ rsp + 0x5a0 ]
setc dil
clc
movzx rdx, dl
adcx rdx, r8
adcx r15, [ rsp + 0x518 ]
mov rdx, 0x2341f27177344 
mulx r8, r10, r11
adcx r10, [ rsp + 0x510 ]
seto r11b
mov rdx, 0x0 
dec rdx
movzx rdi, dil
adox rdi, rdx
adox r12, [ rsp + 0x4a0 ]
mov rdi, [ rsp + 0x4f0 ]
setc dl
mov [ rsp + 0x5b8 ], r10
movzx r10, byte [ rsp + 0x498 ]
clc
mov [ rsp + 0x5c0 ], r15
mov r15, -0x1 
adcx r10, r15
adcx rdi, [ rsp + 0x4e8 ]
movzx r10, byte [ rsp + 0x560 ]
mov r15, [ rsp + 0x508 ]
lea r10, [ r10 + r15 ]
movzx r15, dl
lea r15, [ r15 + r8 ]
adcx r14, [ rsp + 0x4e0 ]
adox rbp, [ rsp + 0x4b8 ]
adcx r9, [ rsp + 0x558 ]
mov r8, [ rsp + 0x550 ]
setc dl
clc
adcx r8, [ rsp - 0x38 ]
mov [ rsp + 0x5c8 ], r15
seto r15b
mov [ rsp + 0x5d0 ], r8
movzx r8, byte [ rsp + 0x528 ]
mov byte [ rsp + 0x5d8 ], r11b
mov r11, 0x0 
dec r11
adox r8, r11
adox rdi, [ rsp + 0x4d8 ]
adox r14, [ rsp + 0x540 ]
seto r8b
inc r11
mov r11, -0x1 
movzx rdx, dl
adox rdx, r11
adox r12, [ rsp + 0x538 ]
adox r10, rbp
seto bpl
inc r11
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r9, [ rsp + 0x548 ]
adcx rcx, [ rsp - 0x40 ]
mov r8, [ rsp + 0x5a8 ]
adcx r8, [ rsp - 0x18 ]
movzx r11, bpl
movzx r15, r15b
lea r11, [ r11 + r15 ]
mov r15, [ rsp - 0x20 ]
adcx r15, [ rsp + 0x1c0 ]
adox r13, r12
seto r12b
movzx rbp, byte [ rsp + 0x598 ]
inc rdx
mov rdx, -0x1 
adox rbp, rdx
adox rdi, [ rsp + 0x570 ]
adox r14, [ rsp + 0x568 ]
setc bpl
clc
movzx r12, r12b
adcx r12, rdx
adcx r10, rbx
movzx rbx, byte [ rsp + 0x5d8 ]
mov r12, [ rsp + 0x530 ]
lea rbx, [ rbx + r12 ]
mov r12, [ rsp + 0x580 ]
setc dl
clc
mov [ rsp + 0x5e0 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx r12, [ rsp + 0x1b8 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mov [ rsp + 0x5e8 ], r12
mulx r12, r15, [ rsp + 0x588 ]
adox r9, [ rsp + 0x5b0 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x5f0 ], r8
mov [ rsp + 0x5f8 ], r9
mulx r9, r8, [ rsp + 0x588 ]
adox r13, [ rsp + 0x5c0 ]
adox r10, [ rsp + 0x5b8 ]
mov rdx, r15
mov [ rsp + 0x600 ], r10
seto r10b
mov [ rsp + 0x608 ], r13
mov r13, -0x2 
inc r13
adox rdx, [ rsp + 0x588 ]
setc dl
clc
movzx rbp, bpl
adcx rbp, r13
adcx r11, rbx
mov rbp, r15
setc bl
clc
adcx rbp, r12
mov r13, 0x2341f27177344 
xchg rdx, r13
mov byte [ rsp + 0x610 ], bl
mov byte [ rsp + 0x618 ], r13b
mulx r13, rbx, [ rsp + 0x588 ]
adcx r15, r12
adcx r8, r12
mov r12, 0x7bc65c783158aea3 
mov rdx, r12
mov [ rsp + 0x620 ], r11
mulx r11, r12, [ rsp + 0x588 ]
adcx r12, r9
mov r9, 0x6cfc5fd681c52056 
mov rdx, r9
mov byte [ rsp + 0x628 ], r10b
mulx r10, r9, [ rsp + 0x588 ]
adcx r9, r11
adcx rbx, r10
seto r11b
movzx r10, byte [ rsp + 0x590 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r10, rdx
adox rdi, [ rsp + 0x5d0 ]
adox rcx, r14
mov r10, 0x0 
adcx r13, r10
mov r14, [ rsp + 0x5f8 ]
adox r14, [ rsp + 0x5f0 ]
clc
movzx r11, r11b
adcx r11, rdx
adcx rdi, rbp
adcx r15, rcx
adcx r8, r14
mov r11, [ rsp + 0x5e0 ]
adox r11, [ rsp + 0x608 ]
mov rbp, [ rsp + 0x600 ]
adox rbp, [ rsp + 0x5e8 ]
adcx r12, r11
mov rcx, [ rsp + 0x5c8 ]
seto r14b
movzx r11, byte [ rsp + 0x628 ]
inc rdx
mov r10, -0x1 
adox r11, r10
adox rcx, [ rsp + 0x620 ]
adcx r9, rbp
mov r11, [ rsp + 0x578 ]
setc bpl
movzx rdx, byte [ rsp + 0x618 ]
clc
adcx rdx, r10
adcx r11, [ rsp + 0x108 ]
mov rdx, [ rsp + 0x100 ]
mov r10, 0x0 
adcx rdx, r10
clc
mov r10, -0x1 
movzx r14, r14b
adcx r14, r10
adcx rcx, r11
movzx r14, byte [ rsp + 0x610 ]
mov r11, 0x0 
adox r14, r11
dec r11
movzx rbp, bpl
adox rbp, r11
adox rcx, rbx
adcx rdx, r14
setc r10b
seto bl
mov rbp, rdi
mov r14, 0xffffffffffffffff 
sub rbp, r14
mov r11, r15
sbb r11, r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rbx, bl
adox rbx, r14
adox rdx, r13
movzx r13, r10b
mov rbx, 0x0 
adox r13, rbx
mov r10, r8
mov rbx, 0xffffffffffffffff 
sbb r10, rbx
mov r14, r12
mov rbx, 0xfdc1767ae2ffffff 
sbb r14, rbx
mov rbx, r9
mov [ rsp + 0x630 ], r10
mov r10, 0x7bc65c783158aea3 
sbb rbx, r10
mov r10, rcx
mov [ rsp + 0x638 ], rbx
mov rbx, 0x6cfc5fd681c52056 
sbb r10, rbx
mov rbx, rdx
mov [ rsp + 0x640 ], rbp
mov rbp, 0x2341f27177344 
sbb rbx, rbp
sbb r13, 0x00000000
cmovc r14, r12
cmovc r10, rcx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], r14
cmovc r11, r15
mov r15, [ rsp + 0x640 ]
cmovc r15, rdi
mov rdi, [ rsp + 0x630 ]
cmovc rdi, r8
mov [ r13 + 0x0 ], r15
cmovc rbx, rdx
mov [ r13 + 0x8 ], r11
mov [ r13 + 0x30 ], rbx
mov r8, [ rsp + 0x638 ]
cmovc r8, r9
mov [ r13 + 0x20 ], r8
mov [ r13 + 0x10 ], rdi
mov [ r13 + 0x28 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1736
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4471
; seed 2580196678671110 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10163784 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=38, initial num_batches=31): 175643 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.017281260601366578
; number reverted permutation / tried permutation: 55932 / 90113 =62.069%
; number reverted decision / tried decision: 52396 / 89886 =58.292%
; validated in 230.029s
