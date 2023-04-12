SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1560
mov rax, rdx
mov rdx, [ rdx + 0x30 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r12
mulx r12, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r11
mulx r11, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r15
mulx r15, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], r10
mulx r10, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r14
mulx r14, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], rbx
mulx rbx, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x48 ], r13
mov [ rsp + 0x50 ], rbp
mulx rbp, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r13
mulx r13, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], rbp
mulx rbp, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r10
mulx r10, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r10
mov [ rsp + 0x90 ], r8
mulx r8, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r10
mov [ rsp + 0xa0 ], rdi
mulx rdi, r10, [ rax + 0x28 ]
xor rdx, rdx
adox r13, r8
adox r9, rbp
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r9
mov [ rsp + 0xb0 ], r13
mulx r13, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], r13
mulx r13, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], r8
mulx r8, r10, [ rsi + 0x28 ]
adcx r12, r11
adcx r14, r15
mov rdx, [ rax + 0x8 ]
mulx r15, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r12
mulx r12, r14, [ rax + 0x0 ]
seto dl
mov [ rsp + 0xe8 ], r14
mov r14, -0x2 
inc r14
adox r11, r12
adcx rcx, rbx
seto bl
inc r14
adox r10, [ rsp + 0xa0 ]
mov r12b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], rcx
mulx rcx, r14, [ rax + 0x30 ]
mov rdx, [ rsp + 0x78 ]
mov [ rsp + 0xf8 ], r10
setc r10b
clc
adcx rdx, [ rsp + 0x80 ]
mov [ rsp + 0x100 ], r11
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x108 ], r10b
mov byte [ rsp + 0x110 ], r12b
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x118 ], r11
mov [ rsp + 0x120 ], rcx
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r13
mov [ rsp + 0x130 ], rdi
mulx rdi, r13, [ rax + 0x10 ]
setc dl
clc
mov [ rsp + 0x138 ], rdi
mov rdi, -0x1 
movzx rbx, bl
adcx rbx, rdi
adcx r15, r11
adox r13, r8
seto r8b
inc rdi
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox r10, [ rsp + 0x50 ]
adox r12, [ rsp + 0x70 ]
mov rdx, [ rax + 0x8 ]
mulx rdi, r11, [ rsi + 0x10 ]
adcx rcx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], r15
mulx r15, rcx, [ rsi + 0x0 ]
adcx r9, [ rsp + 0x30 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x158 ], r9
mov [ rsp + 0x160 ], r12
mulx r12, r9, rcx
mov rdx, [ rsp + 0x90 ]
adox rdx, [ rsp + 0x68 ]
mov [ rsp + 0x168 ], r10
mov r10, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], r9
mulx r9, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x180 ], r10
mov [ rsp + 0x188 ], rbx
mulx rbx, r10, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x190 ], rbx
mov rbx, -0x2 
inc rbx
adox r15, [ rsp + 0x10 ]
adox rbp, [ rsp + 0x8 ]
seto bl
mov [ rsp + 0x198 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r12, [ rsp + 0x88 ]
adox r14, r9
mov rdx, 0x7bc65c783158aea3 
mulx rbp, r9, rcx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1a0 ], r14
mov [ rsp + 0x1a8 ], r12
mulx r12, r14, rcx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x1b0 ], rbp
mov [ rsp + 0x1b8 ], r9
mulx r9, rbp, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1c0 ], r9
mov [ rsp + 0x1c8 ], rbp
mulx rbp, r9, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1d0 ], r12
mov [ rsp + 0x1d8 ], r14
mulx r14, r12, rcx
mov rdx, r12
mov [ rsp + 0x1e0 ], rbp
setc bpl
clc
adcx rdx, rcx
setc dl
clc
adcx r11, r13
adcx r10, rdi
mov dil, dl
mov rdx, [ rax + 0x18 ]
mulx rcx, r13, [ rsi + 0x10 ]
mov rdx, r12
mov [ rsp + 0x1e8 ], r10
setc r10b
clc
adcx rdx, r14
mov [ rsp + 0x1f0 ], r11
mov r11, [ rsp + 0x130 ]
mov byte [ rsp + 0x1f8 ], bpl
seto bpl
mov byte [ rsp + 0x200 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r8, r8b
adox r8, rbx
adox r11, [ rsp + 0x138 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, rbx
adcx r15, rdx
mov rdx, [ rax + 0x20 ]
mulx rbx, rdi, [ rsi + 0x10 ]
setc dl
clc
adcx r15, [ rsp + 0x98 ]
mov [ rsp + 0x208 ], r11
setc r11b
clc
mov byte [ rsp + 0x210 ], dl
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r13, [ rsp + 0x190 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x218 ], r13
mulx r13, r10, [ rax + 0x20 ]
adcx rdi, rcx
mov rdx, [ rsp + 0x40 ]
adox rdx, [ rsp + 0x128 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], rdi
mov byte [ rsp + 0x228 ], r11b
mulx r11, rdi, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x230 ], rcx
mov [ rsp + 0x238 ], r13
mulx r13, rcx, r15
movzx rdx, bpl
mov [ rsp + 0x240 ], r13
mov r13, [ rsp + 0x120 ]
lea rdx, [ rdx + r13 ]
adox r9, [ rsp + 0x38 ]
mov r13, r14
seto bpl
mov [ rsp + 0x248 ], r9
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox r13, r12
adcx rbx, [ rsp + 0x20 ]
mov r12, rdx
mov rdx, [ rax + 0x30 ]
mulx r9, r8, [ rsi + 0x10 ]
setc dl
mov [ rsp + 0x250 ], r12
movzx r12, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x258 ], rbx
mov rbx, -0x1 
adcx r12, rbx
adcx rdi, [ rsp + 0xd0 ]
mov r12b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x260 ], rdi
mulx rdi, rbx, [ rax + 0x28 ]
adcx r10, r11
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x268 ], r10
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x270 ], r13
mov [ rsp + 0x278 ], r10
mulx r10, r13, r15
mov rdx, [ rsp + 0xc8 ]
adcx rdx, [ rsp + 0x238 ]
mov [ rsp + 0x280 ], rdx
seto dl
mov [ rsp + 0x288 ], r10
movzx r10, byte [ rsp + 0x1f8 ]
mov [ rsp + 0x290 ], r13
mov r13, 0x0 
dec r13
adox r10, r13
adox rbx, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0x0 ]
mov r10, [ rsp - 0x10 ]
setc r13b
clc
mov [ rsp + 0x298 ], rdi
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r10, [ rsp + 0x1e0 ]
seto bpl
inc rdi
mov rdi, -0x1 
movzx rdx, dl
adox rdx, rdi
adox r14, [ rsp + 0x1d8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2a0 ], r10
mulx r10, rdi, [ rax + 0x18 ]
setc dl
clc
mov [ rsp + 0x2a8 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r8, [ rsp + 0x18 ]
mov r12, 0x0 
adcx r9, r12
mov rbx, rcx
clc
adcx rbx, r15
mov bl, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x2b0 ], r9
mulx r9, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2b8 ], r8
mov byte [ rsp + 0x2c0 ], bpl
mulx rbp, r8, [ rax + 0x20 ]
mov rdx, [ rsp + 0x1b8 ]
adox rdx, [ rsp + 0x1d0 ]
mov [ rsp + 0x2c8 ], rdx
setc dl
clc
mov [ rsp + 0x2d0 ], r9
mov r9, -0x1 
movzx r13, r13b
adcx r13, r9
adcx r11, [ rsp + 0xb8 ]
mov r13b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2d8 ], r11
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x278 ]
mov byte [ rsp + 0x2e0 ], r13b
mov r13, 0x0 
adcx rdx, r13
mov [ rsp + 0x2e8 ], rdx
mov rdx, rcx
clc
adcx rdx, [ rsp + 0x240 ]
adcx rcx, [ rsp + 0x240 ]
seto r13b
mov [ rsp + 0x2f0 ], rcx
movzx rcx, byte [ rsp + 0x110 ]
mov [ rsp + 0x2f8 ], rdx
mov rdx, 0x0 
dec rdx
adox rcx, rdx
adox rdi, [ rsp + 0x28 ]
adox r9, r10
adox r12, r11
seto cl
movzx r10, byte [ rsp + 0x108 ]
inc rdx
mov r11, -0x1 
adox r10, r11
adox r8, [ rsp - 0x18 ]
adox rbp, [ rsp - 0x20 ]
mov r10, [ rsp + 0x198 ]
seto dl
movzx r11, byte [ rsp + 0x210 ]
mov [ rsp + 0x300 ], rbp
mov rbp, 0x0 
dec rbp
adox r11, rbp
adox r10, [ rsp + 0x270 ]
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r15
mov [ rsp + 0x308 ], r8
mulx r8, rbp, r11
movzx r11, bl
mov [ rsp + 0x310 ], r12
mov r12, [ rsp - 0x30 ]
lea r11, [ r11 + r12 ]
setc r12b
movzx rbx, byte [ rsp + 0x228 ]
clc
mov [ rsp + 0x318 ], r11
mov r11, -0x1 
adcx rbx, r11
adcx r10, [ rsp + 0xb0 ]
adox r14, [ rsp + 0x260 ]
setc bl
clc
movzx r12, r12b
adcx r12, r11
adcx rbp, [ rsp + 0x240 ]
setc r12b
clc
movzx rbx, bl
adcx rbx, r11
adcx r14, [ rsp + 0xa8 ]
seto bl
inc r11
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox r8, [ rsp + 0x290 ]
mov r12, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x320 ], r8
mulx r8, r11, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x328 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r15, r15b
adox r15, r8
adox r11, [ rsp - 0x38 ]
setc r15b
movzx r8, byte [ rsp + 0x2e0 ]
clc
mov [ rsp + 0x330 ], r11
mov r11, -0x1 
adcx r8, r11
adcx r10, [ rsp + 0x2f8 ]
mov r8, [ rsp + 0x2d0 ]
setc r11b
clc
mov [ rsp + 0x338 ], rbp
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx r8, [ rsp + 0x60 ]
mov rcx, [ rsp + 0x58 ]
mov rbp, 0x0 
adcx rcx, rbp
mov rbp, [ rsp + 0x268 ]
clc
mov [ rsp + 0x340 ], rcx
mov rcx, -0x1 
movzx rbx, bl
adcx rbx, rcx
adcx rbp, [ rsp + 0x2c8 ]
setc bl
clc
movzx r11, r11b
adcx r11, rcx
adcx r14, [ rsp + 0x2f0 ]
setc r11b
clc
adcx r10, [ rsp + 0x188 ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x348 ], r8
mov byte [ rsp + 0x350 ], r11b
mulx r11, r8, rcx
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mov [ rsp + 0x358 ], r14
mov [ rsp + 0x360 ], r9
mulx r9, r14, r10
mov rdx, 0x2341f27177344 
mov [ rsp + 0x368 ], rdi
mov [ rsp + 0x370 ], rbp
mulx rbp, rdi, rcx
setc cl
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx r8, [ rsp + 0x288 ]
mov r12, r14
seto dl
mov [ rsp + 0x378 ], rbp
mov rbp, -0x2 
inc rbp
adox r12, r9
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov byte [ rsp + 0x380 ], r10b
mov [ rsp + 0x388 ], r8
mulx r8, r10, rbp
mov rbp, r14
adox rbp, r9
adcx rdi, r11
mov r11, 0x2341f27177344 
mov [ rsp + 0x390 ], rdi
mov [ rsp + 0x398 ], rbp
mulx rbp, rdi, r11
setc r11b
clc
adcx r14, rdx
mov r14, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x3a0 ], r11b
mov [ rsp + 0x3a8 ], r12
mulx r12, r11, r14
movzx r14, byte [ rsp + 0x2c0 ]
mov [ rsp + 0x3b0 ], rbp
mov rbp, [ rsp - 0x40 ]
lea r14, [ r14 + rbp ]
adox r10, r9
mov rbp, [ rsp + 0x1b0 ]
setc r9b
clc
mov [ rsp + 0x3b8 ], r14
mov r14, -0x1 
movzx r13, r13b
adcx r13, r14
adcx rbp, [ rsp + 0x178 ]
mov r13, 0x7bc65c783158aea3 
mov [ rsp + 0x3c0 ], r10
mulx r10, r14, r13
adox r14, r8
mov rdx, [ rsp + 0x170 ]
adcx rdx, [ rsp + 0x1c8 ]
adox r11, r10
mov r8, [ rsp + 0x1c0 ]
mov r10, 0x0 
adcx r8, r10
adox rdi, r12
clc
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx rbp, [ rsp + 0x280 ]
mov rbx, [ rsp + 0x370 ]
seto r10b
inc r12
mov r12, -0x1 
movzx r15, r15b
adox r15, r12
adox rbx, [ rsp + 0x368 ]
adox rbp, [ rsp + 0x360 ]
mov r15, [ rsp + 0x358 ]
seto r12b
mov r13, 0x0 
dec r13
movzx rcx, cl
adox rcx, r13
adox r15, [ rsp + 0x1f0 ]
movzx rcx, r10b
mov r13, [ rsp + 0x3b0 ]
lea rcx, [ rcx + r13 ]
seto r13b
movzx r10, byte [ rsp + 0x350 ]
mov [ rsp + 0x3c8 ], rcx
mov rcx, 0x0 
dec rcx
adox r10, rcx
adox rbx, [ rsp + 0x338 ]
adcx rdx, [ rsp + 0x2d8 ]
adox rbp, [ rsp + 0x320 ]
adcx r8, [ rsp + 0x2e8 ]
setc r10b
clc
movzx r9, r9b
adcx r9, rcx
adcx r15, [ rsp + 0x3a8 ]
seto r9b
inc rcx
adox r15, [ rsp - 0x8 ]
seto cl
mov [ rsp + 0x3d0 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r13, r13b
adox r13, rdi
adox rbx, [ rsp + 0x1e8 ]
adcx rbx, [ rsp + 0x398 ]
adox rbp, [ rsp + 0x218 ]
seto r13b
inc rdi
mov rdi, -0x1 
movzx r12, r12b
adox r12, rdi
adox rdx, [ rsp + 0x310 ]
adox r8, [ rsp + 0x348 ]
mov r12, 0x7bc65c783158aea3 
xchg rdx, r15
mov byte [ rsp + 0x3d8 ], r10b
mulx r10, rdi, r12
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x3e0 ], r10
mov [ rsp + 0x3e8 ], rdi
mulx rdi, r10, r12
seto r12b
mov [ rsp + 0x3f0 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r15, [ rsp + 0x388 ]
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x3f8 ], r10
mulx r10, rdi, r9
adcx rbp, [ rsp + 0x3c0 ]
mov r9, rdi
mov byte [ rsp + 0x400 ], r12b
setc r12b
clc
adcx r9, r10
mov [ rsp + 0x408 ], r9
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x410 ], r11
mov [ rsp + 0x418 ], r14
mulx r14, r11, r9
seto r9b
mov [ rsp + 0x420 ], r14
mov r14, 0x0 
dec r14
movzx rcx, cl
adox rcx, r14
adox rbx, [ rsp + 0x118 ]
adox rbp, [ rsp + 0x168 ]
setc cl
clc
movzx r13, r13b
adcx r13, r14
adcx r15, [ rsp + 0x220 ]
setc r13b
clc
movzx r9, r9b
adcx r9, r14
adcx r8, [ rsp + 0x390 ]
seto r9b
inc r14
mov r14, -0x1 
movzx r12, r12b
adox r12, r14
adox r15, [ rsp + 0x418 ]
setc r12b
clc
movzx r13, r13b
adcx r13, r14
adcx r8, [ rsp + 0x258 ]
adox r8, [ rsp + 0x410 ]
mov r13, rdi
setc r14b
clc
adcx r13, rdx
seto r13b
mov [ rsp + 0x428 ], r11
mov r11, 0x0 
dec r11
movzx r9, r9b
adox r9, r11
adox r15, [ rsp + 0x160 ]
adcx rbx, [ rsp + 0x408 ]
seto r9b
inc r11
adox rbx, [ rsp + 0xe8 ]
mov r11, r10
mov [ rsp + 0x430 ], rbx
seto bl
mov [ rsp + 0x438 ], r15
mov r15, 0x0 
dec r15
movzx rcx, cl
adox rcx, r15
adox r11, rdi
adcx r11, rbp
setc dil
clc
movzx r9, r9b
adcx r9, r15
adcx r8, [ rsp + 0x180 ]
movzx rcx, byte [ rsp + 0x3d8 ]
seto bpl
movzx r9, byte [ rsp + 0x400 ]
inc r15
mov r15, -0x1 
adox r9, r15
adox rcx, [ rsp + 0x340 ]
movzx r9, byte [ rsp + 0x3a0 ]
mov r15, [ rsp + 0x378 ]
lea r9, [ r9 + r15 ]
setc r15b
clc
mov [ rsp + 0x440 ], r11
mov r11, -0x1 
movzx r12, r12b
adcx r12, r11
adcx rcx, r9
seto r12b
inc r11
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox rcx, [ rsp + 0x2b8 ]
setc r14b
clc
movzx rbp, bpl
adcx rbp, r9
adcx r10, [ rsp + 0x428 ]
seto bpl
inc r9
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rcx, [ rsp + 0x3d0 ]
mov r13, [ rsp + 0x3e8 ]
adcx r13, [ rsp + 0x420 ]
movzx r9, r14b
movzx r12, r12b
lea r9, [ r9 + r12 ]
seto r12b
inc r11
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox r10, [ rsp + 0x438 ]
adox r13, r8
mov rdi, 0xffffffffffffffff 
mov r8, rdx
mov rdx, [ rsp + 0x430 ]
mulx r14, r11, rdi
mov rdi, r11
mov [ rsp + 0x448 ], r13
seto r13b
mov [ rsp + 0x450 ], r10
mov r10, -0x2 
inc r10
adox rdi, r14
setc r10b
clc
mov byte [ rsp + 0x458 ], r13b
mov r13, -0x1 
movzx rbp, bpl
adcx rbp, r13
adcx r9, [ rsp + 0x2b0 ]
seto bpl
inc r13
mov r13, -0x1 
movzx r12, r12b
adox r12, r13
adox r9, [ rsp + 0x3c8 ]
seto r12b
inc r13
mov r13, -0x1 
movzx r15, r15b
adox r15, r13
adox rcx, [ rsp + 0x1a8 ]
mov r15, 0x7bc65c783158aea3 
mov [ rsp + 0x460 ], r9
mulx r9, r13, r15
mov r15, r14
mov [ rsp + 0x468 ], rcx
seto cl
mov [ rsp + 0x470 ], rdi
mov rdi, 0x0 
dec rdi
movzx rbp, bpl
adox rbp, rdi
adox r15, r11
mov rbp, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x478 ], cl
mulx rcx, rdi, rbp
adox rdi, r14
adox r13, rcx
mov r14, [ rsp + 0x3f8 ]
setc cl
clc
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx r14, [ rsp + 0x3e0 ]
mov r10, 0x2341f27177344 
xchg rdx, r10
mov [ rsp + 0x480 ], r13
mulx r13, rbp, r8
adcx rbp, [ rsp + 0x3f0 ]
mov r8, [ rsp + 0x440 ]
setc dl
clc
mov [ rsp + 0x488 ], rdi
mov rdi, -0x1 
movzx rbx, bl
adcx rbx, rdi
adcx r8, [ rsp + 0x100 ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, r10
mov [ rsp + 0x490 ], rbp
mulx rbp, rdi, rbx
movzx rbx, r12b
movzx rcx, cl
lea rbx, [ rbx + rcx ]
adox rdi, r9
mov rcx, 0x2341f27177344 
mulx r9, r12, rcx
adox r12, rbp
mov rbp, [ rsp + 0x450 ]
adcx rbp, [ rsp + 0x150 ]
setc cl
clc
adcx r11, rdx
mov r11, 0x0 
adox r9, r11
mov rdx, [ rsp + 0x148 ]
dec r11
movzx rcx, cl
adox rcx, r11
adox rdx, [ rsp + 0x448 ]
adcx r8, [ rsp + 0x470 ]
setc cl
movzx r11, byte [ rsp + 0x458 ]
clc
mov [ rsp + 0x498 ], r9
mov r9, -0x1 
adcx r11, r9
adcx r14, [ rsp + 0x468 ]
setc r11b
clc
movzx rcx, cl
adcx rcx, r9
adcx rbp, r15
adox r14, [ rsp + 0x158 ]
seto r15b
inc r9
adox r8, [ rsp - 0x48 ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x4a0 ], r12
mulx r12, r9, r8
movzx rdx, r10b
lea rdx, [ rdx + r13 ]
mov r13, [ rsp + 0x460 ]
setc r10b
mov [ rsp + 0x4a8 ], r12
movzx r12, byte [ rsp + 0x478 ]
clc
mov [ rsp + 0x4b0 ], rdi
mov rdi, -0x1 
adcx r12, rdi
adcx r13, [ rsp + 0x1a0 ]
adox rbp, [ rsp + 0xf8 ]
adcx rbx, [ rsp + 0x250 ]
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x4b8 ], rbp
mulx rbp, rdi, r8
setc dl
clc
mov [ rsp + 0x4c0 ], rbp
mov rbp, -0x1 
movzx r11, r11b
adcx r11, rbp
adcx r13, [ rsp + 0x490 ]
adcx r12, rbx
mov r11, 0xffffffffffffffff 
xchg rdx, r8
mulx rbp, rbx, r11
movzx r11, r8b
mov [ rsp + 0x4c8 ], rdi
mov rdi, 0x0 
adcx r11, rdi
clc
mov r8, -0x1 
movzx r10, r10b
adcx r10, r8
adcx rcx, [ rsp + 0x488 ]
mov r10, rbx
setc r8b
clc
adcx r10, rdx
setc r10b
clc
mov rdi, -0x1 
movzx r8, r8b
adcx r8, rdi
adcx r14, [ rsp + 0x480 ]
mov r8, rbx
seto dil
mov [ rsp + 0x4d0 ], r14
mov r14, -0x2 
inc r14
adox r8, rbp
adox rbx, rbp
adox r9, rbp
seto bpl
inc r14
mov r14, -0x1 
movzx r15, r15b
adox r15, r14
adox r13, [ rsp + 0x2a8 ]
adox r12, [ rsp + 0x298 ]
adox r11, [ rsp + 0x3b8 ]
adcx r13, [ rsp + 0x4b0 ]
adcx r12, [ rsp + 0x4a0 ]
adcx r11, [ rsp + 0x498 ]
seto r15b
adc r15b, 0x0
movzx r15, r15b
add r10b, 0x7F
adox r8, [ rsp + 0x4b8 ]
adcx r8, [ rsp - 0x28 ]
movzx r10, byte [ rsp + 0x380 ]
mov r14, [ rsp + 0x328 ]
lea r10, [ r10 + r14 ]
mov r14, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x4d8 ], r10
mov byte [ rsp + 0x4e0 ], r15b
mulx r15, r10, r8
mov rdx, 0x2341f27177344 
mov [ rsp + 0x4e8 ], r15
mov [ rsp + 0x4f0 ], r10
mulx r10, r15, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x4f8 ], r10
mov [ rsp + 0x500 ], r15
mulx r15, r10, r8
setc dl
clc
mov [ rsp + 0x508 ], r9
mov r9, -0x1 
movzx rdi, dil
adcx rdi, r9
adcx rcx, [ rsp + 0x140 ]
mov rdi, r10
seto r9b
mov [ rsp + 0x510 ], r11
mov r11, -0x2 
inc r11
adox rdi, r15
mov r11, [ rsp + 0x4d0 ]
adcx r11, [ rsp + 0x208 ]
adcx r13, [ rsp + 0x230 ]
mov [ rsp + 0x518 ], rdi
mov rdi, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x520 ], r13
mov [ rsp + 0x528 ], r11
mulx r11, r13, rdi
mov rdi, r10
adox rdi, r15
mov [ rsp + 0x530 ], rdi
seto dil
mov byte [ rsp + 0x538 ], r14b
mov r14, 0x0 
dec r14
movzx rbp, bpl
adox rbp, r14
adox r13, [ rsp + 0x4a8 ]
adcx r12, [ rsp + 0x248 ]
adox r11, [ rsp + 0x4c8 ]
setc bpl
clc
movzx r9, r9b
adcx r9, r14
adcx rcx, rbx
setc bl
movzx r9, byte [ rsp + 0x538 ]
clc
adcx r9, r14
adcx rcx, [ rsp + 0xe0 ]
mov r9, [ rsp + 0x510 ]
setc r14b
clc
mov byte [ rsp + 0x540 ], dil
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r9, [ rsp + 0x2a0 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x548 ], r9
mulx r9, rdi, rbp
mov rbp, [ rsp + 0x528 ]
mov [ rsp + 0x550 ], r9
seto r9b
mov [ rsp + 0x558 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox rbp, [ rsp + 0x508 ]
seto bl
inc rdi
adox r10, rdx
setc r10b
clc
mov rdi, -0x1 
movzx rbx, bl
adcx rbx, rdi
adcx r13, [ rsp + 0x520 ]
adox rcx, [ rsp + 0x518 ]
mov rbx, 0x2341f27177344 
xchg rdx, r8
mov byte [ rsp + 0x560 ], r10b
mulx r10, rdi, rbx
setc dl
seto bl
mov [ rsp + 0x568 ], r11
mov r11, rcx
mov [ rsp + 0x570 ], r12
mov r12, 0xffffffffffffffff 
sub r11, r12
mov r12, 0x0 
dec r12
movzx r14, r14b
adox r14, r12
adox rbp, [ rsp + 0xd8 ]
setc r14b
clc
movzx r9, r9b
adcx r9, r12
adcx rdi, [ rsp + 0x4c0 ]
mov r9, 0x0 
adcx r10, r9
adox r13, [ rsp + 0xf0 ]
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov [ rsp + 0x578 ], r11
mulx r11, r12, r9
mov rdx, [ rsp + 0x570 ]
clc
mov r9, -0x1 
movzx r8, r8b
adcx r8, r9
adcx rdx, [ rsp + 0x568 ]
adox rdx, [ rsp + 0x308 ]
setc r8b
movzx r9, byte [ rsp + 0x540 ]
clc
mov byte [ rsp + 0x580 ], r14b
mov r14, -0x1 
adcx r9, r14
adcx r15, r12
seto r9b
inc r14
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rbp, [ rsp + 0x530 ]
adox r15, r13
adcx r11, [ rsp + 0x4f0 ]
mov rbx, [ rsp + 0x4e8 ]
adcx rbx, [ rsp + 0x558 ]
mov r13, [ rsp + 0x318 ]
seto r14b
movzx r12, byte [ rsp + 0x560 ]
mov [ rsp + 0x588 ], r15
mov r15, 0x0 
dec r15
mov [ rsp + 0x590 ], rbp
movzx rbp, byte [ rsp + 0x4e0 ]
adox r12, r15
adox r13, rbp
mov rbp, [ rsp + 0x550 ]
adcx rbp, [ rsp + 0x500 ]
seto r12b
inc r15
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox rdi, [ rsp + 0x548 ]
adox r10, r13
movzx r8, r12b
mov r13, 0x0 
adox r8, r13
inc r15
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox rdx, r11
setc r14b
clc
movzx r9, r9b
adcx r9, r13
adcx rdi, [ rsp + 0x300 ]
adox rbx, rdi
setc r9b
seto r11b
movzx r12, byte [ rsp + 0x580 ]
add r12, -0x1
mov r12, [ rsp + 0x590 ]
mov rdi, 0xffffffffffffffff 
sbb r12, rdi
dec r15
movzx r9, r9b
adox r9, r15
adox r10, [ rsp + 0x330 ]
adox r8, [ rsp + 0x4d8 ]
movzx r13, r14b
mov r9, [ rsp + 0x4f8 ]
lea r13, [ r13 + r9 ]
seto r9b
mov r14, [ rsp + 0x588 ]
sbb r14, rdi
inc r15
mov r15, -0x1 
movzx r11, r11b
adox r11, r15
adox r10, rbp
adox r13, r8
seto bpl
mov r11, rdx
mov r8, 0xfdc1767ae2ffffff 
sbb r11, r8
movzx r15, bpl
movzx r9, r9b
lea r15, [ r15 + r9 ]
mov r9, rbx
mov rbp, 0x7bc65c783158aea3 
sbb r9, rbp
mov rdi, r10
mov r8, 0x6cfc5fd681c52056 
sbb rdi, r8
mov rbp, r13
mov r8, 0x2341f27177344 
sbb rbp, r8
sbb r15, 0x00000000
cmovc r9, rbx
cmovc rdi, r10
mov r15, [ rsp + 0x578 ]
cmovc r15, rcx
cmovc r12, [ rsp + 0x590 ]
cmovc r14, [ rsp + 0x588 ]
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x28 ], rdi
mov [ rcx + 0x20 ], r9
cmovc r11, rdx
mov [ rcx + 0x18 ], r11
cmovc rbp, r13
mov [ rcx + 0x8 ], r12
mov [ rcx + 0x10 ], r14
mov [ rcx + 0x30 ], rbp
mov [ rcx + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1560
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3119
; seed 0355724693291898 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 77996 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=29, initial num_batches=31): 1183 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01516744448433253
; number reverted permutation / tried permutation: 264 / 489 =53.988%
; number reverted decision / tried decision: 246 / 510 =48.235%
; validated in 361.72s
