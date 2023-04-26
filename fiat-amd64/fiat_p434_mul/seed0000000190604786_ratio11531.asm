SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1792
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
test al, al
adox r15, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x28 ], r9
mulx r9, r14, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r14
mulx r14, r9, r10
mov rdx, r9
adcx rdx, r10
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], rdi
mulx rdi, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rdi
mulx rdi, rbx, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], rbx
mulx rbx, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rdi
mulx rdi, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], rdi
mov [ rsp + 0x58 ], rbx
mulx rbx, rdi, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], rdi
mulx rdi, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x80 ], rbx
mov rbx, -0x2 
inc rbx
adox rbp, r11
mov r11, r9
setc bl
clc
adcx r11, r14
adcx r9, r14
mov [ rsp + 0x88 ], rdi
mov dil, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], r9
mulx r9, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xa0 ], r15
mov byte [ rsp + 0xa8 ], dil
mulx rdi, r15, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0xb0 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox rbp, r11
seto bl
inc rcx
adox r13, rbp
setc r11b
clc
mov rbp, -0x1 
movzx rdx, dl
adcx rdx, rbp
adcx r12, r15
adcx r8, rdi
mov rdx, 0xfdc1767ae2ffffff 
mulx rdi, r15, r13
mov rdx, [ rsi + 0x30 ]
mulx rbp, rcx, [ rax + 0x20 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], rcx
mulx rcx, rbp, r13
seto dl
mov [ rsp + 0xc8 ], rcx
mov rcx, -0x2 
inc rcx
adox r9, [ rsp + 0xb0 ]
mov cl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r9
mov [ rsp + 0xd8 ], rbp
mulx rbp, r9, [ rax + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r9
mulx r9, rbp, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], r9
mov [ rsp + 0xf8 ], r8
mulx r8, r9, r13
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x100 ], cl
mov [ rsp + 0x108 ], r12
mulx r12, rcx, [ rsi + 0x0 ]
mov rdx, r9
mov [ rsp + 0x110 ], r12
setc r12b
clc
adcx rdx, r8
mov [ rsp + 0x118 ], rcx
mov rcx, r9
adcx rcx, r8
adcx r15, r8
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x120 ], r15
mov byte [ rsp + 0x128 ], r12b
mulx r12, r15, r13
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x130 ], r12
mov [ rsp + 0x138 ], rcx
mulx rcx, r12, r13
adcx r12, rdi
seto dil
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox r14, rbp
mov r11, [ rsp + 0x108 ]
seto bpl
inc rdx
mov rdx, -0x1 
movzx rbx, bl
adox rbx, rdx
adox r11, [ rsp + 0x98 ]
seto bl
movzx rdx, byte [ rsp + 0x100 ]
mov byte [ rsp + 0x140 ], dil
mov rdi, 0x0 
dec rdi
adox rdx, rdi
adox r11, [ rsp + 0x90 ]
adcx r15, rcx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x148 ], r15
movzx r15, byte [ rsp + 0xa8 ]
mov [ rsp + 0x150 ], r12
mov r12, 0x0 
dec r12
adox r15, r12
adox rcx, [ rsp - 0x8 ]
seto r15b
inc r12
adox r9, r13
adox r8, r11
mov r9b, dl
mov rdx, [ rax + 0x0 ]
mulx r11, r13, [ rsi + 0x10 ]
seto dl
dec r12
movzx rbx, bl
adox rbx, r12
adox r14, [ rsp + 0xf8 ]
setc bl
clc
adcx r13, r8
mov r8, 0xffffffffffffffff 
xchg rdx, r13
mov byte [ rsp + 0x158 ], bl
mulx rbx, r12, r8
setc r8b
clc
mov [ rsp + 0x160 ], r11
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx r14, rcx
mov r9, 0xfdc1767ae2ffffff 
mulx r11, rcx, r9
mov r9, r12
mov [ rsp + 0x168 ], r11
seto r11b
mov [ rsp + 0x170 ], rcx
mov rcx, -0x2 
inc rcx
adox r9, rbx
seto cl
mov [ rsp + 0x178 ], r9
mov r9, 0x0 
dec r9
movzx r13, r13b
adox r13, r9
adox r14, [ rsp + 0x138 ]
mov r13, [ rsp - 0x10 ]
setc r9b
mov byte [ rsp + 0x180 ], cl
movzx rcx, byte [ rsp + 0x128 ]
clc
mov [ rsp + 0x188 ], r14
mov r14, -0x1 
adcx rcx, r14
adcx r13, [ rsp + 0xe8 ]
mov rcx, rdx
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x190 ], r8b
mulx r8, r14, [ rsi + 0x8 ]
setc dl
clc
mov byte [ rsp + 0x198 ], r9b
mov r9, -0x1 
movzx r15, r15b
adcx r15, r9
adcx rdi, r14
adcx r8, [ rsp + 0x28 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r10
mulx r9, r14, r15
mov r15, [ rsp + 0xe0 ]
mov [ rsp + 0x1a0 ], r9
seto r9b
mov [ rsp + 0x1a8 ], r8
mov r8, 0x0 
dec r8
movzx r10, r10b
adox r10, r8
adox r15, [ rsp + 0x118 ]
mov r10, 0x7bc65c783158aea3 
mov byte [ rsp + 0x1b0 ], r9b
mulx r9, r8, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1b8 ], rdi
mulx rdi, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c0 ], rdi
mov [ rsp + 0x1c8 ], r15
mulx r15, rdi, [ rax + 0x30 ]
setc dl
clc
mov [ rsp + 0x1d0 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx r8, [ rsp + 0xf0 ]
adox r10, [ rsp + 0x110 ]
adcx r14, r9
setc bpl
clc
movzx r11, r11b
adcx r11, r15
adcx r13, r8
mov r11, [ rsp + 0x20 ]
setc r9b
clc
movzx rdx, dl
adcx rdx, r15
adcx r11, [ rsp + 0x8 ]
adcx rdi, [ rsp + 0x0 ]
seto dl
inc r15
mov r8, -0x1 
movzx r9, r9b
adox r9, r8
adox r14, [ rsp + 0x1c8 ]
setc r9b
movzx r15, byte [ rsp + 0x198 ]
clc
adcx r15, r8
adcx r13, [ rsp + 0x1b8 ]
adcx r14, [ rsp + 0x1a8 ]
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1d8 ], rdi
mulx rdi, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x1e0 ], r15b
mov byte [ rsp + 0x1e8 ], r9b
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x1f0 ], rdi
setc dil
clc
adcx rdx, [ rsp + 0x160 ]
mov [ rsp + 0x1f8 ], r9
setc r9b
mov [ rsp + 0x200 ], r11
movzx r11, byte [ rsp + 0x1b0 ]
clc
mov byte [ rsp + 0x208 ], dil
mov rdi, -0x1 
adcx r11, rdi
adcx r13, [ rsp + 0x120 ]
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x210 ], r15
mulx r15, rdi, [ rax + 0x0 ]
adcx r14, [ rsp + 0x150 ]
setc dl
mov [ rsp + 0x218 ], r14
movzx r14, byte [ rsp + 0x190 ]
clc
mov [ rsp + 0x220 ], r15
mov r15, -0x1 
adcx r14, r15
adcx r11, [ rsp + 0x188 ]
mov r14, r12
setc r15b
clc
adcx r14, rcx
adcx r11, [ rsp + 0x178 ]
setc r14b
clc
mov byte [ rsp + 0x228 ], dl
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx r8, [ rsp + 0x80 ]
setc r9b
clc
adcx rdi, r11
setc r11b
clc
movzx r15, r15b
adcx r15, rdx
adcx r13, r8
mov r15, 0xffffffffffffffff 
mov rdx, rdi
mulx r8, rdi, r15
mov r15, [ rsp + 0x38 ]
mov byte [ rsp + 0x230 ], r9b
setc r9b
clc
mov byte [ rsp + 0x238 ], r11b
mov r11, -0x1 
movzx rbp, bpl
adcx rbp, r11
adcx r15, [ rsp + 0x1a0 ]
mov rbp, rdi
setc r11b
clc
adcx rbp, rdx
mov rbp, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x240 ], r9b
mov [ rsp + 0x248 ], r13
mulx r13, r9, rbp
mov rbp, rdi
mov [ rsp + 0x250 ], r13
seto r13b
mov [ rsp + 0x258 ], r9
mov r9, -0x2 
inc r9
adox rbp, r8
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x260 ], rbp
mov byte [ rsp + 0x268 ], r14b
mulx r14, rbp, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x270 ], r14
mov r14, 0x0 
dec r14
movzx r13, r13b
adox r13, r14
adox r10, r15
mov r13, r8
seto r15b
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox r13, rdi
mov rdi, [ rsp + 0x220 ]
seto dl
inc r14
adox rdi, [ rsp + 0x210 ]
mov r14, 0x7bc65c783158aea3 
xchg rdx, r9
mov byte [ rsp + 0x278 ], r15b
mov [ rsp + 0x280 ], r13
mulx r13, r15, r14
mov r14, rbx
mov [ rsp + 0x288 ], r13
seto r13b
mov [ rsp + 0x290 ], r15
movzx r15, byte [ rsp + 0x180 ]
mov byte [ rsp + 0x298 ], r9b
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox r15, r9
adox r14, r12
setc r12b
movzx r15, byte [ rsp + 0x208 ]
clc
adcx r15, r9
adcx r10, [ rsp + 0x200 ]
seto r15b
movzx r9, byte [ rsp + 0x228 ]
mov byte [ rsp + 0x2a0 ], r12b
mov r12, 0x0 
dec r12
adox r9, r12
adox r10, [ rsp + 0x148 ]
movzx r9, r11b
mov r12, [ rsp + 0x30 ]
lea r9, [ r9 + r12 ]
seto r12b
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox rbp, [ rsp + 0x1f8 ]
setc r13b
movzx r11, byte [ rsp + 0x268 ]
clc
mov byte [ rsp + 0x2a8 ], r12b
mov r12, -0x1 
adcx r11, r12
adcx r14, [ rsp + 0x248 ]
setc r11b
movzx r12, byte [ rsp + 0x238 ]
clc
mov byte [ rsp + 0x2b0 ], r13b
mov r13, -0x1 
adcx r12, r13
adcx r14, rdi
mov r12, 0x7bc65c783158aea3 
xchg rdx, rcx
mulx r13, rdi, r12
mov r12, [ rsp + 0x130 ]
mov [ rsp + 0x2b8 ], r9
seto r9b
mov [ rsp + 0x2c0 ], rbp
movzx rbp, byte [ rsp + 0x158 ]
mov [ rsp + 0x2c8 ], r10
mov r10, 0x0 
dec r10
adox rbp, r10
adox r12, [ rsp + 0xd8 ]
seto bpl
movzx r10, byte [ rsp + 0x2a0 ]
mov [ rsp + 0x2d0 ], r12
mov r12, 0x0 
dec r12
adox r10, r12
adox r14, [ rsp + 0x260 ]
movzx r10, bpl
mov r12, [ rsp + 0xc8 ]
lea r10, [ r10 + r12 ]
mov r12, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x2d8 ], r10
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2e0 ], r10
mov byte [ rsp + 0x2e8 ], r11b
mulx r11, r10, r12
seto dl
mov [ rsp + 0x2f0 ], r11
mov r11, -0x2 
inc r11
adox r14, [ rsp + 0x58 ]
setc r11b
clc
mov byte [ rsp + 0x2f8 ], dl
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx rbx, [ rsp + 0x170 ]
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x300 ], r11b
mulx r11, r15, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x308 ], rbx
movzx rbx, byte [ rsp + 0x230 ]
mov byte [ rsp + 0x310 ], r9b
mov r9, 0x0 
dec r9
adox rbx, r9
adox r15, [ rsp + 0x1f0 ]
adox rbp, r11
mov rbx, 0xffffffffffffffff 
xchg rdx, r14
mulx r9, r11, rbx
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x318 ], r11
mov [ rsp + 0x320 ], r9
mulx r9, r11, [ rsi + 0x18 ]
adcx rdi, [ rsp + 0x168 ]
adcx r10, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x328 ], r10
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x330 ], r14b
mov [ rsp + 0x338 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x340 ], rdi
movzx rdi, byte [ rsp + 0x310 ]
mov [ rsp + 0x348 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rdi, r14
adox r13, [ rsp + 0x270 ]
adox r11, r10
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx r14, r10, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x350 ], r14
mov [ rsp + 0x358 ], r10
mulx r10, r14, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x360 ], r11
movzx r11, byte [ rsp + 0x298 ]
mov byte [ rsp + 0x368 ], dil
mov rdi, 0x0 
dec rdi
adox r11, rdi
adox r8, [ rsp + 0x258 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, rdi
adcx r9, [ rsp + 0x68 ]
setc dl
movzx rdi, byte [ rsp + 0x240 ]
clc
mov [ rsp + 0x370 ], r9
mov r9, -0x1 
adcx rdi, r9
adcx r15, [ rsp + 0x218 ]
seto dil
movzx r9, byte [ rsp + 0x2e8 ]
mov byte [ rsp + 0x378 ], dl
mov rdx, 0x0 
dec rdx
adox r9, rdx
adox r15, [ rsp + 0x308 ]
adcx rbp, [ rsp + 0x2c8 ]
setc r9b
movzx rdx, byte [ rsp + 0x300 ]
clc
mov byte [ rsp + 0x380 ], dil
mov rdi, -0x1 
adcx rdx, rdi
adcx r15, [ rsp + 0x2c0 ]
adox rbp, [ rsp + 0x338 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x388 ], r9b
mulx r9, rdi, [ rax + 0x28 ]
adcx r13, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox r14, [ rsp + 0x50 ]
adox r10, [ rsp + 0x348 ]
setc bpl
mov [ rsp + 0x390 ], r9
movzx r9, byte [ rsp + 0x2f8 ]
clc
mov byte [ rsp + 0x398 ], dl
mov rdx, -0x1 
adcx r9, rdx
adcx r15, [ rsp + 0x280 ]
seto r9b
movzx rdx, byte [ rsp + 0x368 ]
mov byte [ rsp + 0x3a0 ], bpl
mov rbp, 0x0 
dec rbp
adox rdx, rbp
adox rdi, [ rsp + 0x2e0 ]
adcx r8, r13
setc dl
movzx r13, byte [ rsp + 0x330 ]
clc
adcx r13, rbp
adcx r15, r14
adcx r10, r8
mov r13, [ rsp + 0x318 ]
mov r14, r13
setc r8b
clc
adcx r14, [ rsp + 0x320 ]
mov rbp, r13
adcx rbp, [ rsp + 0x320 ]
mov byte [ rsp + 0x3a8 ], r8b
setc r8b
clc
adcx r13, rbx
adcx r14, r15
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov byte [ rsp + 0x3b0 ], bl
mulx rbx, r15, r13
mov r13, [ rsp + 0x340 ]
mov [ rsp + 0x3b8 ], rbx
seto bl
mov [ rsp + 0x3c0 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r13, [ rsp + 0x18 ]
adcx rbp, r10
movzx r9, byte [ rsp + 0x1e8 ]
mov r10, [ rsp + 0x1d0 ]
lea r9, [ r9 + r10 ]
movzx r10, byte [ rsp + 0x1e0 ]
mov rdi, [ rsp + 0x1c0 ]
lea r10, [ r10 + rdi ]
setc dil
clc
mov [ rsp + 0x3c8 ], r13
mov r13, -0x1 
movzx r8, r8b
adcx r8, r13
adcx r15, [ rsp + 0x320 ]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x3d0 ], r15
mulx r15, r13, [ rax + 0x0 ]
setc dl
clc
adcx r13, r14
seto r14b
mov byte [ rsp + 0x3d8 ], dl
movzx rdx, byte [ rsp + 0x278 ]
mov byte [ rsp + 0x3e0 ], dil
mov rdi, 0x0 
dec rdi
adox rdx, rdi
adox r10, [ rsp + 0x2b8 ]
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x3e8 ], r14b
mulx r14, rdi, r13
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x3f0 ], r14
mov byte [ rsp + 0x3f8 ], bl
mulx rbx, r14, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x400 ], rbx
mov [ rsp + 0x408 ], r14
mulx r14, rbx, [ rax + 0x8 ]
mov rdx, rdi
mov [ rsp + 0x410 ], r14
setc r14b
clc
adcx rdx, r13
setc dl
clc
adcx rbx, r15
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov byte [ rsp + 0x418 ], r15b
mov byte [ rsp + 0x420 ], r11b
mulx r11, r15, r13
mov rdx, 0x2341f27177344 
mov [ rsp + 0x428 ], r11
mov [ rsp + 0x430 ], r15
mulx r15, r11, r13
setc dl
clc
mov [ rsp + 0x438 ], r15
mov r15, -0x1 
movzx r14, r14b
adcx r14, r15
adcx rbp, rbx
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r13
mulx r15, rbx, r14
setc dl
movzx r14, byte [ rsp + 0x2b0 ]
clc
mov [ rsp + 0x440 ], r11
mov r11, -0x1 
adcx r14, r11
adcx r10, [ rsp + 0x1d8 ]
mov r14, 0x2341f27177344 
xchg rdx, r12
mov [ rsp + 0x448 ], r15
mulx r15, r11, r14
seto dl
movzx rdx, dl
adcx rdx, r9
movzx r9, byte [ rsp + 0x420 ]
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r9, r14
adox r11, [ rsp + 0x2f0 ]
mov r9, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x450 ], rbx
mulx rbx, r14, [ rsi + 0x28 ]
seto dl
mov byte [ rsp + 0x458 ], r12b
movzx r12, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x460 ], rbx
mov rbx, 0x0 
dec rbx
adox r12, rbx
adox r10, [ rsp + 0x2d0 ]
adox r9, [ rsp + 0x2d8 ]
setc r12b
movzx rbx, byte [ rsp + 0x388 ]
clc
mov [ rsp + 0x468 ], r14
mov r14, -0x1 
adcx rbx, r14
adcx r10, [ rsp + 0x3c0 ]
setc bl
movzx r14, byte [ rsp + 0x398 ]
clc
mov byte [ rsp + 0x470 ], r13b
mov r13, -0x1 
adcx r14, r13
adcx r10, [ rsp + 0x328 ]
mov r14b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x478 ], r10
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x390 ]
mov [ rsp + 0x480 ], r15
setc r15b
mov byte [ rsp + 0x488 ], r14b
movzx r14, byte [ rsp + 0x3f8 ]
clc
mov [ rsp + 0x490 ], r11
mov r11, -0x1 
adcx r14, r11
adcx rdx, [ rsp - 0x28 ]
seto r14b
movzx r11, byte [ rsp + 0x378 ]
mov byte [ rsp + 0x498 ], r15b
mov r15, 0x0 
dec r15
adox r11, r15
adox r13, [ rsp + 0x60 ]
setc r11b
clc
movzx rbx, bl
adcx rbx, r15
adcx r9, rdx
mov rbx, rdi
setc dl
clc
adcx rbx, [ rsp + 0x3f0 ]
seto r15b
mov [ rsp + 0x4a0 ], r13
movzx r13, byte [ rsp + 0x418 ]
mov byte [ rsp + 0x4a8 ], dl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r13, rdx
adox rbp, rbx
adcx rdi, [ rsp + 0x3f0 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, r13, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x4b0 ], rdi
mov rdi, -0x2 
inc rdi
adox rbp, [ rsp + 0xa0 ]
movzx rdi, r14b
movzx r12, r12b
lea rdi, [ rdi + r12 ]
movzx r12, r15b
lea r12, [ r12 + r10 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rbp
mulx r15, r10, r14
mov r14, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4b8 ], r15
mov byte [ rsp + 0x4c0 ], bpl
mulx rbp, r15, r14
mov r14, r10
mov [ rsp + 0x4c8 ], rbp
setc bpl
clc
adcx r14, rdx
mov r14, [ rsp + 0x250 ]
mov [ rsp + 0x4d0 ], r15
setc r15b
mov byte [ rsp + 0x4d8 ], bpl
movzx rbp, byte [ rsp + 0x380 ]
clc
mov [ rsp + 0x4e0 ], r12
mov r12, -0x1 
adcx rbp, r12
adcx r14, [ rsp + 0x290 ]
mov rbp, 0x2341f27177344 
mov byte [ rsp + 0x4e8 ], r15b
mulx r15, r12, rbp
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov [ rsp + 0x4f0 ], r15
mov [ rsp + 0x4f8 ], r12
mulx r12, r15, rcx
adcx r15, [ rsp + 0x288 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x500 ], r15
mov [ rsp + 0x508 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x510 ], r14
mov [ rsp + 0x518 ], r15
mulx r15, r14, rcx
seto cl
movzx rdx, byte [ rsp + 0x498 ]
mov [ rsp + 0x520 ], rbx
mov rbx, 0x0 
dec rbx
adox rdx, rbx
adox r9, [ rsp + 0x490 ]
movzx rdx, r11b
mov rbx, [ rsp - 0x30 ]
lea rdx, [ rdx + rbx ]
adcx r14, r12
seto bl
movzx r11, byte [ rsp + 0x4a8 ]
mov r12, 0x0 
dec r12
adox r11, r12
adox rdi, rdx
mov r11, 0x0 
adcx r15, r11
movzx rdx, byte [ rsp + 0x488 ]
mov r11, [ rsp + 0x480 ]
lea rdx, [ rdx + r11 ]
clc
movzx rbx, bl
adcx rbx, r12
adcx rdi, rdx
setc r11b
movzx rbx, byte [ rsp + 0x470 ]
clc
adcx rbx, r12
adcx r13, [ rsp + 0x410 ]
mov rdx, [ rax + 0x20 ]
mulx r12, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x528 ], cl
mov [ rsp + 0x530 ], r13
mulx r13, rcx, [ rax + 0x28 ]
mov rdx, [ rsp + 0x520 ]
adcx rdx, [ rsp + 0x78 ]
mov [ rsp + 0x538 ], rdx
mov rdx, [ rsp + 0x10 ]
mov [ rsp + 0x540 ], r15
seto r15b
mov [ rsp + 0x548 ], r14
movzx r14, byte [ rsp + 0x3e8 ]
mov byte [ rsp + 0x550 ], r11b
mov r11, 0x0 
dec r11
adox r14, r11
adox rdx, [ rsp - 0x38 ]
adox rcx, [ rsp - 0x40 ]
adcx rbx, [ rsp + 0x70 ]
adcx r12, [ rsp + 0x468 ]
adox r13, [ rsp + 0x518 ]
mov r14, [ rsp + 0x360 ]
seto r11b
mov [ rsp + 0x558 ], r12
movzx r12, byte [ rsp + 0x3a0 ]
mov [ rsp + 0x560 ], rbx
mov rbx, 0x0 
dec rbx
adox r12, rbx
adox r14, [ rsp + 0x478 ]
mov r12, [ rsp + 0x460 ]
adcx r12, [ rsp + 0x48 ]
seto bl
mov [ rsp + 0x568 ], r12
movzx r12, byte [ rsp + 0x3b0 ]
mov [ rsp + 0x570 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r12, r13
adox r14, [ rsp + 0x508 ]
setc r12b
clc
movzx rbx, bl
adcx rbx, r13
adcx r9, [ rsp + 0x370 ]
adcx rdi, [ rsp + 0x4a0 ]
movzx rbx, r11b
mov r13, [ rsp + 0x510 ]
lea rbx, [ rbx + r13 ]
adox r9, [ rsp + 0x500 ]
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x578 ], rbx
mulx rbx, r11, [ rax + 0x10 ]
movzx rdx, r15b
mov [ rsp + 0x580 ], rcx
movzx rcx, byte [ rsp + 0x550 ]
lea rdx, [ rdx + rcx ]
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x588 ], rbx
mulx rbx, rcx, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x590 ], rbx
mov [ rsp + 0x598 ], rcx
mulx rcx, rbx, [ rsi + 0x30 ]
adcx r15, [ rsp + 0x4e0 ]
adox rdi, [ rsp + 0x548 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x5a0 ], rcx
mov [ rsp + 0x5a8 ], rdi
mulx rdi, rcx, r8
adox r15, [ rsp + 0x540 ]
seto dl
mov [ rsp + 0x5b0 ], rdi
movzx rdi, byte [ rsp + 0x3a8 ]
mov [ rsp + 0x5b8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rdi, r15
adox r14, [ rsp + 0x3c8 ]
setc dil
movzx r15, byte [ rsp + 0x3e0 ]
clc
mov byte [ rsp + 0x5c0 ], dl
mov rdx, -0x1 
adcx r15, rdx
adcx r14, [ rsp + 0x3d0 ]
movzx r15, r12b
mov rdx, [ rsp + 0x40 ]
lea r15, [ r15 + rdx ]
setc dl
movzx r12, byte [ rsp + 0x458 ]
clc
mov [ rsp + 0x5c8 ], r15
mov r15, -0x1 
adcx r12, r15
adcx r14, [ rsp + 0x530 ]
adox r13, r9
setc r12b
movzx r9, byte [ rsp + 0x140 ]
clc
adcx r9, r15
adcx r11, [ rsp - 0x48 ]
mov r9, [ rsp + 0x598 ]
adcx r9, [ rsp + 0x588 ]
mov r15, [ rsp + 0x590 ]
adcx r15, [ rsp + 0xc0 ]
adcx rbx, [ rsp + 0xb8 ]
mov [ rsp + 0x5d0 ], rbx
mov rbx, [ rsp + 0x5a8 ]
adox rbx, [ rsp + 0x580 ]
mov [ rsp + 0x5d8 ], r15
mov r15, 0x2341f27177344 
xchg rdx, r15
mov [ rsp + 0x5e0 ], r9
mov [ rsp + 0x5e8 ], r11
mulx r11, r9, r8
setc r8b
movzx rdx, byte [ rsp + 0x3d8 ]
clc
mov byte [ rsp + 0x5f0 ], dil
mov rdi, -0x1 
adcx rdx, rdi
adcx rcx, [ rsp + 0x3b8 ]
setc dl
clc
movzx r15, r15b
adcx r15, rdi
adcx r13, rcx
mov r15, [ rsp + 0x570 ]
adox r15, [ rsp + 0x5b8 ]
seto cl
movzx rdi, byte [ rsp + 0x4c0 ]
mov [ rsp + 0x5f8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rdi, r15
adox r14, [ rsp + 0x4b0 ]
mov rdi, [ rsp + 0x5b0 ]
seto r15b
mov byte [ rsp + 0x600 ], cl
mov rcx, 0x0 
dec rcx
movzx rdx, dl
adox rdx, rcx
adox rdi, [ rsp + 0x358 ]
adcx rdi, rbx
mov rbx, [ rsp - 0x18 ]
seto dl
inc rcx
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox rbx, [ rsp + 0x5a0 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, rcx
adcx r9, [ rsp + 0x350 ]
mov rdx, [ rsp + 0x3f0 ]
seto cl
mov [ rsp + 0x608 ], rbx
movzx rbx, byte [ rsp + 0x4d8 ]
mov [ rsp + 0x610 ], r14
mov r14, 0x0 
dec r14
adox rbx, r14
adox rdx, [ rsp + 0x450 ]
mov rbx, [ rsp + 0x430 ]
adox rbx, [ rsp + 0x448 ]
mov r14, 0x0 
adcx r11, r14
clc
mov r14, -0x1 
movzx r12, r12b
adcx r12, r14
adcx r13, [ rsp + 0x538 ]
seto r12b
inc r14
mov r14, -0x1 
movzx r15, r15b
adox r15, r14
adox r13, rdx
mov r15, [ rsp + 0x428 ]
seto dl
inc r14
mov r14, -0x1 
movzx r12, r12b
adox r12, r14
adox r15, [ rsp + 0x408 ]
adcx rdi, [ rsp + 0x560 ]
mov r12, [ rsp + 0x400 ]
adox r12, [ rsp + 0x440 ]
movzx r14, byte [ rsp + 0x5c0 ]
mov byte [ rsp + 0x618 ], cl
movzx rcx, byte [ rsp + 0x5f0 ]
lea r14, [ r14 + rcx ]
seto cl
mov [ rsp + 0x620 ], r12
mov r12, 0x0 
dec r12
movzx r8, r8b
adox r8, r12
adox r9, [ rsp + 0x5f8 ]
mov r8, [ rsp + 0x610 ]
seto r12b
mov byte [ rsp + 0x628 ], cl
movzx rcx, byte [ rsp + 0x528 ]
mov [ rsp + 0x630 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox rcx, r15
adox r8, [ rsp + 0xd0 ]
adcx r9, [ rsp + 0x558 ]
seto cl
movzx r15, byte [ rsp + 0x600 ]
mov [ rsp + 0x638 ], r9
mov r9, 0x0 
dec r9
adox r15, r9
adox r14, [ rsp + 0x578 ]
seto r15b
inc r9
mov r9, -0x1 
movzx r12, r12b
adox r12, r9
adox r14, r11
setc r11b
clc
movzx rcx, cl
adcx rcx, r9
adcx r13, [ rsp + 0x5e8 ]
setc r12b
clc
movzx r11, r11b
adcx r11, r9
adcx r14, [ rsp + 0x568 ]
mov rcx, r10
seto r11b
inc r9
adox rcx, [ rsp + 0x4b8 ]
adox r10, [ rsp + 0x4b8 ]
setc r9b
clc
mov byte [ rsp + 0x640 ], r15b
mov r15, -0x1 
movzx rdx, dl
adcx rdx, r15
adcx rdi, rbx
seto bl
movzx rdx, byte [ rsp + 0x4e8 ]
inc r15
mov r15, -0x1 
adox rdx, r15
adox r8, rcx
mov rdx, 0x6cfc5fd681c52056 
mulx r15, rcx, rbp
mov rdx, [ rsp + 0x630 ]
adcx rdx, [ rsp + 0x638 ]
adcx r14, [ rsp + 0x620 ]
mov [ rsp + 0x648 ], r8
mov r8, 0x7bc65c783158aea3 
xchg rdx, r8
mov byte [ rsp + 0x650 ], r9b
mov byte [ rsp + 0x658 ], r11b
mulx r11, r9, rbp
mov rbp, [ rsp + 0x4b8 ]
seto dl
mov [ rsp + 0x660 ], r10
mov r10, 0x0 
dec r10
movzx rbx, bl
adox rbx, r10
adox rbp, [ rsp + 0x4d0 ]
setc bl
clc
movzx r12, r12b
adcx r12, r10
adcx rdi, [ rsp + 0x5e0 ]
adcx r8, [ rsp + 0x5d8 ]
adcx r14, [ rsp + 0x5d0 ]
adox r9, [ rsp + 0x4c8 ]
adox rcx, r11
adox r15, [ rsp + 0x4f8 ]
movzx r12, byte [ rsp + 0x628 ]
mov r11, [ rsp + 0x438 ]
lea r12, [ r12 + r11 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, r10
adcx r13, [ rsp + 0x660 ]
movzx rdx, byte [ rsp + 0x658 ]
movzx r10, byte [ rsp + 0x640 ]
lea rdx, [ rdx + r10 ]
setc r10b
mov [ rsp + 0x668 ], r13
movzx r13, byte [ rsp + 0x650 ]
clc
mov [ rsp + 0x670 ], r15
mov r15, -0x1 
adcx r13, r15
adcx rdx, [ rsp + 0x5c8 ]
seto r13b
inc r15
mov r15, -0x1 
movzx rbx, bl
adox rbx, r15
adox rdx, r12
seto bl
adc bl, 0x0
movzx rbx, bl
add r10b, 0xFF
adcx rdi, rbp
adcx r9, r8
movzx r11, r11b
adox r11, r15
adox rdx, [ rsp + 0x608 ]
movzx rbp, byte [ rsp + 0x618 ]
mov r8, [ rsp - 0x20 ]
lea rbp, [ rbp + r8 ]
adcx rcx, r14
adcx rdx, [ rsp + 0x670 ]
movzx r8, r13b
mov r11, [ rsp + 0x4f0 ]
lea r8, [ r8 + r11 ]
movzx r11, bl
adox r11, rbp
adcx r8, r11
setc r14b
seto r13b
mov r12, [ rsp + 0x648 ]
mov r10, 0xffffffffffffffff 
sub r12, r10
mov rbx, [ rsp + 0x668 ]
sbb rbx, r10
mov rbp, rdi
sbb rbp, r10
mov r11, r9
mov r15, 0xfdc1767ae2ffffff 
sbb r11, r15
mov r15, rcx
mov r10, 0x7bc65c783158aea3 
sbb r15, r10
mov r10, rdx
mov [ rsp + 0x678 ], r15
mov r15, 0x6cfc5fd681c52056 
sbb r10, r15
movzx r15, r14b
movzx r13, r13b
lea r15, [ r15 + r13 ]
mov r13, r8
mov r14, 0x2341f27177344 
sbb r13, r14
sbb r15, 0x00000000
cmovc r12, [ rsp + 0x648 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], r12
cmovc r13, r8
cmovc rbx, [ rsp + 0x668 ]
cmovc rbp, rdi
mov [ r15 + 0x10 ], rbp
cmovc r10, rdx
mov [ r15 + 0x28 ], r10
mov [ r15 + 0x30 ], r13
cmovc r11, r9
mov [ r15 + 0x8 ], rbx
mov rdi, [ rsp + 0x678 ]
cmovc rdi, rcx
mov [ r15 + 0x18 ], r11
mov [ r15 + 0x20 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1792
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1531
; seed 3823685221732821 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11360274 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 166643 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.014668924358690645
; number reverted permutation / tried permutation: 50774 / 89891 =56.484%
; number reverted decision / tried decision: 46194 / 90108 =51.265%
; validated in 278.896s
