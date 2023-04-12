SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1800
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r11
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r10
mulx r10, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r10
mov [ rsp + 0x20 ], r11
mulx r11, r10, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], r10
mulx r10, r11, rcx
mov rdx, r11
test al, al
adox rdx, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x48 ], rbx
mov [ rsp + 0x50 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, r11
adcx rdx, r10
mov [ rsp + 0x58 ], r9
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], r13
mulx r13, rdi, [ rsi + 0x0 ]
setc dl
clc
adcx rbx, r12
setc r12b
clc
adcx rdi, r8
adox r9, rdi
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], rbx
mulx rbx, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], rbx
mulx rbx, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], rbx
mov [ rsp + 0x90 ], rdi
mulx rdi, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], r15
mulx r15, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xa8 ], r15
mov byte [ rsp + 0xb0 ], r8b
mulx r8, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], r15
mulx r15, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], r14
mulx r14, r15, [ rax + 0x18 ]
adcx r8, r13
setc dl
clc
mov r13, -0x1 
movzx r12, r12b
adcx r12, r13
adcx rbp, rbx
adcx r15, rdi
setc r12b
clc
adcx r9, [ rsp + 0xd0 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mulx r13, rdi, r9
mov rdx, rdi
mov [ rsp + 0xd8 ], r15
setc r15b
clc
adcx rdx, r9
mov rdx, 0x2341f27177344 
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r14
mulx r14, rbp, r9
mov rdx, rdi
mov [ rsp + 0xf0 ], r14
setc r14b
clc
adcx rdx, r13
mov byte [ rsp + 0xf8 ], r12b
mov r12, r10
mov [ rsp + 0x100 ], rbp
seto bpl
mov byte [ rsp + 0x108 ], bl
movzx rbx, byte [ rsp + 0xb0 ]
mov [ rsp + 0x110 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox rbx, rdx
adox r12, r11
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx rbx, r11, rcx
adox r11, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x118 ], r11
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r10
mov byte [ rsp + 0x128 ], r14b
mulx r14, r10, [ rax + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x130 ], r14
mov byte [ rsp + 0x138 ], r15b
mulx r15, r14, rcx
seto dl
mov [ rsp + 0x140 ], r15
mov r15, -0x2 
inc r15
adox r10, r11
adcx rdi, r13
mov r11, [ rsp + 0xa8 ]
seto r15b
mov [ rsp + 0x148 ], r10
mov r10, -0x2 
inc r10
adox r11, [ rsp + 0xa0 ]
setc r10b
clc
mov [ rsp + 0x150 ], rdi
mov rdi, -0x1 
movzx rdx, dl
adcx rdx, rdi
adcx rbx, [ rsp + 0x98 ]
setc dl
clc
movzx rbp, bpl
adcx rbp, rdi
adcx r8, r12
seto bpl
inc rdi
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox r14, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, [ rax + 0x20 ]
seto dl
mov byte [ rsp + 0x158 ], r10b
movzx r10, byte [ rsp + 0x138 ]
mov [ rsp + 0x160 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r10, r14
adox r8, r11
mov r10b, dl
mov rdx, [ rax + 0x18 ]
mulx r14, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x58 ]
mov byte [ rsp + 0x168 ], r10b
setc r10b
clc
mov [ rsp + 0x170 ], rbx
mov rbx, -0x1 
movzx rbp, bpl
adcx rbp, rbx
adcx rdx, [ rsp + 0x60 ]
setc bpl
movzx rbx, byte [ rsp + 0x128 ]
clc
mov [ rsp + 0x178 ], rdx
mov rdx, -0x1 
adcx rbx, rdx
adcx r8, [ rsp + 0x110 ]
seto bl
inc rdx
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox r11, [ rsp + 0x40 ]
mov rbp, 0x2341f27177344 
mov rdx, rbp
mov [ rsp + 0x180 ], r11
mulx r11, rbp, rcx
setc cl
clc
adcx r8, [ rsp + 0x38 ]
mov rdx, [ rsp + 0x0 ]
mov byte [ rsp + 0x188 ], cl
seto cl
mov [ rsp + 0x190 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r15, r15b
adox r15, r11
adox rdx, [ rsp + 0x130 ]
seto r15b
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox r14, [ rsp + 0x10 ]
mov rcx, [ rsp - 0x8 ]
seto r11b
mov [ rsp + 0x198 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r15, r15b
adox r15, rdx
adox rcx, [ rsp + 0x20 ]
mov r15, 0xffffffffffffffff 
mov rdx, r8
mov [ rsp + 0x1a0 ], rcx
mulx rcx, r8, r15
mov r15, [ rsp + 0xc8 ]
mov byte [ rsp + 0x1a8 ], r11b
seto r11b
mov [ rsp + 0x1b0 ], r8
movzx r8, byte [ rsp + 0x108 ]
mov [ rsp + 0x1b8 ], rcx
mov rcx, 0x0 
dec rcx
adox r8, rcx
adox r15, [ rsp + 0xc0 ]
adox rdi, [ rsp + 0xb8 ]
adox r12, [ rsp - 0x20 ]
mov r8, 0x7bc65c783158aea3 
mov byte [ rsp + 0x1c0 ], r11b
mulx r11, rcx, r8
seto r8b
mov [ rsp + 0x1c8 ], r11
mov r11, 0x0 
dec r11
movzx r10, r10b
adox r10, r11
adox r15, [ rsp + 0x118 ]
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1d0 ], rcx
mulx rcx, r11, r10
mov r10, 0x2341f27177344 
mov [ rsp + 0x1d8 ], rcx
mov [ rsp + 0x1e0 ], r11
mulx r11, rcx, r10
mov r10, 0x6cfc5fd681c52056 
mov [ rsp + 0x1e8 ], r11
mov [ rsp + 0x1f0 ], rcx
mulx rcx, r11, r10
mov r10, 0x7bc65c783158aea3 
xchg rdx, r9
mov [ rsp + 0x1f8 ], rcx
mov [ rsp + 0x200 ], r11
mulx r11, rcx, r10
setc r10b
clc
mov [ rsp + 0x208 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx r15, [ rsp + 0x178 ]
adox rdi, [ rsp + 0x170 ]
adcx rdi, [ rsp + 0x180 ]
adox r12, [ rsp + 0x160 ]
adcx r14, r12
mov rbx, [ rsp - 0x28 ]
seto r12b
inc r11
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox rbx, [ rsp - 0x30 ]
setc r8b
movzx r11, byte [ rsp + 0x168 ]
clc
mov [ rsp + 0x210 ], r14
mov r14, -0x1 
adcx r11, r14
adcx rbp, [ rsp + 0x140 ]
mov r11, [ rsp - 0x38 ]
mov r14, 0x0 
adox r11, r14
mov r14, [ rsp + 0x190 ]
adc r14, 0x0
add r12b, 0xFF
adcx rbx, rbp
mov r12, [ rsp + 0x1b0 ]
mov rbp, r12
adox rbp, [ rsp + 0x1b8 ]
mov [ rsp + 0x218 ], rbp
setc bpl
mov [ rsp + 0x220 ], rcx
movzx rcx, byte [ rsp + 0x188 ]
clc
mov [ rsp + 0x228 ], r14
mov r14, -0x1 
adcx rcx, r14
adcx r15, [ rsp + 0x150 ]
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x230 ], r11
mulx r11, r14, rcx
mov rcx, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x238 ], r11
mov byte [ rsp + 0x240 ], bpl
mulx rbp, r11, [ rsi + 0x8 ]
mov rdx, r12
adox rdx, [ rsp + 0x1b8 ]
mov [ rsp + 0x248 ], rdx
seto dl
mov [ rsp + 0x250 ], rbp
movzx rbp, byte [ rsp + 0x158 ]
mov [ rsp + 0x258 ], rbx
mov rbx, 0x0 
dec rbx
adox rbp, rbx
adox r13, r14
mov rbp, [ rsp + 0x1b8 ]
setc r14b
clc
movzx rdx, dl
adcx rdx, rbx
adcx rbp, [ rsp + 0x1e0 ]
seto dl
inc rbx
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox r15, [ rsp + 0x70 ]
seto r10b
movzx rbx, byte [ rsp + 0x1a8 ]
mov [ rsp + 0x260 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox rbx, rbp
adox r11, [ rsp + 0x8 ]
seto bl
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox rdi, r13
mov r14, [ rsp + 0x1d0 ]
adcx r14, [ rsp + 0x1d8 ]
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x268 ], r14
mulx r14, rbp, [ rax + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x270 ], rdi
mov byte [ rsp + 0x278 ], r10b
mulx r10, rdi, rcx
mov rcx, [ rsp + 0x200 ]
adcx rcx, [ rsp + 0x1c8 ]
seto dl
mov [ rsp + 0x280 ], rcx
mov rcx, 0x0 
dec rcx
movzx r8, r8b
adox r8, rcx
adox r11, [ rsp + 0x258 ]
mov r8, [ rsp + 0x250 ]
seto cl
mov [ rsp + 0x288 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rbx, bl
adox rbx, r11
adox r8, [ rsp + 0x30 ]
mov rbx, [ rsp + 0x230 ]
seto r11b
mov [ rsp + 0x290 ], r15
movzx r15, byte [ rsp + 0x240 ]
mov [ rsp + 0x298 ], r14
mov r14, 0x0 
dec r14
adox r15, r14
adox rbx, [ rsp + 0x228 ]
mov r15, [ rsp + 0x220 ]
seto r14b
mov [ rsp + 0x2a0 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r13, r13b
adox r13, rbp
adox r15, [ rsp + 0x238 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, rbp
adcx r15, [ rsp + 0x210 ]
setc dl
clc
movzx rcx, cl
adcx rcx, rbp
adcx rbx, r8
adox rdi, [ rsp + 0x208 ]
movzx rcx, r11b
mov r8, [ rsp + 0x28 ]
lea rcx, [ rcx + r8 ]
adox r10, [ rsp + 0x100 ]
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbp, r11, [ rax + 0x30 ]
movzx rdx, r14b
adcx rdx, rcx
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x2a8 ], r13b
mulx r13, rcx, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x2b0 ], r13
movzx r13, byte [ rsp + 0xf8 ]
mov [ rsp + 0x2b8 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox r13, rbp
adox rcx, [ rsp + 0xe8 ]
mov r13b, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x2c0 ], rcx
mulx rcx, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2c8 ], rbp
mov [ rsp + 0x2d0 ], r14
mulx r14, rbp, [ rax + 0x28 ]
setc dl
clc
adcx rcx, [ rsp - 0x40 ]
mov [ rsp + 0x2d8 ], rcx
mov cl, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x2e0 ], r10
mov [ rsp + 0x2e8 ], rbx
mulx rbx, r10, [ rax + 0x10 ]
mov rdx, [ rsp + 0x2a0 ]
mov byte [ rsp + 0x2f0 ], cl
setc cl
clc
adcx rdx, [ rsp + 0x80 ]
mov [ rsp + 0x2f8 ], rdx
movzx rdx, r13b
mov byte [ rsp + 0x300 ], cl
mov rcx, [ rsp + 0xf0 ]
lea rdx, [ rdx + rcx ]
adcx r10, [ rsp + 0x298 ]
adcx rbx, [ rsp - 0x10 ]
seto cl
mov r13, -0x2 
inc r13
adox r12, r9
mov r12, [ rsp + 0x290 ]
adox r12, [ rsp + 0x218 ]
seto r9b
inc r13
adox r12, [ rsp + 0x78 ]
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x308 ], rbx
mov [ rsp + 0x310 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x318 ], cl
mov [ rsp + 0x320 ], r13
mulx r13, rcx, r12
adcx rbx, [ rsp - 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x328 ], r13
mov [ rsp + 0x330 ], rbx
mulx rbx, r13, r12
adcx rbp, r10
mov r10, [ rsp + 0x270 ]
seto dl
mov [ rsp + 0x338 ], rbp
movzx rbp, byte [ rsp + 0x278 ]
mov [ rsp + 0x340 ], rcx
mov rcx, 0x0 
dec rcx
adox rbp, rcx
adox r10, [ rsp + 0xe0 ]
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x348 ], r13
mulx r13, rcx, [ rax + 0x28 ]
setc dl
clc
mov [ rsp + 0x350 ], r13
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx r10, [ rsp + 0x248 ]
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x358 ], r10
mulx r10, r13, r9
seto r9b
mov byte [ rsp + 0x360 ], bpl
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r12, r12b
adox r12, rbp
adox r14, r11
setc r11b
clc
movzx r8, r8b
adcx r8, rbp
adcx rdi, [ rsp + 0x288 ]
seto r8b
inc rbp
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox r15, [ rsp + 0xd8 ]
mov r9, [ rsp + 0x2e8 ]
adcx r9, [ rsp + 0x2e0 ]
mov rbp, [ rsp + 0x2d0 ]
adcx rbp, [ rsp + 0x320 ]
movzx r12, r8b
mov [ rsp + 0x368 ], r14
mov r14, [ rsp + 0x2b8 ]
lea r12, [ r12 + r14 ]
movzx r14, byte [ rsp + 0x2f0 ]
mov r8, 0x0 
adcx r14, r8
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x370 ], r12
mov [ rsp + 0x378 ], r14
mulx r14, r12, [ rsi + 0x30 ]
adox rdi, [ rsp + 0x2c0 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x380 ], rbp
mov [ rsp + 0x388 ], r14
mulx r14, rbp, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x390 ], r12
mov [ rsp + 0x398 ], rdi
mulx rdi, r12, [ rax + 0x10 ]
mov rdx, rbx
clc
adcx rdx, [ rsp + 0x348 ]
mov [ rsp + 0x3a0 ], rdx
mov rdx, rbx
adcx rdx, [ rsp + 0x348 ]
mov [ rsp + 0x3a8 ], rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x3b0 ], rdi
mov [ rsp + 0x3b8 ], r9
mulx r9, rdi, r8
adcx rbp, rbx
adcx rdi, r14
adcx r13, r9
adcx r10, [ rsp + 0x340 ]
setc bl
movzx r14, byte [ rsp + 0x300 ]
clc
mov r9, -0x1 
adcx r14, r9
adcx r12, [ rsp - 0x48 ]
setc r14b
clc
movzx r11, r11b
adcx r11, r9
adcx r15, [ rsp + 0x260 ]
seto r11b
movzx r9, byte [ rsp + 0x318 ]
mov rdx, 0x0 
dec rdx
adox r9, rdx
adox rcx, [ rsp + 0x2b0 ]
seto r9b
inc rdx
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox rcx, [ rsp + 0x3b8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x3c0 ], r12
mulx r12, r11, [ rax + 0x20 ]
mov rdx, [ rsp + 0x398 ]
adcx rdx, [ rsp + 0x268 ]
mov [ rsp + 0x3c8 ], r10
mov r10, [ rsp + 0x3b0 ]
mov byte [ rsp + 0x3d0 ], bl
seto bl
mov [ rsp + 0x3d8 ], r13
mov r13, 0x0 
dec r13
movzx r14, r14b
adox r14, r13
adox r10, [ rsp + 0x390 ]
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x3e0 ], r10
mulx r10, r13, [ rsi + 0x30 ]
adcx rcx, [ rsp + 0x280 ]
mov rdx, [ rsp + 0x358 ]
mov [ rsp + 0x3e8 ], r10
seto r10b
mov [ rsp + 0x3f0 ], rdi
movzx rdi, byte [ rsp + 0x360 ]
mov byte [ rsp + 0x3f8 ], bl
mov rbx, 0x0 
dec rbx
adox rdi, rbx
adox rdx, [ rsp + 0x2f8 ]
mov rdi, [ rsp + 0x388 ]
setc bl
clc
mov [ rsp + 0x400 ], rbp
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx rdi, [ rsp + 0x90 ]
adox r15, [ rsp + 0x310 ]
adcx r13, [ rsp + 0x88 ]
seto r10b
inc rbp
adox r8, [ rsp + 0x348 ]
adox rdx, [ rsp + 0x3a0 ]
setc r8b
clc
adcx rdx, [ rsp + 0x120 ]
adox r15, [ rsp + 0x3a8 ]
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x408 ], r13
mov [ rsp + 0x410 ], rdi
mulx rdi, r13, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x418 ], r8b
mov byte [ rsp + 0x420 ], bl
mulx rbx, r8, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x428 ], rbx
mov [ rsp + 0x430 ], rcx
mulx rcx, rbx, [ rsi + 0x28 ]
adcx r15, [ rsp + 0x148 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x438 ], rcx
mov [ rsp + 0x440 ], rbx
mulx rbx, rcx, rbp
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x448 ], rbx
mov [ rsp + 0x450 ], rcx
mulx rcx, rbx, rbp
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x458 ], r14
mov byte [ rsp + 0x460 ], r10b
mulx r10, r14, rbp
mov rdx, 0x2341f27177344 
mov [ rsp + 0x468 ], r10
mov [ rsp + 0x470 ], r14
mulx r14, r10, rbp
mov rdx, r13
mov [ rsp + 0x478 ], r14
setc r14b
clc
adcx rdx, rdi
mov [ rsp + 0x480 ], r10
setc r10b
clc
mov byte [ rsp + 0x488 ], r14b
mov r14, -0x1 
movzx r9, r9b
adcx r9, r14
adcx r8, [ rsp + 0x350 ]
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x490 ], r8
mulx r8, r14, [ rax + 0x28 ]
seto dl
mov [ rsp + 0x498 ], r8
movzx r8, byte [ rsp + 0x1c0 ]
mov [ rsp + 0x4a0 ], r14
mov r14, 0x0 
dec r14
adox r8, r14
adox r11, [ rsp + 0x18 ]
mov r8b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x4a8 ], r11
mulx r11, r14, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x4b0 ], r11
mov byte [ rsp + 0x4b8 ], r8b
mulx r8, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x4c0 ], r8
mov [ rsp + 0x4c8 ], r11
mulx r11, r8, [ rax + 0x8 ]
mov rdx, r13
mov [ rsp + 0x4d0 ], r11
setc r11b
clc
adcx rdx, rbp
mov rdx, [ rax + 0x0 ]
mov byte [ rsp + 0x4d8 ], r11b
mulx r11, rbp, [ rsi + 0x28 ]
adox r14, r12
adcx r9, r15
mov rdx, rdi
seto r12b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r10, r10b
adox r10, r15
adox rdx, r13
setc r13b
clc
adcx rbp, r9
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mulx r15, r9, rbp
adox rbx, rdi
adox rcx, [ rsp + 0x470 ]
mov rdi, 0x6cfc5fd681c52056 
mov rdx, rbp
mov [ rsp + 0x4e0 ], r15
mulx r15, rbp, rdi
mov rdi, [ rsp + 0x1f0 ]
mov [ rsp + 0x4e8 ], r15
setc r15b
mov [ rsp + 0x4f0 ], rbp
movzx rbp, byte [ rsp + 0x2a8 ]
clc
mov [ rsp + 0x4f8 ], r9
mov r9, -0x1 
adcx rbp, r9
adcx rdi, [ rsp + 0x1f8 ]
mov rbp, [ rsp + 0x1e8 ]
mov r9, 0x0 
adcx rbp, r9
mov r9, [ rsp + 0x458 ]
mov [ rsp + 0x500 ], r14
movzx r14, byte [ rsp + 0x460 ]
clc
mov byte [ rsp + 0x508 ], r12b
mov r12, -0x1 
adcx r14, r12
adcx r9, [ rsp + 0x308 ]
mov r14, [ rsp + 0x330 ]
adcx r14, [ rsp + 0x430 ]
seto r12b
mov [ rsp + 0x510 ], rcx
movzx rcx, byte [ rsp + 0x4b8 ]
mov [ rsp + 0x518 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rcx, rbx
adox r9, [ rsp + 0x400 ]
mov rcx, [ rsp + 0x490 ]
setc bl
mov byte [ rsp + 0x520 ], r12b
movzx r12, byte [ rsp + 0x3f8 ]
clc
mov byte [ rsp + 0x528 ], r15b
mov r15, -0x1 
adcx r12, r15
adcx rcx, [ rsp + 0x380 ]
adox r14, [ rsp + 0x3f0 ]
seto r12b
movzx r15, byte [ rsp + 0x488 ]
mov [ rsp + 0x530 ], rbp
mov rbp, 0x0 
dec rbp
adox r15, rbp
adox r9, [ rsp + 0x198 ]
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x538 ], r12b
mulx r12, rbp, [ rsi + 0x28 ]
setc dl
mov byte [ rsp + 0x540 ], bl
movzx rbx, byte [ rsp + 0x420 ]
clc
mov [ rsp + 0x548 ], r10
mov r10, -0x1 
adcx rbx, r10
adcx rcx, rdi
seto bl
inc r10
adox r8, r11
mov r11, [ rsp + 0x4d0 ]
adox r11, [ rsp + 0x50 ]
mov rdi, [ rsp + 0x4c8 ]
adox rdi, [ rsp + 0x48 ]
adox rbp, [ rsp + 0x4c0 ]
adox r12, [ rsp + 0x4a0 ]
mov r10, [ rsp + 0x440 ]
adox r10, [ rsp + 0x498 ]
mov [ rsp + 0x550 ], r10
setc r10b
clc
mov [ rsp + 0x558 ], r12
mov r12, -0x1 
movzx rbx, bl
adcx rbx, r12
adcx r14, [ rsp + 0x1a0 ]
mov rbx, [ rsp + 0x438 ]
mov r12, 0x0 
adox rbx, r12
movzx r12, byte [ rsp + 0x4d8 ]
mov [ rsp + 0x560 ], rbx
mov rbx, [ rsp + 0x428 ]
lea r12, [ r12 + rbx ]
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox r9, [ rsp + 0x548 ]
setc r13b
movzx rbx, byte [ rsp + 0x540 ]
clc
mov [ rsp + 0x568 ], rbp
mov rbp, -0x1 
adcx rbx, rbp
adcx rcx, [ rsp + 0x338 ]
mov bl, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x570 ], rdi
mulx rdi, rbp, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x578 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r12, [ rsp + 0x378 ]
setc bl
clc
movzx r10, r10b
adcx r10, rdi
adcx r12, [ rsp + 0x530 ]
seto r10b
movzx rdi, byte [ rsp + 0x528 ]
mov [ rsp + 0x580 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rdi, r11
adox r9, r8
movzx rdi, r10b
mov r8, 0x0 
adcx rdi, r8
movzx r10, byte [ rsp + 0x538 ]
clc
adcx r10, r11
adcx rcx, [ rsp + 0x3d8 ]
seto r10b
dec r8
movzx r13, r13b
adox r13, r8
adox rcx, [ rsp + 0x4a8 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, r8
adcx r14, [ rsp + 0x518 ]
adcx rcx, [ rsp + 0x510 ]
setc r13b
clc
movzx rbx, bl
adcx rbx, r8
adcx r12, [ rsp + 0x368 ]
mov rdx, [ rsp + 0x450 ]
seto bl
movzx r8, byte [ rsp + 0x520 ]
mov [ rsp + 0x588 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox r8, r9
adox rdx, [ rsp + 0x468 ]
adcx rdi, [ rsp + 0x370 ]
movzx r8, byte [ rsp + 0x3d0 ]
mov r9, [ rsp + 0x328 ]
lea r8, [ r8 + r9 ]
setc r9b
clc
mov [ rsp + 0x590 ], rcx
mov rcx, -0x1 
movzx r11, r11b
adcx r11, rcx
adcx r12, [ rsp + 0x3c8 ]
mov r11, [ rsp + 0x448 ]
adox r11, [ rsp + 0x480 ]
mov rcx, [ rsp + 0x478 ]
mov [ rsp + 0x598 ], r14
mov r14, 0x0 
adox rcx, r14
mov r14, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x5a0 ], rcx
mov byte [ rsp + 0x5a8 ], r10b
mulx r10, rcx, r14
adcx r8, rdi
movzx rdi, r9b
adc rdi, 0x0
mov r9, rcx
test al, al
adox r9, r10
mov r14, rcx
adox r14, r10
mov [ rsp + 0x5b0 ], rdi
movzx rdi, byte [ rsp + 0x508 ]
mov [ rsp + 0x5b8 ], r14
mov r14, -0x1 
adcx rdi, r14
adcx rbp, [ rsp + 0x4b0 ]
seto dil
inc r14
mov r14, -0x1 
movzx rbx, bl
adox rbx, r14
adox r12, [ rsp + 0x500 ]
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0x5c0 ], r9
mulx r9, r14, rbx
adox rbp, r8
setc r8b
clc
mov rbx, -0x1 
movzx rdi, dil
adcx rdi, rbx
adcx r10, [ rsp + 0x4f8 ]
seto dil
inc rbx
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox r12, r15
adcx r14, [ rsp + 0x4e0 ]
adox r11, rbp
adcx r9, [ rsp + 0x4f0 ]
setc r13b
clc
adcx rcx, rdx
mov rcx, [ rsp + 0x598 ]
setc r15b
movzx rbp, byte [ rsp + 0x5a8 ]
clc
adcx rbp, rbx
adcx rcx, [ rsp + 0x580 ]
mov rbp, [ rsp + 0x570 ]
adcx rbp, [ rsp + 0x590 ]
mov rbx, [ rsp + 0x5c0 ]
mov byte [ rsp + 0x5c8 ], r13b
seto r13b
mov [ rsp + 0x5d0 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r15, r15b
adox r15, r9
adox rbx, [ rsp + 0x588 ]
adcx r12, [ rsp + 0x568 ]
adox rcx, [ rsp + 0x5b8 ]
adox r10, rbp
seto r15b
inc r9
adox rbx, [ rsp + 0x2c8 ]
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x5d8 ], r14
mulx r14, r9, rbp
mov rbp, 0x7bc65c783158aea3 
mov [ rsp + 0x5e0 ], r14
mov [ rsp + 0x5e8 ], r12
mulx r12, r14, rbp
mov rbp, 0x6cfc5fd681c52056 
mov [ rsp + 0x5f0 ], r12
mov [ rsp + 0x5f8 ], r14
mulx r14, r12, rbp
movzx rbp, r8b
mov [ rsp + 0x600 ], r14
mov r14, [ rsp + 0x578 ]
lea rbp, [ rbp + r14 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x608 ], r12
mulx r12, r8, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x610 ], r12
mov byte [ rsp + 0x618 ], r15b
mulx r15, r12, r14
seto dl
mov [ rsp + 0x620 ], r10
mov r10, 0x0 
dec r10
movzx rdi, dil
adox rdi, r10
adox rbp, [ rsp + 0x5b0 ]
setc dil
movzx r10, byte [ rsp + 0x418 ]
clc
mov [ rsp + 0x628 ], r9
mov r9, -0x1 
adcx r10, r9
adcx r8, [ rsp + 0x3e8 ]
setc r10b
clc
movzx r13, r13b
adcx r13, r9
adcx rbp, [ rsp + 0x5a0 ]
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov r9, r12
adox r9, r15
mov [ rsp + 0x630 ], r8
mov r8, -0x1 
movzx rdx, dl
adcx rdx, r8
adcx rcx, [ rsp + 0x2d8 ]
setc dl
clc
movzx rdi, dil
adcx rdi, r8
adcx r11, [ rsp + 0x558 ]
mov rdi, r12
seto r8b
mov byte [ rsp + 0x638 ], r10b
mov r10, -0x2 
inc r10
adox rdi, r14
adcx rbp, [ rsp + 0x550 ]
adox r9, rcx
movzx r13, r13b
movzx rdi, r13b
adcx rdi, [ rsp + 0x560 ]
mov r13, r15
setc cl
clc
movzx r8, r8b
adcx r8, r10
adcx r13, r12
setc r12b
seto r8b
mov r10, r9
mov byte [ rsp + 0x640 ], cl
mov rcx, 0xffffffffffffffff 
sub r10, rcx
mov rcx, 0x0 
dec rcx
movzx r12, r12b
adox r12, rcx
adox r15, [ rsp + 0x628 ]
mov r12, 0x2341f27177344 
xchg rdx, r12
mov [ rsp + 0x648 ], r10
mulx r10, rcx, rbx
mov rbx, [ rsp + 0x3c0 ]
seto dl
mov [ rsp + 0x650 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox rbx, [ rsp + 0x620 ]
mov r12, [ rsp + 0x5d8 ]
setc r15b
mov byte [ rsp + 0x658 ], dl
movzx rdx, byte [ rsp + 0x618 ]
clc
mov [ rsp + 0x660 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx r12, [ rsp + 0x5e8 ]
adcx r11, [ rsp + 0x5d0 ]
adox r12, [ rsp + 0x3e0 ]
adox r11, [ rsp + 0x410 ]
movzx rdx, byte [ rsp + 0x638 ]
mov r13, [ rsp + 0x610 ]
lea rdx, [ rdx + r13 ]
seto r13b
mov byte [ rsp + 0x668 ], r15b
movzx r15, byte [ rsp + 0x5c8 ]
mov [ rsp + 0x670 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox r15, r11
adox rcx, [ rsp + 0x4e8 ]
adcx rcx, rbp
mov r15, 0x0 
adox r10, r15
adcx r10, rdi
dec r15
movzx r8, r8b
adox r8, r15
adox rbx, [ rsp + 0x660 ]
seto r11b
inc r15
mov rbp, -0x1 
movzx r13, r13b
adox r13, rbp
adox rcx, [ rsp + 0x408 ]
movzx r8, byte [ rsp + 0x640 ]
adcx r8, r15
adox r10, [ rsp + 0x630 ]
clc
movzx r11, r11b
adcx r11, rbp
adcx r12, [ rsp + 0x650 ]
adox rdx, r8
mov rdi, [ rsp + 0x5e0 ]
seto r13b
movzx r11, byte [ rsp + 0x658 ]
inc rbp
mov r15, -0x1 
adox r11, r15
adox rdi, [ rsp + 0x5f8 ]
adcx rdi, [ rsp + 0x670 ]
mov r11, [ rsp + 0x5f0 ]
adox r11, [ rsp + 0x608 ]
mov r8, 0x2341f27177344 
xchg rdx, r8
mulx r15, rbp, r14
adox rbp, [ rsp + 0x600 ]
mov r14, 0x0 
adox r15, r14
adcx r11, rcx
adcx rbp, r10
adcx r15, r8
movzx rcx, r13b
adc rcx, 0x0
movzx r10, byte [ rsp + 0x668 ]
add r10, -0x1
mov r10, rbx
mov r13, 0xffffffffffffffff 
sbb r10, r13
mov r8, r12
sbb r8, r13
mov r14, rdi
mov r13, 0xfdc1767ae2ffffff 
sbb r14, r13
mov r13, r11
mov rdx, 0x7bc65c783158aea3 
sbb r13, rdx
mov rdx, rbp
mov [ rsp + 0x678 ], r8
mov r8, 0x6cfc5fd681c52056 
sbb rdx, r8
mov r8, r15
mov [ rsp + 0x680 ], r10
mov r10, 0x2341f27177344 
sbb r8, r10
sbb rcx, 0x00000000
cmovc rdx, rbp
cmovc r13, r11
cmovc r14, rdi
mov rcx, [ rsp + 0x680 ]
cmovc rcx, rbx
mov rbx, [ rsp + 0x678 ]
cmovc rbx, r12
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x28 ], rdx
mov [ r12 + 0x10 ], rbx
cmovc r8, r15
mov rdi, [ rsp + 0x648 ]
cmovc rdi, r9
mov [ r12 + 0x0 ], rdi
mov [ r12 + 0x20 ], r13
mov [ r12 + 0x18 ], r14
mov [ r12 + 0x30 ], r8
mov [ r12 + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1800
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4237
; seed 2589058022761101 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9465331 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=38, initial num_batches=31): 160304 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016935910640631584
; number reverted permutation / tried permutation: 56648 / 89748 =63.119%
; number reverted decision / tried decision: 53927 / 90251 =59.752%
; validated in 239.606s
