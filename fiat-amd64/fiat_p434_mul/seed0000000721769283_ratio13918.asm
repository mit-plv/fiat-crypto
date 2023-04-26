SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1312
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r11
mulx r11, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], rdi
mulx rdi, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r10
mulx r10, rdi, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], rdi
mulx rdi, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r10
mulx r10, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r8
mulx r8, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rbx
mulx rbx, r8, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], r15
mulx r15, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], r11
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r9
mulx r9, r11, [ rax + 0x30 ]
test al, al
adox r8, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r8
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], r11
mulx r11, r9, [ rax + 0x0 ]
adcx rdi, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x70 ], r8
mulx r8, r11, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x78 ], rdi
mov [ rsp + 0x80 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], r8
mov [ rsp + 0x90 ], r11
mulx r11, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r12
mulx r12, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa8 ], rbp
mov [ rsp + 0xb0 ], r14
mulx r14, rbp, [ rsi + 0x8 ]
adcx r15, r10
adcx rdi, r12
adox r8, rbx
seto dl
mov r10, -0x2 
inc r10
adox r13, r14
setc bl
clc
movzx rdx, dl
adcx rdx, r10
adcx r11, rcx
mov rcx, [ rsp + 0xa8 ]
adox rcx, [ rsp + 0xb0 ]
mov r12, 0x6cfc5fd681c52056 
mov rdx, r9
mulx r14, r9, r12
mov r10, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb8 ], r11
mulx r11, r12, [ rsi + 0x0 ]
mov rdx, [ rsp + 0xa0 ]
adox rdx, [ rsp + 0x98 ]
mov [ rsp + 0xc0 ], r8
seto r8b
mov [ rsp + 0xc8 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rbx, bl
adox rbx, rdx
adox r12, [ rsp + 0x90 ]
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0xd0 ], r8b
mulx r8, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r9
mulx r9, r14, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0xe8 ], r14
mov r14, rdx
mov [ rsp + 0xf0 ], r12
setc r12b
clc
adcx r14, [ rsp + 0x88 ]
mov byte [ rsp + 0xf8 ], r12b
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x100 ], rcx
mov [ rsp + 0x108 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
mov rdx, r12
adcx rdx, [ rsp + 0x88 ]
mov [ rsp + 0x110 ], rdi
setc dil
clc
adcx rcx, r9
adcx rbx, r13
adox r11, [ rsp + 0x40 ]
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], rbx
mulx rbx, r13, [ rax + 0x0 ]
setc dl
clc
adcx r12, r10
adcx r14, [ rsp + 0x78 ]
seto r12b
mov [ rsp + 0x120 ], rcx
mov rcx, 0x0 
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r8, [ rsp + 0x30 ]
seto dl
inc rcx
adox rbp, r14
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r8
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x130 ], rcx
mov byte [ rsp + 0x138 ], r12b
mulx r12, rcx, rbp
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x140 ], r11
mov byte [ rsp + 0x148 ], r14b
mulx r14, r11, r10
adcx r9, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x150 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x158 ], rcx
mov [ rsp + 0x160 ], r13
mulx r13, rcx, [ rsi + 0x28 ]
setc dl
clc
adcx r15, rbx
mov bl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], r13
mov [ rsp + 0x170 ], r15
mulx r15, r13, [ rax + 0x8 ]
setc dl
clc
mov [ rsp + 0x178 ], r14
mov r14, -0x1 
movzx rdi, dil
adcx rdi, r14
adcx r11, [ rsp + 0x88 ]
seto dil
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox r12, [ rsp + 0x28 ]
setc dl
clc
movzx rbx, bl
adcx rbx, r14
adcx r11, [ rsp + 0x110 ]
mov bl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x180 ], r12
mulx r12, r14, [ rax + 0x0 ]
setc dl
clc
adcx r13, r8
mov r8b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x188 ], r13
mov [ rsp + 0x190 ], r14
mulx r14, r13, [ rsi + 0x30 ]
adcx rcx, r15
setc dl
clc
mov r15, -0x1 
movzx rdi, dil
adcx rdi, r15
adcx r9, [ rsp + 0x108 ]
mov dil, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x198 ], rcx
mulx rcx, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x1a0 ], dil
mov [ rsp + 0x1a8 ], r9
mulx r9, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x1b0 ], r8b
mov byte [ rsp + 0x1b8 ], bl
mulx rbx, r8, [ rsi + 0x30 ]
adox r15, [ rsp + 0x20 ]
adcx r11, [ rsp + 0x100 ]
seto dl
mov [ rsp + 0x1c0 ], r15
movzx r15, byte [ rsp + 0xf8 ]
mov [ rsp + 0x1c8 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox r15, r11
adox rdi, [ rsp + 0x10 ]
mov r15b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1d0 ], rdi
mulx rdi, r11, [ rax + 0x8 ]
adox r13, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1d8 ], r13
mulx r13, r9, [ rax + 0x30 ]
adox r8, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e0 ], r8
mulx r8, r14, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x1e8 ], r13
mov r13, 0x0 
dec r13
movzx r15, r15b
adox r15, r13
adox rcx, r14
adox r8, [ rsp + 0x8 ]
mov r15b, dl
mov rdx, [ rsi + 0x20 ]
mulx r13, r14, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1f0 ], r8
mov [ rsp + 0x1f8 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
setc dl
clc
adcx r11, r12
adcx rdi, [ rsp + 0x0 ]
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mov [ rsp + 0x200 ], rdi
mov [ rsp + 0x208 ], r11
mulx r11, rdi, rbp
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x210 ], r12b
mov [ rsp + 0x218 ], r13
mulx r13, r12, r10
adcx r8, [ rsp - 0x8 ]
adcx rcx, [ rsp - 0x20 ]
adox r9, [ rsp - 0x28 ]
mov rdx, rdi
mov [ rsp + 0x220 ], rcx
seto cl
mov [ rsp + 0x228 ], r8
mov r8, -0x2 
inc r8
adox rdx, r11
mov r8, rdi
adox r8, r11
adcx r14, [ rsp - 0x40 ]
mov [ rsp + 0x230 ], r14
setc r14b
mov byte [ rsp + 0x238 ], cl
movzx rcx, byte [ rsp + 0x1b8 ]
clc
mov [ rsp + 0x240 ], r9
mov r9, -0x1 
adcx rcx, r9
adcx r12, [ rsp + 0x178 ]
mov rcx, 0x2341f27177344 
xchg rdx, r10
mov byte [ rsp + 0x248 ], r14b
mulx r14, r9, rcx
seto dl
movzx rcx, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x250 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rcx, r14
adox r12, [ rsp + 0xf0 ]
setc cl
clc
adcx rdi, rbp
adcx r10, [ rsp + 0x1a8 ]
seto dil
inc r14
mov r14, -0x1 
movzx rcx, cl
adox rcx, r14
adox r13, [ rsp + 0xe0 ]
movzx rcx, r15b
lea rcx, [ rcx + rbx ]
adox r9, [ rsp + 0xd8 ]
seto bl
inc r14
adox r10, [ rsp + 0x160 ]
adcx r8, [ rsp + 0x1c8 ]
mov r15b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x258 ], rcx
mulx rcx, r14, [ rsi + 0x8 ]
adox r8, [ rsp + 0x170 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x260 ], r8
mov byte [ rsp + 0x268 ], bl
mulx rbx, r8, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x270 ], r9
movzx r9, byte [ rsp + 0xd0 ]
mov [ rsp + 0x278 ], r13
mov r13, 0x0 
dec r13
adox r9, r13
adox r14, [ rsp + 0x70 ]
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov byte [ rsp + 0x280 ], bpl
mulx rbp, r13, r9
adox r8, rcx
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x288 ], r8
mulx r8, r9, [ rsi + 0x18 ]
adox rbx, [ rsp + 0x50 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x290 ], r8
mov [ rsp + 0x298 ], rbx
mulx rbx, r8, r10
seto dl
mov [ rsp + 0x2a0 ], rbx
mov rbx, 0x0 
dec rbx
movzx r15, r15b
adox r15, rbx
adox r11, r13
mov r15, [ rsp + 0x68 ]
setc r13b
movzx rbx, byte [ rsp + 0x248 ]
clc
mov [ rsp + 0x2a8 ], r8
mov r8, -0x1 
adcx rbx, r8
adcx r15, [ rsp + 0x218 ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x2b0 ], r15
mulx r15, r8, rbx
adox rbp, [ rsp + 0x158 ]
adox r8, [ rsp + 0x150 ]
setc bl
mov byte [ rsp + 0x2b8 ], cl
movzx rcx, byte [ rsp + 0x148 ]
clc
mov [ rsp + 0x2c0 ], r8
mov r8, -0x1 
adcx rcx, r8
adcx r9, [ rsp - 0x48 ]
mov rcx, 0x2341f27177344 
mov byte [ rsp + 0x2c8 ], bl
mulx rbx, r8, rcx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2d0 ], r9
mulx r9, rcx, [ rsi + 0x0 ]
adox r8, r15
seto dl
movzx r15, byte [ rsp + 0x210 ]
mov [ rsp + 0x2d8 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r15, r8
adox r12, [ rsp + 0xc8 ]
mov r15, [ rsp + 0x140 ]
setc r8b
clc
mov [ rsp + 0x2e0 ], r9
mov r9, -0x1 
movzx rdi, dil
adcx rdi, r9
adcx r15, [ rsp + 0x278 ]
adox r14, r15
setc dil
clc
movzx r13, r13b
adcx r13, r9
adcx r12, r11
adcx rbp, r14
seto r13b
movzx r11, byte [ rsp + 0x138 ]
inc r9
mov r15, -0x1 
adox r11, r15
adox rcx, [ rsp + 0x18 ]
movzx r11, dl
lea r11, [ r11 + rbx ]
mov rbx, [ rsp + 0x2e0 ]
adox rbx, r9
inc r15
mov r9, -0x1 
movzx rdi, dil
adox rdi, r9
adox rcx, [ rsp + 0x270 ]
seto dl
inc r9
mov r15, -0x1 
movzx r13, r13b
adox r13, r15
adox rcx, [ rsp + 0x288 ]
mov dil, dl
mov rdx, [ rax + 0x30 ]
mulx r14, r13, [ rsi + 0x18 ]
adcx rcx, [ rsp + 0x2c0 ]
movzx rdx, byte [ rsp + 0x268 ]
mov r9, [ rsp + 0x250 ]
lea rdx, [ rdx + r9 ]
movzx r9, byte [ rsp + 0x2b8 ]
mov r15, [ rsp + 0x48 ]
lea r9, [ r9 + r15 ]
setc r15b
clc
mov [ rsp + 0x2e8 ], r14
mov r14, -0x1 
movzx rdi, dil
adcx rdi, r14
adcx rbx, rdx
setc dil
movzx rdx, byte [ rsp + 0x280 ]
clc
adcx rdx, r14
adcx r12, [ rsp + 0x180 ]
adox rbx, [ rsp + 0x298 ]
movzx rdx, dil
adox rdx, r9
adcx rbp, [ rsp + 0x1c0 ]
seto r9b
inc r14
mov rdi, -0x1 
movzx r15, r15b
adox r15, rdi
adox rbx, [ rsp + 0x2d8 ]
adox r11, rdx
mov r15, [ rsp + 0x290 ]
seto dl
dec r14
movzx r8, r8b
adox r8, r14
adox r15, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
movzx rdi, byte [ rsp + 0x2c8 ]
mov r8, [ rsp + 0x60 ]
lea rdi, [ rdi + r8 ]
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mov [ rsp + 0x2f0 ], rdi
mulx rdi, r14, r10
adcx rcx, [ rsp + 0x1f8 ]
adcx rbx, [ rsp + 0x1f0 ]
mov rdx, r14
mov [ rsp + 0x2f8 ], r13
seto r13b
mov [ rsp + 0x300 ], r15
mov r15, -0x2 
inc r15
adox rdx, rdi
adcx r11, [ rsp + 0x240 ]
mov r15, r14
adox r15, rdi
mov [ rsp + 0x308 ], r11
movzx r11, r13b
mov [ rsp + 0x310 ], rbx
mov rbx, [ rsp + 0x2e8 ]
lea r11, [ r11 + rbx ]
setc bl
clc
adcx r14, r10
adcx rdx, [ rsp + 0x260 ]
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0x318 ], r11
mulx r11, r13, r10
movzx rdx, byte [ rsp + 0x238 ]
mov [ rsp + 0x320 ], rcx
mov rcx, [ rsp + 0x1e8 ]
lea rdx, [ rdx + rcx ]
movzx rcx, r8b
movzx r9, r9b
lea rcx, [ rcx + r9 ]
adox r13, rdi
mov r9, 0x7bc65c783158aea3 
xchg rdx, r9
mulx rdi, r8, r10
adox r8, r11
adcx r15, r12
seto r12b
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rbx, bl
adox rbx, r11
adox rcx, r9
adcx r13, rbp
mov rbp, 0x6cfc5fd681c52056 
mov rdx, rbp
mulx rbx, rbp, r10
seto r10b
inc r11
mov r9, -0x1 
movzx r12, r12b
adox r12, r9
adox rdi, rbp
seto r12b
mov rbp, -0x3 
inc rbp
adox r14, [ rsp + 0xe8 ]
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx rbp, r11, r14
adox r15, [ rsp + 0x120 ]
adox r13, [ rsp + 0x118 ]
seto r9b
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox rbx, [ rsp + 0x2a8 ]
adcx r8, [ rsp + 0x320 ]
mov r12, 0x6cfc5fd681c52056 
mov rdx, r12
mov byte [ rsp + 0x328 ], r10b
mulx r10, r12, r14
mov rdx, [ rsp + 0x2a0 ]
mov [ rsp + 0x330 ], r10
mov r10, 0x0 
adox rdx, r10
adcx rdi, [ rsp + 0x310 ]
mov r10, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0x338 ], r12
mov [ rsp + 0x340 ], rbp
mulx rbp, r12, r10
adcx rbx, [ rsp + 0x308 ]
mov r10, r12
mov [ rsp + 0x348 ], rbx
mov rbx, -0x2 
inc rbx
adox r10, rbp
mov rbx, r12
adox rbx, rbp
adcx r14, rcx
adox r11, rbp
seto cl
mov rbp, -0x2 
inc rbp
adox r12, rdx
adox r10, r15
adox rbx, r13
setc r12b
clc
movzx r9, r9b
adcx r9, rbp
adcx r8, [ rsp + 0x128 ]
setc r15b
clc
adcx r10, [ rsp + 0x190 ]
adcx rbx, [ rsp + 0x208 ]
setc r9b
clc
movzx r15, r15b
adcx r15, rbp
adcx rdi, [ rsp + 0x2d0 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx rbp, r15, r10
mov rdx, 0x2341f27177344 
mov [ rsp + 0x350 ], r14
mov byte [ rsp + 0x358 ], r12b
mulx r12, r14, r10
adox r11, r8
seto r8b
mov rdx, 0x0 
dec rdx
movzx r9, r9b
adox r9, rdx
adox r11, [ rsp + 0x200 ]
mov r9, r15
seto dl
mov [ rsp + 0x360 ], r12
mov r12, -0x2 
inc r12
adox r9, r10
mov r9, r15
setc r12b
clc
adcx r9, rbp
adox r9, rbx
setc bl
clc
adcx r9, [ rsp + 0x130 ]
mov [ rsp + 0x368 ], r14
mov r14b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x370 ], r11
mov byte [ rsp + 0x378 ], r12b
mulx r12, r11, [ rsi + 0x28 ]
mov rdx, rbp
mov [ rsp + 0x380 ], r12
seto r12b
mov [ rsp + 0x388 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rbx, bl
adox rbx, r11
adox rdx, r15
mov r15, 0x2341f27177344 
xchg rdx, r15
mulx r11, rbx, r9
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x390 ], r11
mov [ rsp + 0x398 ], rbx
mulx rbx, r11, r13
seto dl
mov [ rsp + 0x3a0 ], r15
mov r15, 0x0 
dec r15
movzx rcx, cl
adox rcx, r15
adox r11, [ rsp + 0x340 ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov byte [ rsp + 0x3a8 ], r12b
mulx r12, r15, rcx
adox rbx, [ rsp + 0x338 ]
seto cl
mov [ rsp + 0x3b0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r8, r8b
adox r8, r12
adox rdi, r11
setc r8b
clc
movzx r14, r14b
adcx r14, r12
adcx rdi, [ rsp + 0x228 ]
mov r14, [ rsp + 0x348 ]
setc r11b
movzx r12, byte [ rsp + 0x378 ]
clc
mov [ rsp + 0x3b8 ], r15
mov r15, -0x1 
adcx r12, r15
adcx r14, [ rsp + 0x300 ]
movzx r12, byte [ rsp + 0x358 ]
movzx r15, byte [ rsp + 0x328 ]
lea r12, [ r12 + r15 ]
mov r15, 0x2341f27177344 
xchg rdx, r15
mov byte [ rsp + 0x3c0 ], r8b
mov [ rsp + 0x3c8 ], rdi
mulx rdi, r8, r13
mov r13, [ rsp + 0x350 ]
adcx r13, [ rsp + 0x2f8 ]
setc dl
clc
mov byte [ rsp + 0x3d0 ], r9b
mov r9, -0x1 
movzx rcx, cl
adcx rcx, r9
adcx r8, [ rsp + 0x330 ]
adox rbx, r14
adox r8, r13
setc cl
clc
movzx rdx, dl
adcx rdx, r9
adcx r12, [ rsp + 0x318 ]
movzx r14, cl
lea r14, [ r14 + rdi ]
adox r14, r12
setc dil
clc
movzx r11, r11b
adcx r11, r9
adcx rbx, [ rsp + 0x220 ]
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r13, r11, r10
adcx r8, [ rsp + 0x230 ]
mov rdx, [ rsi + 0x28 ]
mulx r12, rcx, [ rax + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov byte [ rsp + 0x3d8 ], dil
mulx rdi, r9, r10
seto dl
mov [ rsp + 0x3e0 ], r12
movzx r12, byte [ rsp + 0x3d0 ]
mov [ rsp + 0x3e8 ], rcx
mov rcx, 0x0 
dec rcx
adox r12, rcx
adox rbp, r11
adcx r14, [ rsp + 0x2b0 ]
adox r9, r13
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r10
mulx r13, r11, r12
mov rdx, [ rsp + 0x3a0 ]
setc cl
movzx r12, byte [ rsp + 0x3a8 ]
clc
mov byte [ rsp + 0x3f0 ], r10b
mov r10, -0x1 
adcx r12, r10
adcx rdx, [ rsp + 0x370 ]
adcx rbp, [ rsp + 0x3c8 ]
adox r11, rdi
adox r13, [ rsp + 0x368 ]
adcx r9, rbx
adcx r11, r8
seto r12b
movzx rbx, byte [ rsp + 0x3c0 ]
inc r10
mov r8, -0x1 
adox rbx, r8
adox rdx, [ rsp + 0x188 ]
mov rbx, [ rsp + 0x168 ]
setc dil
movzx r10, byte [ rsp + 0x1a0 ]
clc
adcx r10, r8
adcx rbx, [ rsp + 0x3e8 ]
mov r10, rdx
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x3f8 ], r12b
mulx r12, r8, [ rsi + 0x28 ]
adcx r8, [ rsp + 0x3e0 ]
adcx r12, [ rsp + 0x388 ]
adox rbp, [ rsp + 0x198 ]
adox rbx, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x400 ], r12
mulx r12, r9, r15
setc dl
clc
mov [ rsp + 0x408 ], rbx
mov rbx, -0x1 
movzx rdi, dil
adcx rdi, rbx
adcx r14, r13
adox r8, r11
movzx r13, byte [ rsp + 0x3f0 ]
movzx rdi, byte [ rsp + 0x3d8 ]
lea r13, [ r13 + rdi ]
setc dil
clc
movzx rcx, cl
adcx rcx, rbx
adcx r13, [ rsp + 0x2f0 ]
mov rcx, [ rsp + 0x380 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, rbx
adcx rcx, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
mov rbx, 0x0 
adcx rdx, rbx
movzx rbx, byte [ rsp + 0x3f8 ]
mov [ rsp + 0x410 ], rdx
mov rdx, [ rsp + 0x360 ]
lea rbx, [ rbx + rdx ]
mov rdx, r9
clc
adcx rdx, r12
mov [ rsp + 0x418 ], rcx
mov rcx, r9
adcx rcx, r12
mov [ rsp + 0x420 ], r8
seto r8b
mov byte [ rsp + 0x428 ], r11b
mov r11, -0x2 
inc r11
adox r9, r15
adox rdx, r10
adox rcx, rbp
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r15
mulx rbp, r10, r9
adcx r12, [ rsp + 0x3b8 ]
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x430 ], rbx
mulx rbx, r9, r11
adcx r9, [ rsp + 0x3b0 ]
adcx r10, rbx
adcx rbp, [ rsp + 0x398 ]
setc dl
clc
adcx r15, [ rsp + 0x38 ]
adox r12, [ rsp + 0x408 ]
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov byte [ rsp + 0x438 ], bl
mulx rbx, r11, r15
adcx rcx, [ rsp + 0x58 ]
adcx r12, [ rsp + 0xc0 ]
setc dl
clc
mov [ rsp + 0x440 ], rbx
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx r14, [ rsp + 0x400 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, rbx
adcx r13, [ rsp + 0x430 ]
movzx rdi, byte [ rsp + 0x428 ]
mov rbx, 0x0 
adcx rdi, rbx
adox r9, [ rsp + 0x420 ]
clc
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx r9, [ rsp + 0xb8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x448 ], rdi
mulx rdi, rbx, r15
adox r10, r14
mov r14, rbx
setc dl
clc
adcx r14, rdi
mov [ rsp + 0x450 ], r10
mov r10, rbx
mov byte [ rsp + 0x458 ], dl
seto dl
mov [ rsp + 0x460 ], rbp
mov rbp, -0x2 
inc rbp
adox r10, r15
adcx rbx, rdi
adcx r11, rdi
adox r14, rcx
setc r10b
clc
movzx r8, r8b
adcx r8, rbp
adcx r13, [ rsp + 0x418 ]
adox rbx, r12
adox r11, r9
setc cl
clc
movzx rdx, dl
adcx rdx, rbp
adcx r13, [ rsp + 0x460 ]
movzx r12, byte [ rsp + 0x438 ]
mov r8, [ rsp + 0x390 ]
lea r12, [ r12 + r8 ]
setc r8b
seto r9b
mov rdi, r14
mov rdx, 0xffffffffffffffff 
sub rdi, rdx
mov rbp, rbx
sbb rbp, rdx
mov rdx, [ rsp + 0x448 ]
mov [ rsp + 0x468 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rcx, cl
adox rcx, rdi
adox rdx, [ rsp + 0x410 ]
mov rcx, [ rsp + 0x450 ]
seto dil
mov [ rsp + 0x470 ], rbp
movzx rbp, byte [ rsp + 0x458 ]
mov byte [ rsp + 0x478 ], r9b
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox rbp, r9
adox rcx, [ rsp + 0x1d0 ]
seto bpl
mov r9, r11
mov [ rsp + 0x480 ], rcx
mov rcx, 0xffffffffffffffff 
sbb r9, rcx
mov rcx, 0x0 
dec rcx
movzx r8, r8b
adox r8, rcx
adox rdx, r12
seto r8b
inc rcx
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r13, [ rsp + 0x1d8 ]
movzx rbp, r8b
movzx rdi, dil
lea rbp, [ rbp + rdi ]
adox rdx, [ rsp + 0x1e0 ]
mov rdi, 0x7bc65c783158aea3 
xchg rdx, rdi
mulx rcx, r8, r15
seto r12b
mov rdx, 0x0 
dec rdx
movzx r10, r10b
adox r10, rdx
adox r8, [ rsp + 0x440 ]
mov r10, 0x6cfc5fd681c52056 
mov rdx, r15
mov [ rsp + 0x488 ], r9
mulx r9, r15, r10
mov r10, 0x2341f27177344 
mov [ rsp + 0x490 ], rbp
mov byte [ rsp + 0x498 ], r12b
mulx r12, rbp, r10
adox r15, rcx
adox rbp, r9
seto dl
movzx rcx, byte [ rsp + 0x478 ]
mov r9, 0x0 
dec r9
adox rcx, r9
adox r8, [ rsp + 0x480 ]
adox r15, r13
movzx rcx, dl
lea rcx, [ rcx + r12 ]
adox rbp, rdi
mov r13, [ rsp + 0x258 ]
seto dil
movzx r12, byte [ rsp + 0x498 ]
inc r9
mov rdx, -0x1 
adox r12, rdx
adox r13, [ rsp + 0x490 ]
seto r12b
dec r9
movzx rdi, dil
adox rdi, r9
adox r13, rcx
seto dl
mov rcx, r8
mov rdi, 0xfdc1767ae2ffffff 
sbb rcx, rdi
mov r9, r15
mov r10, 0x7bc65c783158aea3 
sbb r9, r10
movzx rdi, dl
movzx r12, r12b
lea rdi, [ rdi + r12 ]
mov r12, rbp
mov rdx, 0x6cfc5fd681c52056 
sbb r12, rdx
mov rdx, r13
mov r10, 0x2341f27177344 
sbb rdx, r10
sbb rdi, 0x00000000
cmovc r12, rbp
cmovc r9, r15
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r9
mov r15, [ rsp + 0x470 ]
cmovc r15, rbx
mov rbx, [ rsp + 0x468 ]
cmovc rbx, r14
mov r14, [ rsp + 0x488 ]
cmovc r14, r11
mov [ rdi + 0x8 ], r15
cmovc rdx, r13
mov [ rdi + 0x30 ], rdx
cmovc rcx, r8
mov [ rdi + 0x18 ], rcx
mov [ rdi + 0x0 ], rbx
mov [ rdi + 0x10 ], r14
mov [ rdi + 0x28 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1312
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3918
; seed 2380733322603365 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 18117759 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=22, initial num_batches=31): 318996 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.017606813292968516
; number reverted permutation / tried permutation: 66684 / 90100 =74.011%
; number reverted decision / tried decision: 53390 / 89899 =59.389%
; validated in 437.008s
