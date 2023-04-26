SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1600
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r15
mulx r15, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rbp
mulx rbp, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], rcx
mulx rcx, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], rdi
mulx rdi, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], rcx
mulx rcx, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], rcx
mov [ rsp + 0x48 ], r10
mulx r10, rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r10
mov [ rsp + 0x58 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], rax
mulx rax, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], rax
mov [ rsp + 0x78 ], rcx
mulx rcx, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], rax
mulx rax, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], rcx
mulx rcx, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rax
mov [ rsp + 0xa8 ], r15
mulx r15, rax, rdx
xor rdx, rdx
adox r14, rcx
mov rcx, 0x6cfc5fd681c52056 
mov rdx, rax
mov [ rsp + 0xb0 ], r14
mulx r14, rax, rcx
mov rcx, 0x7bc65c783158aea3 
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], rax
mulx rax, r14, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], rax
mov [ rsp + 0xd0 ], r14
mulx r14, rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], rbx
mulx rbx, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r13
mulx r13, rbx, [ rsi + 0x20 ]
adcx rax, r11
adox r10, rbp
mov rdx, [ rsi + 0x28 ]
mulx r11, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], rbp
mov [ rsp + 0x100 ], r10
mulx r10, rbp, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x108 ], rax
mov rax, -0x2 
inc rax
adox rdi, r11
adcx r8, r14
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mulx rax, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rax
mov [ rsp + 0x118 ], rdi
mulx rdi, rax, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x120 ], r8
mov r8, -0x2 
inc r8
adox rbp, r15
mov r15b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], r11
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], r11
mov [ rsp + 0x138 ], r8
mulx r8, r11, [ rsi + 0x20 ]
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x140 ], r12
mulx r12, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r9
mov [ rsp + 0x150 ], r8
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x158 ], rdi
mov [ rsp + 0x160 ], rax
mulx rax, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x168 ], r15b
mov [ rsp + 0x170 ], rbp
mulx rbp, r15, [ rsi + 0x30 ]
setc dl
clc
adcx rbp, [ rsp + 0xe0 ]
mov [ rsp + 0x178 ], rbp
setc bpl
clc
mov [ rsp + 0x180 ], r15
mov r15, -0x1 
movzx rdx, dl
adcx rdx, r15
adcx r9, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r9
mov [ rsp + 0x198 ], r15
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x1a0 ], r10
seto r10b
mov [ rsp + 0x1a8 ], r11
mov r11, 0x0 
dec r11
movzx rbp, bpl
adox rbp, r11
adox rdx, [ rsp + 0xf0 ]
mov rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x1b0 ], r10b
mulx r10, r11, [ rsi + 0x10 ]
setc dl
clc
adcx r12, [ rsp + 0x78 ]
mov [ rsp + 0x1b8 ], rbp
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c0 ], r12
mov [ rsp + 0x1c8 ], r10
mulx r10, r12, [ rsi + 0x20 ]
adox rdi, [ rsp + 0xe8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1d0 ], rdi
mov [ rsp + 0x1d8 ], r10
mulx r10, rdi, rcx
adox r9, rax
mov rax, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x68 ]
mov rdx, rdi
mov [ rsp + 0x1e0 ], r9
seto r9b
mov [ rsp + 0x1e8 ], rax
mov rax, -0x2 
inc rax
adox rdx, r10
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1f0 ], r11
mov [ rsp + 0x1f8 ], r13
mulx r13, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x48 ]
adcx rdx, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x8 ]
mov [ rsp + 0x200 ], r12
mov r12, [ rsp + 0x60 ]
mov [ rsp + 0x208 ], rdx
seto dl
mov [ rsp + 0x210 ], rax
mov rax, 0x0 
dec rax
movzx r14, r14b
adox r14, rax
adox r12, [ rsp + 0x0 ]
mov r14b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x218 ], r12
mulx r12, rax, rdx
adox rax, [ rsp - 0x28 ]
setc dl
clc
mov [ rsp + 0x220 ], rax
mov rax, -0x1 
movzx r9, r9b
adcx r9, rax
adcx r15, [ rsp - 0x18 ]
adox rbx, r12
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r9
mulx rax, r12, rcx
mov rdx, [ rsp - 0x20 ]
adcx rdx, [ rsp + 0x18 ]
mov [ rsp + 0x228 ], rdx
setc dl
clc
mov [ rsp + 0x230 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx r8, r11
mov bpl, dl
mov rdx, [ rsi + 0x30 ]
mulx r15, r11, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x1a8 ]
adox rdx, [ rsp + 0x1f8 ]
mov [ rsp + 0x238 ], rdx
mov rdx, r10
mov [ rsp + 0x240 ], rbx
seto bl
mov [ rsp + 0x248 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rdx, rdi
adcx r11, r13
adox r12, r10
adox rax, [ rsp + 0xd0 ]
mov r10, rdx
mov rdx, [ rsi + 0x28 ]
mulx r13, r14, [ rsi + 0x20 ]
setc dl
clc
adcx rdi, rcx
mov rdi, [ rsp - 0x30 ]
seto r8b
mov [ rsp + 0x250 ], r11
movzx r11, byte [ rsp + 0x1b0 ]
mov byte [ rsp + 0x258 ], bl
mov rbx, 0x0 
dec rbx
adox r11, rbx
adox rdi, [ rsp + 0x1a0 ]
mov r11, [ rsp + 0x170 ]
adcx r11, [ rsp + 0x210 ]
mov bl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x260 ], r11
mov [ rsp + 0x268 ], r13
mulx r13, r11, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x28 ]
adox rdx, [ rsp - 0x38 ]
adox r11, [ rsp + 0x20 ]
adox r13, [ rsp - 0x8 ]
mov [ rsp + 0x270 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x278 ], r14
mov byte [ rsp + 0x280 ], bpl
mulx rbp, r14, [ rsi + 0x28 ]
mov rdx, [ rsp - 0x10 ]
adox rdx, [ rsp + 0x88 ]
adcx r10, rdi
adcx r12, r13
movzx rdi, bl
lea rdi, [ rdi + r15 ]
mov r15, [ rsp + 0x30 ]
setc bl
movzx r13, byte [ rsp + 0x168 ]
clc
mov [ rsp + 0x288 ], rdi
mov rdi, -0x1 
adcx r13, rdi
adcx r15, [ rsp + 0x1f0 ]
seto r13b
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r11, rax
mov rax, [ rsp + 0xc0 ]
seto bl
inc rdi
mov rdi, -0x1 
movzx r8, r8b
adox r8, rdi
adox rax, [ rsp + 0xc8 ]
adcx r14, [ rsp + 0x1c8 ]
mov r8, [ rsp + 0x160 ]
setc dil
clc
mov [ rsp + 0x290 ], r14
mov r14, -0x1 
movzx r9, r9b
adcx r9, r14
adcx r8, [ rsp + 0x1d8 ]
movzx r9, byte [ rsp + 0x280 ]
mov r14, [ rsp + 0x10 ]
lea r9, [ r9 + r14 ]
mov r14, [ rsp + 0x158 ]
adcx r14, [ rsp + 0x138 ]
mov [ rsp + 0x298 ], r9
mov r9, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x2a0 ], r15
mov [ rsp + 0x2a8 ], r14
mulx r14, r15, rcx
setc cl
clc
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx rbp, [ rsp + 0x278 ]
mov rdi, [ rsp + 0x268 ]
adcx rdi, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2b0 ], rdi
mov [ rsp + 0x2b8 ], rbp
mulx rbp, rdi, [ rsi + 0x18 ]
adox r15, [ rsp + 0xb8 ]
mov rdx, [ rsp + 0x128 ]
adcx rdx, [ rsp - 0x48 ]
mov [ rsp + 0x2c0 ], rdx
mov rdx, [ rsp + 0x260 ]
mov byte [ rsp + 0x2c8 ], cl
setc cl
clc
adcx rdx, [ rsp + 0x40 ]
mov byte [ rsp + 0x2d0 ], cl
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x2d8 ], r8
mov [ rsp + 0x2e0 ], r15
mulx r15, r8, rcx
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2e8 ], r9
mov byte [ rsp + 0x2f0 ], r13b
mulx r13, r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2f8 ], r13
mov [ rsp + 0x300 ], r11
mulx r11, r13, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x308 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rbx, bl
adox rbx, r13
adox rax, [ rsp + 0x270 ]
adcx r10, [ rsp + 0x108 ]
movzx rbx, dl
lea rbx, [ rbx + r14 ]
seto r14b
inc r13
adox rdi, r11
mov rdx, r8
setc r11b
clc
adcx rdx, r15
mov [ rsp + 0x310 ], rdi
mov rdi, r8
mov [ rsp + 0x318 ], rax
setc al
clc
adcx rdi, rcx
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x320 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, r15
mov byte [ rsp + 0x328 ], r14b
seto r14b
mov [ rsp + 0x330 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rax, al
adox rax, r12
adox rdx, r8
adox r9, r15
movzx r8, byte [ rsp + 0x258 ]
mov r15, [ rsp + 0x150 ]
lea r8, [ r8 + r15 ]
seto r15b
inc r12
mov rax, -0x1 
movzx r14, r14b
adox r14, rax
adox rbp, r13
adox rbx, [ rsp + 0x58 ]
adcx rdi, r10
setc r10b
clc
adcx rdi, [ rsp + 0x148 ]
mov r14, [ rsp + 0x120 ]
setc r13b
clc
movzx r11, r11b
adcx r11, rax
adcx r14, [ rsp + 0x330 ]
mov r11, [ rsp + 0x50 ]
adox r11, [ rsp + 0x198 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x338 ], r8
mulx r8, rax, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x300 ]
adcx rdx, [ rsp + 0x140 ]
adox rax, [ rsp + 0x190 ]
mov [ rsp + 0x340 ], rax
mov rax, 0x2341f27177344 
xchg rdx, rdi
mov [ rsp + 0x348 ], r11
mov [ rsp + 0x350 ], rbx
mulx rbx, r11, rax
mov rax, 0x7bc65c783158aea3 
mov [ rsp + 0x358 ], rbp
mov [ rsp + 0x360 ], rbx
mulx rbx, rbp, rax
xchg rdx, rcx
mov [ rsp + 0x368 ], r11
mov [ rsp + 0x370 ], rbx
mulx rbx, r11, rax
adox r8, [ rsp + 0x98 ]
seto al
mov [ rsp + 0x378 ], r8
mov r8, 0x0 
dec r8
movzx r15, r15b
adox r15, r8
adox r11, [ rsp + 0x2f8 ]
movzx r15, byte [ rsp + 0x2f0 ]
mov r8, [ rsp + 0x80 ]
lea r15, [ r15 + r8 ]
mov r8, [ rsp + 0x2e8 ]
mov [ rsp + 0x380 ], rbp
seto bpl
mov byte [ rsp + 0x388 ], al
movzx rax, byte [ rsp + 0x328 ]
mov [ rsp + 0x390 ], rbx
mov rbx, 0x0 
dec rbx
adox rax, rbx
adox r8, [ rsp + 0x2e0 ]
adox r15, [ rsp + 0x320 ]
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov byte [ rsp + 0x398 ], bpl
mulx rbp, rbx, rcx
seto dl
mov [ rsp + 0x3a0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox r14, r12
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mulx rbp, r10, rcx
mov rdx, [ rsp + 0x318 ]
adcx rdx, [ rsp + 0x188 ]
adcx r8, [ rsp + 0x248 ]
mov [ rsp + 0x3a8 ], rbx
mov rbx, 0x2341f27177344 
xchg rdx, rax
mov [ rsp + 0x3b0 ], rbp
mov [ rsp + 0x3b8 ], r10
mulx r10, rbp, rbx
adox r9, rdi
adcx r15, [ rsp + 0x250 ]
movzx r12, r12b
movzx rdi, r12b
adcx rdi, [ rsp + 0x288 ]
adox r11, rax
setc r12b
clc
mov rax, -0x1 
movzx r13, r13b
adcx r13, rax
adcx r14, [ rsp + 0x1c0 ]
adcx r9, [ rsp + 0x1e8 ]
mov r13, 0x6cfc5fd681c52056 
mulx rbx, rax, r13
setc dl
movzx r13, byte [ rsp + 0x398 ]
clc
mov byte [ rsp + 0x3c0 ], r12b
mov r12, -0x1 
adcx r13, r12
adcx rax, [ rsp + 0x390 ]
adcx rbp, rbx
mov r13, 0x0 
adcx r10, r13
clc
movzx rdx, dl
adcx rdx, r12
adcx r11, [ rsp + 0x208 ]
adox rax, r8
adcx rax, [ rsp + 0x200 ]
mov r8, rcx
seto dl
mov rbx, -0x3 
inc rbx
adox r8, [ rsp + 0x3b8 ]
seto r8b
dec r13
movzx rdx, dl
adox rdx, r13
adox r15, rbp
mov r12, [ rsp + 0x3b8 ]
mov rbp, r12
setc dl
clc
adcx rbp, [ rsp + 0x3b0 ]
adcx r12, [ rsp + 0x3b0 ]
seto bl
inc r13
mov r13, -0x1 
movzx r8, r8b
adox r8, r13
adox r14, rbp
adox r12, r9
mov r9, [ rsp + 0x3b0 ]
adcx r9, [ rsp + 0x3a8 ]
movzx r8, byte [ rsp + 0x388 ]
mov rbp, [ rsp + 0x90 ]
lea r8, [ r8 + rbp ]
mov rbp, [ rsp + 0x3a0 ]
adcx rbp, [ rsp + 0x380 ]
setc r13b
clc
adcx r14, [ rsp + 0x308 ]
adox r9, r11
mov r11, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x3c8 ], r8
mov [ rsp + 0x3d0 ], r9
mulx r9, r8, r11
adox rbp, rax
mov rax, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3d8 ], r9
mulx r9, r11, rax
adcx r12, [ rsp + 0x310 ]
mov rax, 0x6cfc5fd681c52056 
xchg rdx, rax
mov [ rsp + 0x3e0 ], r8
mov [ rsp + 0x3e8 ], r9
mulx r9, r8, rcx
setc cl
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r8, [ rsp + 0x370 ]
setc r13b
clc
movzx r14, r14b
adcx r14, rdx
adcx r15, [ rsp + 0x2d8 ]
setc r14b
clc
movzx r13, r13b
adcx r13, rdx
adcx r9, [ rsp + 0x368 ]
mov r13, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp + 0x3f0 ], r9
mulx r9, r13, rax
setc dl
clc
mov [ rsp + 0x3f8 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx rdi, r10
movzx r10, byte [ rsp + 0x3c0 ]
mov rbx, 0x0 
adcx r10, rbx
clc
movzx r14, r14b
adcx r14, r11
adcx rdi, [ rsp + 0x2a8 ]
movzx r14, dl
mov rbx, [ rsp + 0x360 ]
lea r14, [ r14 + rbx ]
mov rbx, [ rsp + 0x3d0 ]
seto dl
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox rbx, [ rsp + 0x358 ]
setc cl
clc
movzx rdx, dl
adcx rdx, r11
adcx r15, r8
adox rbp, [ rsp + 0x350 ]
mov rdx, r13
seto r8b
inc r11
adox rdx, rax
mov rdx, r13
mov [ rsp + 0x400 ], rbp
setc bpl
clc
adcx rdx, r9
adox rdx, r12
movzx r12, byte [ rsp + 0x2c8 ]
mov r11, [ rsp + 0x130 ]
lea r12, [ r12 + r11 ]
mov r11, 0x6cfc5fd681c52056 
xchg rdx, rax
mov [ rsp + 0x408 ], rbx
mov [ rsp + 0x410 ], r14
mulx r14, rbx, r11
adcx r13, r9
adcx r9, [ rsp + 0x3f8 ]
mov r11, [ rsp + 0x3e8 ]
adcx r11, [ rsp + 0x3e0 ]
mov [ rsp + 0x418 ], r11
seto r11b
mov [ rsp + 0x420 ], r9
mov r9, -0x2 
inc r9
adox rax, [ rsp + 0xa0 ]
mov r9, 0xffffffffffffffff 
xchg rdx, rax
mov [ rsp + 0x428 ], r13
mov byte [ rsp + 0x430 ], r11b
mulx r11, r13, r9
seto r9b
mov [ rsp + 0x438 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx rcx, cl
adox rcx, r13
adox r10, r12
seto cl
inc r13
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox rdi, [ rsp + 0x3f0 ]
adcx rbx, [ rsp + 0x3d8 ]
mov rbp, 0x2341f27177344 
xchg rdx, rax
mulx r12, r13, rbp
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x440 ], r12
mulx r12, rbp, rax
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x448 ], r12
mov [ rsp + 0x450 ], rbp
mulx rbp, r12, rax
adcx r13, r14
setc r14b
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx r15, [ rsp + 0x348 ]
adox r10, [ rsp + 0x410 ]
movzx r8, cl
mov rdx, 0x0 
adox r8, rdx
mov rcx, 0x7bc65c783158aea3 
mov rdx, rax
mov [ rsp + 0x458 ], r8
mulx r8, rax, rcx
mov rcx, [ rsp + 0x428 ]
mov byte [ rsp + 0x460 ], r14b
movzx r14, byte [ rsp + 0x430 ]
mov [ rsp + 0x468 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r14, r8
adox rcx, [ rsp + 0x408 ]
adcx rdi, [ rsp + 0x340 ]
mov r14, [ rsp + 0x400 ]
adox r14, [ rsp + 0x420 ]
adcx r10, [ rsp + 0x378 ]
adox r15, [ rsp + 0x418 ]
adox rbx, rdi
setc dil
clc
movzx r9, r9b
adcx r9, r8
adcx rcx, [ rsp + 0xb0 ]
adox r13, r10
adcx r14, [ rsp + 0x100 ]
mov r9, r11
seto r10b
inc r8
adox r9, [ rsp + 0x438 ]
mov byte [ rsp + 0x470 ], r10b
mov r10, rdx
mov byte [ rsp + 0x478 ], dil
setc dil
clc
adcx r10, [ rsp + 0x438 ]
adcx r9, rcx
mov r10, r11
adox r10, [ rsp + 0x438 ]
adox r12, r11
seto r11b
mov rcx, -0x3 
inc rcx
adox r9, [ rsp + 0xf8 ]
adcx r10, r14
setc r14b
clc
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx r15, [ rsp + 0x218 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx rcx, r8, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x480 ], rcx
mov [ rsp + 0x488 ], r8
mulx r8, rcx, r9
adcx rbx, [ rsp + 0x220 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x490 ], rbx
mov [ rsp + 0x498 ], r13
mulx r13, rbx, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4a0 ], r13
mov [ rsp + 0x4a8 ], rbx
mulx rbx, r13, r9
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x4b0 ], rbx
mov [ rsp + 0x4b8 ], r13
mulx r13, rbx, r9
adox r10, [ rsp + 0x118 ]
mov rdx, rcx
mov [ rsp + 0x4c0 ], r13
setc r13b
clc
adcx rdx, r8
mov [ rsp + 0x4c8 ], rbx
mov rbx, 0x2341f27177344 
xchg rdx, rbx
mov byte [ rsp + 0x4d0 ], r13b
mov [ rsp + 0x4d8 ], rax
mulx rax, r13, rdi
mov rdi, rcx
seto dl
mov [ rsp + 0x4e0 ], rax
mov rax, -0x2 
inc rax
adox rdi, r9
adox rbx, r10
seto dil
inc rax
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox r15, r12
seto r12b
dec rax
movzx rdx, dl
adox rdx, rax
adox r15, [ rsp + 0x2a0 ]
seto r9b
inc rax
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox rbp, [ rsp + 0x4d8 ]
adcx rcx, r8
mov r11, [ rsp + 0x468 ]
adox r11, [ rsp + 0x450 ]
setc dl
clc
movzx rdi, dil
adcx rdi, r14
adcx r15, rcx
adox r13, [ rsp + 0x448 ]
setc r10b
clc
adcx rbx, [ rsp + 0x180 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx rax, rcx, rbx
mov r14, 0xfdc1767ae2ffffff 
mov rdx, r14
mov [ rsp + 0x4e8 ], rax
mulx rax, r14, rbx
mov rdx, [ rsp + 0x4e0 ]
mov [ rsp + 0x4f0 ], rcx
mov rcx, 0x0 
adox rdx, rcx
mov rcx, 0x7bc65c783158aea3 
xchg rdx, rcx
mov [ rsp + 0x4f8 ], rax
mov [ rsp + 0x500 ], r14
mulx r14, rax, rbx
mov rdx, [ rsp + 0x498 ]
mov [ rsp + 0x508 ], r14
movzx r14, byte [ rsp + 0x4d0 ]
mov [ rsp + 0x510 ], rax
mov rax, 0x0 
dec rax
adox r14, rax
adox rdx, [ rsp + 0x240 ]
adcx r15, [ rsp + 0x178 ]
setc r14b
clc
movzx r12, r12b
adcx r12, rax
adcx rbp, [ rsp + 0x490 ]
seto r12b
inc rax
mov rax, -0x1 
movzx r9, r9b
adox r9, rax
adox rbp, [ rsp + 0x290 ]
movzx r9, byte [ rsp + 0x460 ]
mov rax, [ rsp + 0x440 ]
lea r9, [ r9 + rax ]
mov rax, [ rsp + 0x458 ]
mov [ rsp + 0x518 ], r15
setc r15b
mov [ rsp + 0x520 ], rcx
movzx rcx, byte [ rsp + 0x478 ]
clc
mov [ rsp + 0x528 ], r13
mov r13, -0x1 
adcx rcx, r13
adcx rax, [ rsp + 0x3c8 ]
seto cl
inc r13
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox r8, [ rsp + 0x4b8 ]
mov rdi, [ rsp + 0x4c8 ]
adox rdi, [ rsp + 0x4b0 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x530 ], rdi
mov byte [ rsp + 0x538 ], cl
mulx rcx, rdi, rbx
mov rdx, rdi
mov byte [ rsp + 0x540 ], r12b
setc r12b
clc
adcx rdx, rcx
mov [ rsp + 0x548 ], rdx
mov rdx, [ rsp + 0x488 ]
adox rdx, [ rsp + 0x4c0 ]
mov [ rsp + 0x550 ], rdx
setc dl
mov byte [ rsp + 0x558 ], r14b
movzx r14, byte [ rsp + 0x470 ]
clc
mov [ rsp + 0x560 ], r8
mov r8, -0x1 
adcx r14, r8
adcx rax, r9
mov r14, [ rsp + 0x4a8 ]
adox r14, [ rsp + 0x480 ]
movzx r9, r12b
mov r8, 0x0 
adcx r9, r8
clc
mov r12, -0x1 
movzx r15, r15b
adcx r15, r12
adcx r13, r11
mov r11, [ rsp + 0x4a0 ]
adox r11, r8
inc r12
mov r8, -0x1 
movzx r10, r10b
adox r10, r8
adox rbp, [ rsp + 0x560 ]
mov r10, rdi
setc r15b
clc
adcx r10, rbx
seto r10b
movzx r12, byte [ rsp + 0x558 ]
inc r8
mov r8, -0x1 
adox r12, r8
adox rbp, [ rsp + 0x1b8 ]
setc r12b
movzx r8, byte [ rsp + 0x540 ]
clc
mov [ rsp + 0x568 ], r11
mov r11, -0x1 
adcx r8, r11
adcx rax, [ rsp + 0x238 ]
adcx r9, [ rsp + 0x338 ]
mov r8, rcx
seto r11b
mov [ rsp + 0x570 ], r14
mov r14, 0x0 
dec r14
movzx rdx, dl
adox rdx, r14
adox r8, rdi
setc dil
movzx rdx, byte [ rsp + 0x538 ]
clc
adcx rdx, r14
adcx r13, [ rsp + 0x2b8 ]
seto dl
inc r14
mov r14, -0x1 
movzx r10, r10b
adox r10, r14
adox r13, [ rsp + 0x530 ]
seto r10b
inc r14
mov r14, -0x1 
movzx r15, r15b
adox r15, r14
adox rax, [ rsp + 0x528 ]
adox r9, [ rsp + 0x520 ]
seto r15b
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox rcx, [ rsp + 0x500 ]
mov rdx, [ rsp + 0x4f8 ]
adox rdx, [ rsp + 0x510 ]
adcx rax, [ rsp + 0x2b0 ]
mov r14, [ rsp + 0x508 ]
adox r14, [ rsp + 0x4f0 ]
adcx r9, [ rsp + 0x2c0 ]
mov [ rsp + 0x578 ], r14
setc r14b
clc
mov [ rsp + 0x580 ], r9
mov r9, -0x1 
movzx r10, r10b
adcx r10, r9
adcx rax, [ rsp + 0x550 ]
mov r10, [ rsp + 0x548 ]
setc r9b
clc
mov byte [ rsp + 0x588 ], r14b
mov r14, -0x1 
movzx r12, r12b
adcx r12, r14
adcx r10, [ rsp + 0x518 ]
adcx r8, rbp
setc r12b
clc
movzx r11, r11b
adcx r11, r14
adcx r13, [ rsp + 0x1d0 ]
adcx rax, [ rsp + 0x1e0 ]
setc bpl
seto r11b
mov r14, r10
mov byte [ rsp + 0x590 ], r9b
mov r9, 0xffffffffffffffff 
sub r14, r9
mov [ rsp + 0x598 ], r14
mov r14, r8
sbb r14, r9
movzx r9, r15b
movzx rdi, dil
lea r9, [ r9 + rdi ]
mov rdi, 0x0 
dec rdi
movzx r12, r12b
adox r12, rdi
adox r13, rcx
adox rdx, rax
seto r15b
mov rcx, r13
mov r12, 0xffffffffffffffff 
sbb rcx, r12
movzx rax, byte [ rsp + 0x2d0 ]
mov rdi, [ rsp + 0x110 ]
lea rax, [ rax + rdi ]
mov rdi, rdx
mov r12, 0xfdc1767ae2ffffff 
sbb rdi, r12
mov r12, 0x2341f27177344 
xchg rdx, r12
mov [ rsp + 0x5a0 ], rdi
mov [ rsp + 0x5a8 ], rcx
mulx rcx, rdi, rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox rdi, [ rsp + 0x4e8 ]
seto r11b
movzx rbx, byte [ rsp + 0x588 ]
mov rdx, 0x0 
dec rdx
adox rbx, rdx
adox r9, rax
mov rbx, [ rsp + 0x570 ]
setc al
movzx rdx, byte [ rsp + 0x590 ]
clc
mov [ rsp + 0x5b0 ], r14
mov r14, -0x1 
adcx rdx, r14
adcx rbx, [ rsp + 0x580 ]
adcx r9, [ rsp + 0x568 ]
seto dl
inc r14
mov r14, -0x1 
movzx rbp, bpl
adox rbp, r14
adox rbx, [ rsp + 0x230 ]
adox r9, [ rsp + 0x228 ]
setc bpl
clc
movzx r15, r15b
adcx r15, r14
adcx rbx, [ rsp + 0x578 ]
adcx rdi, r9
setc r15b
seto r9b
movzx r14, al
add r14, -0x1
mov rax, rbx
mov r14, 0x7bc65c783158aea3 
sbb rax, r14
mov r14, rdi
mov [ rsp + 0x5b8 ], rax
mov rax, 0x6cfc5fd681c52056 
sbb r14, rax
movzx rax, bpl
movzx rdx, dl
lea rax, [ rax + rdx ]
movzx rdx, r11b
lea rdx, [ rdx + rcx ]
mov rcx, -0x1 
inc rcx
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox rax, [ rsp + 0x298 ]
setc bpl
clc
movzx r15, r15b
adcx r15, r11
adcx rax, rdx
seto r9b
adc r9b, 0x0
movzx r9, r9b
movzx r15, bpl
add r15, -0x1
mov rbp, rax
mov r15, 0x2341f27177344 
sbb rbp, r15
movzx rdx, r9b
sbb rdx, 0x00000000
cmovc rbp, rax
mov rdx, [ rsp + 0x5b0 ]
cmovc rdx, r8
mov r8, [ rsp + 0x5a8 ]
cmovc r8, r13
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], r8
mov [ r13 + 0x8 ], rdx
mov rax, [ rsp + 0x5a0 ]
cmovc rax, r12
mov [ r13 + 0x30 ], rbp
mov [ r13 + 0x18 ], rax
cmovc r14, rdi
mov [ r13 + 0x28 ], r14
mov r12, [ rsp + 0x5b8 ]
cmovc r12, rbx
mov rbx, [ rsp + 0x598 ]
cmovc rbx, r10
mov [ r13 + 0x0 ], rbx
mov [ r13 + 0x20 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1600
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4028
; seed 2862586031305590 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 72654 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 1174 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.016158779970820603
; number reverted permutation / tried permutation: 269 / 522 =51.533%
; number reverted decision / tried decision: 187 / 477 =39.203%
; validated in 351.663s
