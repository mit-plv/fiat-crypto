SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1440
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r14
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r10
mulx r10, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], rax
mov [ rsp + 0x8 ], r13
mulx r13, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r13
mov [ rsp + 0x18 ], rax
mulx rax, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r10
mulx r10, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r10
mov [ rsp + 0x38 ], r8
mulx r8, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], r15
mulx r15, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r8
mulx r8, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], rdi
mulx rdi, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], rax
mov [ rsp + 0x98 ], r8
mulx r8, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], r8
mov [ rsp + 0xa8 ], rax
mulx rax, r8, [ rsi + 0x28 ]
add rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], rbp
mulx rbp, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], r9
mulx r9, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], rax
mulx rax, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe8 ], rbp
mov [ rsp + 0xf0 ], r8
mulx r8, rbp, [ rsi + 0x18 ]
adcx r12, rbx
mov rdx, -0x2 
inc rdx
adox rcx, rax
mov rdx, [ rsi + 0x28 ]
mulx rax, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], rcx
mulx rcx, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r12
mulx r12, rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x118 ], rax
mov [ rsp + 0x120 ], r12
mulx r12, rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x128 ], r12
mov [ rsp + 0x130 ], rax
mulx rax, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], rcx
mov [ rsp + 0x140 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x148 ], r8
mov [ rsp + 0x150 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
adox r12, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x158 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x160 ], r12
mov [ rsp + 0x168 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], rbx
mov [ rsp + 0x178 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x180 ], r9
mov [ rsp + 0x188 ], rcx
mulx rcx, r9, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x190 ], r9
mov r9, -0x2 
inc r9
adox r12, rcx
mov cl, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x198 ], r12
mulx r12, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1a0 ], r12
mov [ rsp + 0x1a8 ], r9
mulx r9, r12, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x1b0 ], r12
mov r12, -0x2 
inc r12
adox r13, r9
seto r9b
inc r12
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x1c8 ], r12
mov r12, -0x2 
inc r12
adox rbx, r14
setc r14b
clc
adcx r10, r15
mov r15b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1d0 ], rbx
mulx rbx, r12, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x1d8 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox rax, [ rsp + 0x98 ]
setc cl
clc
movzx r9, r9b
adcx r9, r10
adcx r11, [ rsp + 0x90 ]
setc r9b
clc
movzx rdx, dl
adcx rdx, r10
adcx rbp, r8
adox r13, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x180 ]
adcx rdx, [ rsp + 0x188 ]
mov [ rsp + 0x1e0 ], r11
seto r11b
mov [ rsp + 0x1e8 ], rdx
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox r8, [ rsp + 0x80 ]
setc r15b
clc
movzx r11, r11b
adcx r11, rdx
adcx rdi, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x1c8 ]
mov [ rsp + 0x1f8 ], rbp
seto bpl
mov [ rsp + 0x200 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox rdx, [ rsp + 0x48 ]
mov r9, [ rsp + 0xa8 ]
adox r9, [ rsp + 0x28 ]
mov r13, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x178 ]
mov [ rsp + 0x208 ], r9
mov r9, [ rsp + 0xf0 ]
mov [ rsp + 0x210 ], rdx
seto dl
mov [ rsp + 0x218 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r14, r14b
adox r14, r13
adox r9, [ rsp + 0x8 ]
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], r9
mulx r9, r13, rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x228 ], rax
mov [ rsp + 0x230 ], r8
mulx r8, rax, r13
mov rdx, [ rsp + 0xe0 ]
adox rdx, [ rsp + 0x170 ]
mov [ rsp + 0x238 ], rdx
seto dl
mov [ rsp + 0x240 ], r8
mov r8, 0x0 
dec r8
movzx rbp, bpl
adox rbp, r8
adox r10, [ rsp + 0x150 ]
mov rbp, [ rsp + 0x140 ]
mov r8, 0x0 
adcx rbp, r8
clc
adcx r9, [ rsp + 0x168 ]
mov r8, [ rsp + 0x38 ]
adox r8, [ rsp + 0x148 ]
mov [ rsp + 0x248 ], rbp
mov rbp, [ rsp + 0x160 ]
adcx rbp, [ rsp + 0x0 ]
mov [ rsp + 0x250 ], r8
mov r8b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x258 ], r10
mov [ rsp + 0x260 ], rax
mulx rax, r10, [ rsi + 0x8 ]
mov rdx, [ rsp - 0x8 ]
adcx rdx, [ rsp + 0xd0 ]
mov [ rsp + 0x268 ], rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x270 ], rbp
mov [ rsp + 0x278 ], r9
mulx r9, rbp, r13
adcx r11, [ rsp + 0xc8 ]
adcx rdi, [ rsp + 0x58 ]
seto dl
mov [ rsp + 0x280 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rcx, cl
adox rcx, rdi
adox r10, [ rsp + 0x40 ]
adox rax, [ rsp + 0xc0 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x288 ], rax
mulx rax, rdi, rcx
adox r12, [ rsp + 0xb8 ]
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x290 ], r12
mov [ rsp + 0x298 ], r10
mulx r10, r12, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x2a0 ], r11
setc r11b
clc
mov [ rsp + 0x2a8 ], r9
mov r9, -0x1 
movzx r14, r14b
adcx r14, r9
adcx rdx, [ rsp - 0x18 ]
mov r14, [ rsp + 0xd8 ]
seto r9b
mov [ rsp + 0x2b0 ], rdx
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox r14, [ rsp + 0x138 ]
mov r15, [ rsp + 0x68 ]
seto dl
mov [ rsp + 0x2b8 ], r14
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox r15, [ rsp + 0x50 ]
mov r11, [ rsp - 0x20 ]
adcx r11, [ rsp + 0x130 ]
seto r14b
mov [ rsp + 0x2c0 ], r11
mov r11, 0x0 
dec r11
movzx rdx, dl
adox rdx, r11
adox r12, [ rsp + 0x120 ]
adox r10, [ rsp + 0x18 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2c8 ], r10
mulx r10, r11, rcx
mov rdx, rdi
mov [ rsp + 0x2d0 ], r12
setc r12b
clc
adcx rdx, rax
mov byte [ rsp + 0x2d8 ], r14b
mov r14, rdi
adcx r14, rax
adcx r11, rax
adcx rbp, r10
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2e0 ], r15
mulx r15, r10, rdx
seto dl
mov [ rsp + 0x2e8 ], rbp
mov rbp, 0x0 
dec rbp
movzx r8, r8b
adox r8, rbp
adox r10, [ rsp + 0x118 ]
mov r8, [ rsp + 0x30 ]
seto bpl
mov [ rsp + 0x2f0 ], r10
mov r10, 0x0 
dec r10
movzx r13, r13b
adox r13, r10
adox r8, [ rsp + 0x1a8 ]
setc r13b
clc
adcx rdi, rcx
seto dil
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox r15, [ rsp + 0x110 ]
movzx rbp, r12b
mov r10, [ rsp + 0x128 ]
lea rbp, [ rbp + r10 ]
mov r10, [ rsp + 0x108 ]
mov r12, 0x0 
adox r10, r12
dec r12
movzx r9, r9b
adox r9, r12
adox rbx, [ rsp - 0x28 ]
mov r9, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x2f8 ], rbp
mulx rbp, r12, r9
adcx rax, [ rsp + 0x278 ]
adcx r14, [ rsp + 0x270 ]
mov rdx, [ rsp - 0x30 ]
adox rdx, [ rsp - 0x38 ]
movzx r9, dil
mov [ rsp + 0x300 ], r10
mov r10, [ rsp + 0x1a0 ]
lea r9, [ r9 + r10 ]
movzx r10, cl
mov rdi, [ rsp + 0x10 ]
lea r10, [ r10 + rdi ]
seto dil
mov rcx, 0x0 
dec rcx
movzx r13, r13b
adox r13, rcx
adox r12, [ rsp + 0x2a8 ]
adox rbp, [ rsp + 0x260 ]
adcx r11, [ rsp + 0x268 ]
movzx r13, dil
mov rcx, [ rsp - 0x48 ]
lea r13, [ r13 + rcx ]
seto cl
mov rdi, -0x2 
inc rdi
adox rax, [ rsp + 0x70 ]
adox r14, [ rsp + 0x1d8 ]
mov rdi, [ rsp + 0x2a0 ]
adcx rdi, [ rsp + 0x2e8 ]
mov [ rsp + 0x308 ], r15
mov r15, 0x7bc65c783158aea3 
xchg rdx, rax
mov [ rsp + 0x310 ], r10
mov [ rsp + 0x318 ], r9
mulx r9, r10, r15
adcx r12, [ rsp + 0x280 ]
adox r11, [ rsp + 0x298 ]
adcx rbp, [ rsp + 0x2e0 ]
movzx r15, cl
mov [ rsp + 0x320 ], r8
mov r8, [ rsp + 0x240 ]
lea r15, [ r15 + r8 ]
adox rdi, [ rsp + 0x288 ]
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x328 ], r9
mulx r9, rcx, r8
adox r12, [ rsp + 0x290 ]
mov r8, rcx
mov [ rsp + 0x330 ], r13
setc r13b
clc
adcx r8, r9
mov [ rsp + 0x338 ], rax
mov rax, rcx
adcx rax, r9
mov [ rsp + 0x340 ], rbx
setc bl
clc
adcx rcx, rdx
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x348 ], rbp
mov [ rsp + 0x350 ], r12
mulx r12, rbp, rcx
movzx rcx, byte [ rsp + 0x2d8 ]
mov [ rsp + 0x358 ], r15
mov r15, [ rsp + 0x60 ]
lea rcx, [ rcx + r15 ]
setc r15b
clc
mov [ rsp + 0x360 ], rcx
mov rcx, -0x1 
movzx rbx, bl
adcx rbx, rcx
adcx r9, rbp
adcx r10, r12
setc bl
clc
movzx r15, r15b
adcx r15, rcx
adcx r14, r8
adcx rax, r11
adcx r9, rdi
mov r11, [ rsp + 0x360 ]
setc dil
clc
movzx r13, r13b
adcx r13, rcx
adcx r11, [ rsp + 0x358 ]
seto r13b
inc rcx
mov r8, -0x1 
movzx rdi, dil
adox rdi, r8
adox r10, [ rsp + 0x350 ]
mov r15, [ rsp + 0x348 ]
seto bpl
dec rcx
movzx r13, r13b
adox r13, rcx
adox r15, [ rsp + 0x340 ]
adox r11, [ rsp + 0x338 ]
seto r8b
inc rcx
adox r14, [ rsp + 0x190 ]
mov r13, 0x2341f27177344 
mulx rdi, r12, r13
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x368 ], r10
mulx r10, r13, r14
mov [ rsp + 0x370 ], r10
mov [ rsp + 0x378 ], r13
mulx r13, r10, rcx
movzx r8, r8b
movzx rcx, r8b
adcx rcx, [ rsp + 0x330 ]
mov r8, 0xfdc1767ae2ffffff 
mov rdx, r8
mov [ rsp + 0x380 ], rcx
mulx rcx, r8, r14
setc dl
clc
mov [ rsp + 0x388 ], rcx
mov rcx, -0x1 
movzx rbx, bl
adcx rbx, rcx
adcx r10, [ rsp + 0x328 ]
adcx r12, r13
mov rbx, 0x0 
adcx rdi, rbx
mov r13, 0x7bc65c783158aea3 
xchg rdx, r13
mulx rcx, rbx, r14
clc
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx r15, r10
mov rbp, 0x2341f27177344 
mov rdx, r14
mulx r10, r14, rbp
mov rbp, 0xffffffffffffffff 
mov byte [ rsp + 0x390 ], r13b
mov [ rsp + 0x398 ], r10
mulx r10, r13, rbp
mov rbp, r13
mov [ rsp + 0x3a0 ], r15
seto r15b
mov [ rsp + 0x3a8 ], r14
mov r14, -0x2 
inc r14
adox rbp, r10
mov r14, r13
adox r14, r10
mov [ rsp + 0x3b0 ], r14
seto r14b
mov [ rsp + 0x3b8 ], rbp
mov rbp, -0x2 
inc rbp
adox r13, rdx
adcx r12, r11
setc r13b
clc
movzx r15, r15b
adcx r15, rbp
adcx rax, [ rsp + 0x198 ]
seto r11b
inc rbp
mov rdx, -0x1 
movzx r14, r14b
adox r14, rdx
adox r10, r8
adcx r9, [ rsp + 0x1c0 ]
adox rbx, [ rsp + 0x388 ]
adox rcx, [ rsp + 0x378 ]
setc r15b
clc
movzx r13, r13b
adcx r13, rdx
adcx rdi, [ rsp + 0x380 ]
mov r8, [ rsp + 0x370 ]
adox r8, [ rsp + 0x3a8 ]
mov r14, [ rsp + 0x230 ]
setc r13b
clc
movzx r15, r15b
adcx r15, rdx
adcx r14, [ rsp + 0x368 ]
mov r15, [ rsp + 0x258 ]
adcx r15, [ rsp + 0x3a0 ]
setc bpl
clc
movzx r11, r11b
adcx r11, rdx
adcx rax, [ rsp + 0x3b8 ]
mov r11, [ rsp + 0x398 ]
mov rdx, 0x0 
adox r11, rdx
adcx r9, [ rsp + 0x3b0 ]
mov [ rsp + 0x3c0 ], r11
mov r11, -0x3 
inc r11
adox rax, [ rsp + 0xe8 ]
adcx r10, r14
adox r9, [ rsp + 0x100 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r11, r14, rax
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x3c8 ], r8
mov byte [ rsp + 0x3d0 ], r13b
mulx r13, r8, rax
mov rdx, r14
mov [ rsp + 0x3d8 ], r13
setc r13b
clc
adcx rdx, r11
mov [ rsp + 0x3e0 ], r8
mov r8, r14
adcx r8, r11
adox r10, [ rsp + 0x158 ]
mov [ rsp + 0x3e8 ], rcx
setc cl
clc
adcx r14, rax
adcx rdx, r9
seto r14b
mov r9, -0x2 
inc r9
adox rdx, [ rsp - 0x10 ]
adcx r8, r10
setc r10b
clc
movzx r13, r13b
adcx r13, r9
adcx r15, rbx
mov rbx, 0x7bc65c783158aea3 
xchg rdx, rbx
mulx r9, r13, rax
seto dl
mov [ rsp + 0x3f0 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox r12, [ rsp + 0x250 ]
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov byte [ rsp + 0x3f8 ], al
mulx rax, r8, rbp
adox rdi, [ rsp + 0x320 ]
adcx r12, [ rsp + 0x3e8 ]
seto bpl
mov [ rsp + 0x400 ], rdi
mov rdi, 0x0 
dec rdi
movzx rcx, cl
adox rcx, rdi
adox r11, r8
seto cl
inc rdi
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox r15, [ rsp + 0x228 ]
setc r14b
clc
movzx rcx, cl
adcx rcx, r8
adcx rax, r13
adcx r9, [ rsp + 0x3e0 ]
setc r13b
clc
movzx r10, r10b
adcx r10, r8
adcx r15, r11
movzx r10, byte [ rsp + 0x3d0 ]
movzx r11, byte [ rsp + 0x390 ]
lea r10, [ r10 + r11 ]
adox r12, [ rsp + 0x200 ]
seto r11b
inc r8
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox r10, [ rsp + 0x318 ]
adcx rax, r12
mov rbp, 0xffffffffffffffff 
xchg rdx, rbx
mulx r12, rcx, rbp
mov rdi, rcx
setc bpl
clc
adcx rdi, r12
mov r8, rcx
adcx r8, r12
mov [ rsp + 0x408 ], r9
mov r9, 0x2341f27177344 
mov byte [ rsp + 0x410 ], bpl
mov [ rsp + 0x418 ], r8
mulx r8, rbp, r9
mov r9, 0x7bc65c783158aea3 
mov [ rsp + 0x420 ], r8
mov [ rsp + 0x428 ], r10
mulx r10, r8, r9
mov r9, [ rsp + 0x1d0 ]
mov [ rsp + 0x430 ], rdi
setc dil
mov byte [ rsp + 0x438 ], r11b
movzx r11, byte [ rsp + 0x3f8 ]
clc
mov [ rsp + 0x440 ], rbp
mov rbp, -0x1 
adcx r11, rbp
adcx r9, [ rsp + 0x3f0 ]
seto r11b
inc rbp
adox rcx, rdx
adcx r15, [ rsp + 0x1f8 ]
mov rcx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x448 ], r11b
mulx r11, rbp, rcx
mov rcx, 0x2341f27177344 
xchg rdx, rbx
mov [ rsp + 0x450 ], r15
mov [ rsp + 0x458 ], r9
mulx r9, r15, rcx
seto dl
mov rcx, 0x0 
dec rcx
movzx rdi, dil
adox rdi, rcx
adox r12, rbp
adox r8, r11
setc dil
clc
movzx r13, r13b
adcx r13, rcx
adcx r15, [ rsp + 0x3d8 ]
mov r13, 0x6cfc5fd681c52056 
xchg rdx, rbx
mulx r11, rbp, r13
adox rbp, r10
mov rdx, 0x0 
adcx r9, rdx
mov r10, [ rsp + 0x400 ]
clc
movzx r14, r14b
adcx r14, rcx
adcx r10, [ rsp + 0x3c8 ]
setc r14b
clc
movzx rdi, dil
adcx rdi, rcx
adcx rax, [ rsp + 0x1e8 ]
adox r11, [ rsp + 0x440 ]
seto dil
movzx rdx, byte [ rsp + 0x438 ]
inc rcx
mov rcx, -0x1 
adox rdx, rcx
adox r10, [ rsp + 0x1f0 ]
mov rdx, [ rsp + 0x458 ]
seto cl
mov r13, 0x0 
dec r13
movzx rbx, bl
adox rbx, r13
adox rdx, [ rsp + 0x430 ]
mov rbx, [ rsp + 0x428 ]
seto r13b
mov [ rsp + 0x460 ], r11
mov r11, 0x0 
dec r11
movzx r14, r14b
adox r14, r11
adox rbx, [ rsp + 0x3c0 ]
mov r14, [ rsp + 0x450 ]
setc r11b
clc
mov [ rsp + 0x468 ], rbp
mov rbp, -0x1 
movzx r13, r13b
adcx r13, rbp
adcx r14, [ rsp + 0x418 ]
seto r13b
inc rbp
mov rbp, -0x1 
movzx rcx, cl
adox rcx, rbp
adox rbx, [ rsp + 0x218 ]
seto cl
inc rbp
adox rdx, [ rsp - 0x40 ]
seto bpl
mov [ rsp + 0x470 ], r9
movzx r9, byte [ rsp + 0x410 ]
mov byte [ rsp + 0x478 ], cl
mov rcx, 0x0 
dec rcx
adox r9, rcx
adox r10, [ rsp + 0x408 ]
adox r15, rbx
movzx r9, dil
mov rbx, [ rsp + 0x420 ]
lea r9, [ r9 + rbx ]
mov rbx, 0x7bc65c783158aea3 
mulx rcx, rdi, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x480 ], r9
mov [ rsp + 0x488 ], rcx
mulx rcx, r9, rbx
mov rbx, r9
mov [ rsp + 0x490 ], rdi
setc dil
clc
adcx rbx, rdx
mov rbx, r9
mov [ rsp + 0x498 ], r8
setc r8b
clc
adcx rbx, rcx
adcx r9, rcx
mov [ rsp + 0x4a0 ], r9
setc r9b
clc
mov [ rsp + 0x4a8 ], rbx
mov rbx, -0x1 
movzx rbp, bpl
adcx rbp, rbx
adcx r14, [ rsp + 0xb0 ]
seto bpl
inc rbx
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r10, [ rsp + 0x2b8 ]
movzx r11, r13b
movzx rbx, byte [ rsp + 0x448 ]
lea r11, [ r11 + rbx ]
adox r15, [ rsp + 0x2d0 ]
setc bl
clc
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx rax, r12
mov r12, 0xfdc1767ae2ffffff 
mulx r13, rdi, r12
seto r12b
mov [ rsp + 0x4b0 ], r14
mov r14, 0x0 
dec r14
movzx rbx, bl
adox rbx, r14
adox rax, [ rsp + 0xf8 ]
seto bl
inc r14
mov r14, -0x1 
movzx r9, r9b
adox r9, r14
adox rcx, rdi
adcx r10, [ rsp + 0x498 ]
mov r9, 0x6cfc5fd681c52056 
mulx r14, rdi, r9
adox r13, [ rsp + 0x490 ]
adox rdi, [ rsp + 0x488 ]
seto r9b
mov [ rsp + 0x4b8 ], rdi
movzx rdi, byte [ rsp + 0x478 ]
mov [ rsp + 0x4c0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rdi, r13
adox r11, [ rsp + 0x248 ]
mov rdi, 0x2341f27177344 
mov [ rsp + 0x4c8 ], rcx
mulx rcx, r13, rdi
setc dl
clc
mov rdi, -0x1 
movzx r9, r9b
adcx r9, rdi
adcx r14, r13
setc r9b
clc
movzx rbp, bpl
adcx rbp, rdi
adcx r11, [ rsp + 0x470 ]
seto bpl
adc bpl, 0x0
movzx rbp, bpl
add bl, 0xFF
adcx r10, [ rsp + 0x220 ]
movzx r12, r12b
adox r12, rdi
adox r11, [ rsp + 0x2c8 ]
seto r12b
inc rdi
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox r15, [ rsp + 0x468 ]
adcx r15, [ rsp + 0x238 ]
mov rdx, [ rsp + 0x4b0 ]
setc r13b
clc
movzx r8, r8b
adcx r8, rbx
adcx rdx, [ rsp + 0x4a8 ]
adcx rax, [ rsp + 0x4a0 ]
adcx r10, [ rsp + 0x4c8 ]
movzx r8, r9b
lea r8, [ r8 + rcx ]
adox r11, [ rsp + 0x460 ]
seto cl
inc rbx
mov rdi, -0x1 
movzx r13, r13b
adox r13, rdi
adox r11, [ rsp + 0x2f0 ]
movzx r9, bpl
setc r13b
clc
movzx r12, r12b
adcx r12, rdi
adcx r9, [ rsp + 0x310 ]
seto bpl
inc rdi
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox r15, [ rsp + 0x4c0 ]
setc r12b
clc
movzx rcx, cl
adcx rcx, rbx
adcx r9, [ rsp + 0x480 ]
movzx r13, r12b
adcx r13, rdi
adox r11, [ rsp + 0x4b8 ]
clc
movzx rbp, bpl
adcx rbp, rbx
adcx r9, [ rsp + 0x308 ]
adcx r13, [ rsp + 0x300 ]
adox r14, r9
setc cl
clc
adcx rdx, [ rsp + 0x1b0 ]
adcx rax, [ rsp + 0x1b8 ]
mov rbp, 0x7bc65c783158aea3 
mulx r9, r12, rbp
mov rdi, 0x2341f27177344 
mulx rbp, rbx, rdi
mov rdi, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4d0 ], rbp
mov [ rsp + 0x4d8 ], rax
mulx rax, rbp, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x4e0 ], rbx
mov [ rsp + 0x4e8 ], r9
mulx r9, rbx, rdi
mov rdi, rbx
mov byte [ rsp + 0x4f0 ], cl
seto cl
mov [ rsp + 0x4f8 ], r12
mov r12, -0x2 
inc r12
adox rdi, rdx
seto dil
inc r12
mov r12, -0x1 
movzx rcx, cl
adox rcx, r12
adox r13, r8
adcx r10, [ rsp + 0x1e0 ]
adcx r15, [ rsp + 0x210 ]
mov r8, 0x6cfc5fd681c52056 
mulx r12, rcx, r8
adcx r11, [ rsp + 0x208 ]
mov rdx, rbx
setc r8b
clc
adcx rdx, r9
mov [ rsp + 0x500 ], r11
seto r11b
mov [ rsp + 0x508 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox r14, [ rsp + 0x2b0 ]
adox r13, [ rsp + 0x2c0 ]
adcx rbx, r9
adcx rbp, r9
adcx rax, [ rsp + 0x4f8 ]
movzx r9, r11b
movzx r8, byte [ rsp + 0x4f0 ]
lea r9, [ r9 + r8 ]
adcx rcx, [ rsp + 0x4e8 ]
adcx r12, [ rsp + 0x4e0 ]
setc r8b
clc
movzx rdi, dil
adcx rdi, r15
adcx rdx, [ rsp + 0x4d8 ]
adcx rbx, r10
adcx rbp, [ rsp + 0x508 ]
adcx rax, [ rsp + 0x500 ]
adcx rcx, r14
adcx r12, r13
movzx rdi, r8b
mov r11, [ rsp + 0x4d0 ]
lea rdi, [ rdi + r11 ]
setc r11b
seto r10b
mov r14, rdx
mov r13, 0xffffffffffffffff 
sub r14, r13
mov r8, rbx
sbb r8, r13
mov r15, rbp
sbb r15, r13
mov r13, 0x0 
dec r13
movzx r10, r10b
adox r10, r13
adox r9, [ rsp + 0x2f8 ]
seto r10b
mov r13, rax
mov [ rsp + 0x510 ], r8
mov r8, 0xfdc1767ae2ffffff 
sbb r13, r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r11, r11b
adox r11, r8
adox r9, rdi
seto r11b
mov rdi, rcx
mov r8, 0x7bc65c783158aea3 
sbb rdi, r8
mov r8, r12
mov [ rsp + 0x518 ], r13
mov r13, 0x6cfc5fd681c52056 
sbb r8, r13
movzx r13, r11b
movzx r10, r10b
lea r13, [ r13 + r10 ]
mov r10, r9
mov r11, 0x2341f27177344 
sbb r10, r11
sbb r13, 0x00000000
cmovc r15, rbp
cmovc r14, rdx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], r15
cmovc rdi, rcx
cmovc r8, r12
mov [ r13 + 0x0 ], r14
mov [ r13 + 0x20 ], rdi
cmovc r10, r9
mov rdx, [ rsp + 0x510 ]
cmovc rdx, rbx
mov rbx, [ rsp + 0x518 ]
cmovc rbx, rax
mov [ r13 + 0x8 ], rdx
mov [ r13 + 0x18 ], rbx
mov [ r13 + 0x28 ], r8
mov [ r13 + 0x30 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1440
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1303
; seed 1445662425849269 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 112718 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=22, initial num_batches=31): 1774 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01573839138380738
; number reverted permutation / tried permutation: 321 / 496 =64.718%
; number reverted decision / tried decision: 263 / 503 =52.286%
; validated in 392.742s
