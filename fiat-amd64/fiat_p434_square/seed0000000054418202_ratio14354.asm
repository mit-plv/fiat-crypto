SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1472
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r10
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r10
mulx r10, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], rax
mov [ rsp - 0x18 ], r9
mulx r9, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], rax
mulx rax, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rax
mov [ rsp + 0x8 ], r8
mulx r8, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rax
mov [ rsp + 0x28 ], r10
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], r14
mulx r14, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], r12
mulx r12, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], r14
mulx r14, r12, rdx
test al, al
adox rax, rbp
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x80 ], r14
mulx r14, rbp, rbx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r13
mulx r13, r12, rbx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r13
mulx r13, r15, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], r12
mov [ rsp + 0xb0 ], r14
mulx r14, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r12
mulx r12, r14, [ rsi + 0x8 ]
adox r11, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xc8 ], r12
mulx r12, r10, rbx
mov rdx, r10
adcx rdx, r12
mov [ rsp + 0xd0 ], r14
mov r14, r10
adcx r14, r12
mov [ rsp + 0xd8 ], r14
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0xe0 ], r11
mov [ rsp + 0xe8 ], rdi
mulx rdi, r11, rbx
adcx r11, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], r11
mulx r11, r12, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0xf8 ], r11
mov r11, -0x2 
inc r11
adox r10, rbx
adcx r15, rdi
adox r14, rax
setc r10b
clc
movzx rdx, dl
adcx rdx, r11
adcx rcx, r9
seto bl
inc r11
mov r9, -0x1 
movzx r10, r10b
adox r10, r9
adox r13, rbp
adcx r8, [ rsp + 0xe8 ]
mov rax, [ rsp + 0xb0 ]
adox rax, [ rsp + 0xa8 ]
mov rbp, [ rsp + 0xa0 ]
adox rbp, r11
mov rdx, [ rsi + 0x30 ]
mulx r10, rdi, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x98 ]
adcx rdx, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0x58 ]
mov r11, [ rsp + 0xe0 ]
inc r9
mov r9, -0x1 
movzx rbx, bl
adox rbx, r9
adox r11, [ rsp + 0xd8 ]
mov rbx, 0x0 
adcx r10, rbx
adox rcx, [ rsp + 0xf0 ]
adox r15, r8
adox r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, [ rsi + 0x8 ]
adox rax, rdi
clc
adcx r8, r14
adox rbp, r10
seto dl
inc r9
adox rbx, [ rsp + 0x50 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mulx r10, rdi, r8
mov r9, [ rsp + 0x30 ]
adox r9, [ rsp + 0x38 ]
adcx rbx, r11
adcx r9, rcx
mov r11, [ rsp + 0x28 ]
adox r11, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
adox rcx, [ rsp + 0x18 ]
adcx r11, r15
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x108 ], r14b
mulx r14, r15, [ rsi + 0x8 ]
adox r15, r12
adcx rcx, r13
mov rdx, [ rsi + 0x8 ]
mulx r12, r13, [ rsi + 0x30 ]
mov rdx, rdi
mov [ rsp + 0x110 ], rbp
seto bpl
mov [ rsp + 0x118 ], r12
mov r12, -0x2 
inc r12
adox rdx, r10
mov r12, rdi
mov [ rsp + 0x120 ], r13
seto r13b
mov [ rsp + 0x128 ], r14
mov r14, -0x2 
inc r14
adox r12, r8
adcx r15, rax
mov r12, r10
setc al
clc
movzx r13, r13b
adcx r13, r14
adcx r12, rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r8
mulx r14, r13, rdi
adcx r13, r10
adox r8, rbx
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rsi + 0x10 ]
adox r12, r9
adox r13, r11
mov rdx, 0x7bc65c783158aea3 
mulx r11, r9, r10
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x130 ], al
mov byte [ rsp + 0x138 ], bpl
mulx rbp, rax, [ rsi + 0x10 ]
adcx r9, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r15
mulx r15, r14, rdx
setc dl
clc
adcx rax, r8
mov r8, 0x7bc65c783158aea3 
xchg rdx, rax
mov [ rsp + 0x148 ], r15
mov [ rsp + 0x150 ], r11
mulx r11, r15, r8
adox r9, rcx
seto cl
mov r8, -0x2 
inc r8
adox rbx, rbp
adox r14, rdi
mov rdi, 0x6cfc5fd681c52056 
mulx r8, rbp, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x158 ], r8
mov [ rsp + 0x160 ], rbp
mulx rbp, r8, rdi
adcx rbx, r12
mov r12, r8
seto dil
mov [ rsp + 0x168 ], r11
mov r11, -0x2 
inc r11
adox r12, rbp
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x170 ], r9
mov byte [ rsp + 0x178 ], dil
mulx rdi, r9, r11
mov r11, r8
adox r11, rbp
adcx r14, r13
adox r9, rbp
setc r13b
clc
adcx r8, rdx
adcx r12, rbx
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x180 ], r9
mov [ rsp + 0x188 ], r11
mulx r11, r9, r10
setc dl
clc
adcx r12, [ rsp + 0x10 ]
adox r15, rdi
mov rdi, 0x7bc65c783158aea3 
xchg rdx, rdi
mov [ rsp + 0x190 ], r15
mov [ rsp + 0x198 ], r11
mulx r11, r15, r12
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1a0 ], r11
mov [ rsp + 0x1a8 ], r15
mulx r15, r11, r10
seto r10b
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx rax, al
adox rax, rdx
adox r11, [ rsp + 0x150 ]
setc al
clc
movzx rcx, cl
adcx rcx, rdx
adcx r11, [ rsp + 0x140 ]
seto cl
movzx rdx, byte [ rsp + 0x178 ]
mov byte [ rsp + 0x1b0 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox rdx, r10
adox rbp, [ rsp + 0x148 ]
setc dl
clc
movzx rcx, cl
adcx rcx, r10
adcx r15, r9
mov r9, [ rsp + 0x120 ]
setc cl
movzx r10, byte [ rsp + 0x138 ]
clc
mov [ rsp + 0x1b8 ], r15
mov r15, -0x1 
adcx r10, r15
adcx r9, [ rsp + 0x128 ]
adox rbx, [ rsp + 0x8 ]
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x1c0 ], cl
mulx rcx, r15, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x1c8 ], rcx
mov rcx, -0x1 
movzx r13, r13b
adcx r13, rcx
adcx rbp, [ rsp + 0x170 ]
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x1d0 ], r10b
mulx r10, rcx, [ rsi + 0x30 ]
adcx rbx, r11
movzx rdx, r13b
mov r11, [ rsp + 0x118 ]
lea rdx, [ rdx + r11 ]
setc r11b
clc
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx r14, [ rsp + 0x188 ]
adcx rbp, [ rsp + 0x180 ]
mov rdi, [ rsp + 0xd0 ]
setc r13b
clc
adcx rdi, [ rsp + 0x0 ]
adcx r15, [ rsp + 0xc8 ]
mov [ rsp + 0x1d8 ], rbx
mov rbx, [ rsp - 0x18 ]
adox rbx, [ rsp + 0x68 ]
mov byte [ rsp + 0x1e0 ], r13b
setc r13b
mov [ rsp + 0x1e8 ], r10
movzx r10, byte [ rsp + 0x130 ]
clc
mov [ rsp + 0x1f0 ], r15
mov r15, -0x1 
adcx r10, r15
adcx r9, [ rsp + 0x110 ]
adox rcx, [ rsp + 0x60 ]
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x1f8 ], r13b
mulx r13, r15, [ rsi + 0x20 ]
movzx rdx, byte [ rsp + 0x108 ]
adcx rdx, r10
seto r10b
mov [ rsp + 0x200 ], r13
mov r13, 0x0 
dec r13
movzx rax, al
adox rax, r13
adox r14, rdi
setc al
movzx rdi, byte [ rsp + 0x1d0 ]
clc
adcx rdi, r13
adcx r9, [ rsp + 0x1b8 ]
setc dil
clc
movzx r11, r11b
adcx r11, r13
adcx r9, rbx
adox rbp, [ rsp + 0x1f0 ]
movzx r11, byte [ rsp + 0x1c0 ]
mov rbx, [ rsp + 0x198 ]
lea r11, [ r11 + rbx ]
seto bl
inc r13
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox rdx, r11
mov rdi, 0xffffffffffffffff 
xchg rdx, r12
mulx r13, r11, rdi
adcx rcx, r12
movzx r12, r10b
mov rdi, [ rsp + 0x1e8 ]
lea r12, [ r12 + rdi ]
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x208 ], bl
mulx rbx, r10, [ rsi + 0x30 ]
mov rdx, r11
mov [ rsp + 0x210 ], rbx
seto bl
mov [ rsp + 0x218 ], r10
mov r10, -0x2 
inc r10
adox rdx, rdi
movzx rdx, bl
movzx rax, al
lea rdx, [ rdx + rax ]
adcx r12, rdx
mov rax, r11
setc bl
clc
adcx rax, r13
adox rax, r14
adcx r11, r13
mov r14, 0xfdc1767ae2ffffff 
mov rdx, rdi
mulx r10, rdi, r14
adcx rdi, r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x220 ], bl
mulx rbx, r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x228 ], rdi
mov [ rsp + 0x230 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
adox r11, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox rax, [ rsp - 0x8 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mov byte [ rsp + 0x238 ], bpl
mov [ rsp + 0x240 ], r12
mulx r12, rbp, rax
mov rdx, 0x2341f27177344 
mov [ rsp + 0x248 ], rbp
mov [ rsp + 0x250 ], r12
mulx r12, rbp, rax
adcx r10, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x258 ], r12
mov [ rsp + 0x260 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rsp + 0x168 ]
mov [ rsp + 0x268 ], r10
seto r10b
mov [ rsp + 0x270 ], rbp
movzx rbp, byte [ rsp + 0x1b0 ]
mov [ rsp + 0x278 ], r12
mov r12, 0x0 
dec r12
adox rbp, r12
adox rdx, [ rsp + 0x160 ]
setc bpl
clc
adcx r15, [ rsp - 0x10 ]
setc r12b
clc
mov byte [ rsp + 0x280 ], bpl
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx r11, r15
mov r10, 0x2341f27177344 
xchg rdx, r10
mulx rbp, r15, r8
adox r15, [ rsp + 0x158 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x288 ], r11
mulx r11, r8, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x290 ], r11
movzx r11, byte [ rsp + 0x1f8 ]
mov [ rsp + 0x298 ], rdi
mov rdi, 0x0 
dec rdi
adox r11, rdi
adox r14, [ rsp + 0x1c8 ]
movzx r11, dl
lea r11, [ r11 + rbp ]
mov rbp, 0x7bc65c783158aea3 
mov rdx, rbp
mulx rdi, rbp, rax
mov rdx, [ rsp + 0x1d8 ]
mov [ rsp + 0x2a0 ], rdi
setc dil
mov [ rsp + 0x2a8 ], rbp
movzx rbp, byte [ rsp + 0x1e0 ]
clc
mov [ rsp + 0x2b0 ], r14
mov r14, -0x1 
adcx rbp, r14
adcx rdx, [ rsp + 0x190 ]
adcx r10, r9
adcx r15, rcx
adox rbx, [ rsp + 0xc0 ]
adcx r11, [ rsp + 0x230 ]
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r9, rdx
mov rdx, [ rsp + 0x200 ]
seto r14b
mov [ rsp + 0x2b8 ], r11
mov r11, 0x0 
dec r11
movzx r12, r12b
adox r12, r11
adox rdx, [ rsp - 0x20 ]
adox r8, [ rsp - 0x38 ]
mov r12, [ rsp + 0xb8 ]
seto r11b
mov [ rsp + 0x2c0 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox r12, [ rsp + 0x298 ]
mov r14, [ rsp + 0x240 ]
adox r14, [ rsp + 0x218 ]
setc r8b
mov [ rsp + 0x2c8 ], r14
movzx r14, byte [ rsp + 0x208 ]
clc
mov [ rsp + 0x2d0 ], r12
mov r12, -0x1 
adcx r14, r12
adcx rbp, [ rsp + 0x2b0 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x2d8 ], r8b
mulx r8, r12, [ rsi + 0x28 ]
adcx rbx, r10
setc dl
clc
mov r10, -0x1 
movzx r11, r11b
adcx r11, r10
adcx r9, [ rsp + 0x290 ]
adcx rcx, [ rsp + 0x278 ]
mov r11, [ rsp + 0x250 ]
mov r10, r11
mov [ rsp + 0x2e0 ], rcx
seto cl
mov [ rsp + 0x2e8 ], r9
mov r9, -0x2 
inc r9
adox r10, [ rsp + 0x248 ]
setc r9b
mov [ rsp + 0x2f0 ], r15
movzx r15, byte [ rsp + 0x238 ]
clc
mov byte [ rsp + 0x2f8 ], dl
mov rdx, -0x1 
adcx r15, rdx
adcx rbp, [ rsp + 0x228 ]
mov r15, [ rsp - 0x40 ]
setc dl
clc
mov byte [ rsp + 0x300 ], cl
mov rcx, -0x1 
movzx r9, r9b
adcx r9, rcx
adcx r15, [ rsp + 0x270 ]
seto r9b
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox rbp, r14
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mulx rcx, r14, r13
seto dl
mov [ rsp + 0x308 ], r15
movzx r15, byte [ rsp + 0x280 ]
mov [ rsp + 0x310 ], rcx
mov rcx, 0x0 
dec rcx
adox r15, rcx
adox r14, [ rsp + 0x1a0 ]
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, r15
mov [ rsp + 0x318 ], r14
mulx r14, rcx, rax
mov rdx, rax
mov byte [ rsp + 0x320 ], r15b
setc r15b
clc
adcx rdx, [ rsp + 0x248 ]
adcx r10, [ rsp + 0x288 ]
mov rdx, r11
mov byte [ rsp + 0x328 ], r15b
setc r15b
clc
mov [ rsp + 0x330 ], r14
mov r14, -0x1 
movzx r9, r9b
adcx r9, r14
adcx rdx, [ rsp + 0x248 ]
seto r9b
inc r14
mov r14, -0x1 
movzx r15, r15b
adox r15, r14
adox rbp, rdx
mov r15, 0x2341f27177344 
mov rdx, r15
mulx r14, r15, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x338 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x340 ], r14
mov [ rsp + 0x348 ], r13
mulx r13, r14, [ rsi + 0x10 ]
adcx rcx, r11
setc dl
clc
adcx r12, r10
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x350 ], rcx
mulx rcx, r10, [ rsi + 0x30 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x358 ], r13
mov [ rsp + 0x360 ], r14
mulx r14, r13, r12
setc dl
clc
adcx r8, [ rsp + 0x48 ]
mov [ rsp + 0x368 ], r14
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mov [ rsp + 0x370 ], r13
mov [ rsp + 0x378 ], rcx
mulx rcx, r13, r12
setc dl
clc
mov [ rsp + 0x380 ], r15
mov r15, -0x1 
movzx rdi, dil
adcx rdi, r15
adcx rbx, [ rsp + 0x268 ]
mov rdi, [ rsp + 0x330 ]
seto r15b
mov byte [ rsp + 0x388 ], dl
mov rdx, 0x0 
dec rdx
movzx r11, r11b
adox r11, rdx
adox rdi, [ rsp + 0x2a8 ]
mov r11, r13
setc dl
clc
adcx r11, rcx
mov [ rsp + 0x390 ], rdi
seto dil
mov byte [ rsp + 0x398 ], r15b
mov r15, -0x2 
inc r15
adox r10, [ rsp - 0x28 ]
mov r15, r13
adcx r15, rcx
mov [ rsp + 0x3a0 ], r10
movzx r10, byte [ rsp + 0x300 ]
mov [ rsp + 0x3a8 ], r15
mov r15, [ rsp + 0x210 ]
lea r10, [ r10 + r15 ]
mov r15, [ rsp + 0x2f0 ]
mov byte [ rsp + 0x3b0 ], dil
seto dil
mov byte [ rsp + 0x3b8 ], dl
movzx rdx, byte [ rsp + 0x2f8 ]
mov byte [ rsp + 0x3c0 ], r9b
mov r9, 0x0 
dec r9
adox rdx, r9
adox r15, [ rsp + 0x2d0 ]
mov rdx, [ rsp + 0x2b8 ]
adox rdx, [ rsp + 0x2c8 ]
movzx r9, byte [ rsp + 0x2d8 ]
mov byte [ rsp + 0x3c8 ], dil
movzx rdi, byte [ rsp + 0x220 ]
lea r9, [ r9 + rdi ]
adox r10, r9
seto dil
movzx r9, byte [ rsp + 0x320 ]
mov [ rsp + 0x3d0 ], r10
mov r10, 0x0 
dec r10
adox r9, r10
adox rbx, [ rsp + 0x2c0 ]
setc r9b
clc
movzx r14, r14b
adcx r14, r10
adcx rbp, r8
setc r14b
clc
adcx r13, r12
adcx r11, rbp
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r8, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x380 ]
setc r10b
mov byte [ rsp + 0x3d8 ], r9b
movzx r9, byte [ rsp + 0x3c0 ]
clc
mov byte [ rsp + 0x3e0 ], r14b
mov r14, -0x1 
adcx r9, r14
adcx rdx, [ rsp + 0x310 ]
seto r9b
movzx r14, byte [ rsp + 0x3b8 ]
mov byte [ rsp + 0x3e8 ], r10b
mov r10, 0x0 
dec r10
adox r14, r10
adox r15, [ rsp + 0x318 ]
setc r14b
clc
adcx r11, [ rsp - 0x30 ]
mov r10, 0xffffffffffffffff 
xchg rdx, r10
mov [ rsp + 0x3f0 ], rbx
mov [ rsp + 0x3f8 ], rbp
mulx rbp, rbx, r11
adox r10, r13
mov r13, 0x6cfc5fd681c52056 
mov rdx, r11
mov [ rsp + 0x400 ], rbp
mulx rbp, r11, r13
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r12
mov [ rsp + 0x408 ], rbp
mov [ rsp + 0x410 ], r11
mulx r11, rbp, r13
xchg rdx, r13
mov [ rsp + 0x418 ], r11
mov [ rsp + 0x420 ], rbp
mulx rbp, r11, r12
movzx rdx, r14b
mov [ rsp + 0x428 ], rbp
mov rbp, [ rsp + 0x338 ]
lea rdx, [ rdx + rbp ]
mov rbp, 0x2341f27177344 
xchg rdx, r12
mov [ rsp + 0x430 ], r11
mulx r11, r14, rbp
mov rbp, rbx
mov [ rsp + 0x438 ], r11
setc r11b
clc
adcx rbp, rdx
mov rbp, [ rsp + 0x348 ]
mov [ rsp + 0x440 ], r14
seto r14b
mov byte [ rsp + 0x448 ], r11b
movzx r11, byte [ rsp + 0x3c8 ]
mov [ rsp + 0x450 ], r8
mov r8, 0x0 
dec r8
adox r11, r8
adox rbp, [ rsp + 0x378 ]
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x458 ], rbp
mulx rbp, r8, r11
setc dl
clc
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx r12, [ rsp + 0x3d0 ]
seto r14b
inc r11
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox r15, [ rsp + 0x2e8 ]
movzx r9, dil
mov r11, 0x0 
adcx r9, r11
mov dil, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x460 ], rbp
mulx rbp, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x468 ], dil
mov [ rsp + 0x470 ], r9
mulx r9, rdi, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x40 ]
mov [ rsp + 0x478 ], r8
movzx r8, byte [ rsp + 0x388 ]
clc
mov [ rsp + 0x480 ], r12
mov r12, -0x1 
adcx r8, r12
adcx rdx, [ rsp + 0x360 ]
adox r10, [ rsp + 0x2e0 ]
mov r8, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x488 ], r10
mulx r10, r12, [ rsi + 0x18 ]
adcx r11, [ rsp + 0x358 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x490 ], r11
mov [ rsp + 0x498 ], r15
mulx r15, r11, rdx
adcx rbp, [ rsp + 0x450 ]
mov rdx, [ rsp + 0x88 ]
adcx rdx, [ rsp + 0x3f8 ]
mov [ rsp + 0x4a0 ], r15
mov r15, [ rsp + 0x100 ]
adcx r15, [ rsp + 0x80 ]
mov [ rsp + 0x4a8 ], r15
seto r15b
mov [ rsp + 0x4b0 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r14, r14b
adox r14, rdx
adox r12, [ rsp + 0x340 ]
adox rdi, r10
mov r14, 0x6cfc5fd681c52056 
mov rdx, r14
mulx r10, r14, rax
setc al
movzx rdx, byte [ rsp + 0x3b0 ]
clc
mov [ rsp + 0x4b8 ], rdi
mov rdi, -0x1 
adcx rdx, rdi
adcx r14, [ rsp + 0x2a0 ]
adox r9, [ rsp + 0x78 ]
mov rdx, [ rsp + 0x3f0 ]
seto dil
mov [ rsp + 0x4c0 ], r9
movzx r9, byte [ rsp + 0x398 ]
mov [ rsp + 0x4c8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r9, r12
adox rdx, [ rsp + 0x350 ]
seto r9b
movzx r12, byte [ rsp + 0x3e0 ]
mov byte [ rsp + 0x4d0 ], al
mov rax, -0x1 
inc rax
mov rax, -0x1 
adox r12, rax
adox rdx, r8
mov r12, rbx
seto r8b
inc rax
adox r12, [ rsp + 0x400 ]
adcx r10, [ rsp + 0x260 ]
mov rax, [ rsp + 0x498 ]
mov [ rsp + 0x4d8 ], r12
setc r12b
clc
mov [ rsp + 0x4e0 ], rdx
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx rax, [ rsp + 0x390 ]
mov r9, [ rsp + 0x480 ]
seto dl
mov [ rsp + 0x4e8 ], rbp
mov rbp, 0x0 
dec rbp
movzx r15, r15b
adox r15, rbp
adox r9, [ rsp + 0x308 ]
adcx r14, [ rsp + 0x488 ]
adcx r10, r9
mov r15, 0x7bc65c783158aea3 
xchg rdx, r13
mulx rbp, r9, r15
movzx r15, r12b
mov [ rsp + 0x4f0 ], r10
mov r10, [ rsp + 0x258 ]
lea r15, [ r15 + r10 ]
movzx r10, byte [ rsp + 0x328 ]
mov r12, [ rsp - 0x48 ]
lea r10, [ r10 + r12 ]
seto r12b
mov [ rsp + 0x4f8 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r13, r13b
adox r13, r15
adox rbx, [ rsp + 0x400 ]
seto r13b
movzx r15, byte [ rsp + 0x3d8 ]
mov [ rsp + 0x500 ], rbx
mov rbx, 0x0 
dec rbx
adox r15, rbx
adox rcx, [ rsp + 0x420 ]
mov r15, [ rsp + 0x400 ]
setc bl
clc
mov [ rsp + 0x508 ], rcx
mov rcx, -0x1 
movzx r13, r13b
adcx r13, rcx
adcx r15, [ rsp + 0x430 ]
seto r13b
inc rcx
mov rcx, -0x1 
movzx rdi, dil
adox rdi, rcx
adox r11, [ rsp + 0x70 ]
seto dil
inc rcx
mov rcx, -0x1 
movzx r13, r13b
adox r13, rcx
adox r9, [ rsp + 0x418 ]
mov r13, [ rsp + 0x478 ]
adcx r13, [ rsp + 0x428 ]
mov rcx, 0x2341f27177344 
mov [ rsp + 0x510 ], r11
mov [ rsp + 0x518 ], r13
mulx r13, r11, rcx
adox rbp, [ rsp + 0x370 ]
adox r11, [ rsp + 0x368 ]
setc dl
clc
mov rcx, -0x1 
movzx r8, r8b
adcx r8, rcx
adcx rax, [ rsp + 0x490 ]
adcx r14, [ rsp + 0x4e8 ]
mov r8, [ rsp + 0x4e0 ]
seto cl
mov byte [ rsp + 0x520 ], dil
movzx rdi, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x528 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rdi, r11
adox r8, [ rsp + 0x3a8 ]
movzx rdi, cl
lea rdi, [ rdi + r13 ]
setc r13b
clc
movzx r12, r12b
adcx r12, r11
adcx r10, [ rsp + 0x470 ]
movzx r12, byte [ rsp + 0x4d0 ]
mov rcx, [ rsp + 0xf8 ]
lea r12, [ r12 + rcx ]
adox rax, [ rsp + 0x508 ]
adox r9, r14
setc cl
clc
movzx rbx, bl
adcx rbx, r11
adcx r10, [ rsp + 0x4f8 ]
mov rbx, [ rsp + 0x4b0 ]
setc r14b
clc
movzx r13, r13b
adcx r13, r11
adcx rbx, [ rsp + 0x4f0 ]
adcx r10, [ rsp + 0x4a8 ]
adox rbp, rbx
movzx r13, r14b
movzx rcx, cl
lea r13, [ r13 + rcx ]
adcx r12, r13
setc cl
movzx r14, byte [ rsp + 0x448 ]
clc
adcx r14, r11
adcx r8, [ rsp + 0x3a0 ]
adcx rax, [ rsp + 0x458 ]
adcx r9, [ rsp + 0x4c8 ]
seto r14b
movzx rbx, byte [ rsp + 0x468 ]
inc r11
mov r13, -0x1 
adox rbx, r13
adox r8, [ rsp + 0x4d8 ]
adox rax, [ rsp + 0x500 ]
adox r15, r9
mov rbx, [ rsp + 0x410 ]
setc r9b
clc
movzx rdx, dl
adcx rdx, r13
adcx rbx, [ rsp + 0x460 ]
seto dl
dec r11
movzx r14, r14b
adox r14, r11
adox r10, [ rsp + 0x528 ]
adox rdi, r12
setc r13b
clc
movzx r9, r9b
adcx r9, r11
adcx rbp, [ rsp + 0x4b8 ]
adcx r10, [ rsp + 0x4c0 ]
mov r14, [ rsp + 0x408 ]
seto r12b
inc r11
mov r9, -0x1 
movzx r13, r13b
adox r13, r9
adox r14, [ rsp + 0x440 ]
mov r13, [ rsp + 0x438 ]
adox r13, r11
movzx r11, byte [ rsp + 0x520 ]
mov r9, [ rsp + 0x4a0 ]
lea r11, [ r11 + r9 ]
mov r9, 0x0 
dec r9
movzx rdx, dl
adox rdx, r9
adox rbp, [ rsp + 0x518 ]
movzx rdx, r12b
movzx rcx, cl
lea rdx, [ rdx + rcx ]
adox rbx, r10
adcx rdi, [ rsp + 0x510 ]
adox r14, rdi
adcx r11, rdx
adox r13, r11
seto cl
adc cl, 0x0
movzx rcx, cl
mov r12, r8
mov r10, 0xffffffffffffffff 
sub r12, r10
mov rdx, rax
sbb rdx, r10
mov rdi, r15
sbb rdi, r10
mov r11, rbp
mov r9, 0xfdc1767ae2ffffff 
sbb r11, r9
mov r9, rbx
mov r10, 0x7bc65c783158aea3 
sbb r9, r10
mov r10, r14
mov [ rsp + 0x530 ], r9
mov r9, 0x6cfc5fd681c52056 
sbb r10, r9
mov r9, r13
mov [ rsp + 0x538 ], r10
mov r10, 0x2341f27177344 
sbb r9, r10
movzx r10, cl
sbb r10, 0x00000000
cmovc rdx, rax
cmovc r11, rbp
cmovc r12, r8
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x0 ], r12
mov [ r10 + 0x8 ], rdx
cmovc rdi, r15
mov [ r10 + 0x10 ], rdi
mov [ r10 + 0x18 ], r11
mov r8, [ rsp + 0x530 ]
cmovc r8, rbx
mov [ r10 + 0x20 ], r8
mov rax, [ rsp + 0x538 ]
cmovc rax, r14
cmovc r9, r13
mov [ r10 + 0x28 ], rax
mov [ r10 + 0x30 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1472
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4354
; seed 1571851804729870 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10678378 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 186421 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01745780117542196
; number reverted permutation / tried permutation: 50252 / 90069 =55.793%
; number reverted decision / tried decision: 42243 / 89930 =46.973%
; validated in 320.66s
