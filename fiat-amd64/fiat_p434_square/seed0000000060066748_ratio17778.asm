SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1208
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r8
mulx r8, rbx, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], rcx
mulx rcx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r9
mulx r9, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r9
mov [ rsp + 0x28 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], rcx
mulx rcx, r9, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], r15
mov [ rsp + 0x48 ], r11
mulx r11, r15, rdx
mov rdx, r9
add rdx, rcx
mov [ rsp + 0x50 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r10
mulx r10, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r10
mov [ rsp + 0x70 ], r15
mulx r15, r10, [ rsi + 0x0 ]
mov rdx, r9
adcx rdx, rcx
adcx rdi, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], r15
mulx r15, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], rcx
mulx rcx, rdi, [ rsi + 0x28 ]
adcx rbx, rbp
adcx r14, r8
mov rdx, [ rsi + 0x28 ]
mulx r8, rbp, [ rsi + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x98 ], rcx
mov [ rsp + 0xa0 ], rdi
mulx rdi, rcx, r12
mov rdx, -0x2 
inc rdx
adox r10, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r8
mulx r8, r13, [ rsi + 0x10 ]
adox r13, r15
adox rax, r8
mov rdx, [ rsp + 0x60 ]
adox rdx, [ rsp + 0x48 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], rbp
mulx rbp, r8, [ rsi + 0x30 ]
adcx rcx, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rbp
mov [ rsp + 0xc0 ], r8
mulx r8, rbp, rdx
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r8
mulx r8, rdi, [ rsi + 0x30 ]
clc
adcx r9, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r8
mov [ rsp + 0xe0 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
adox r9, [ rsp + 0x8 ]
adcx r11, r10
adox rdi, r12
adcx r13, [ rsp + 0x90 ]
setc dl
clc
adcx r8, r11
mov r10, 0x7bc65c783158aea3 
xchg rdx, r8
mulx r11, r12, r10
seto r10b
mov [ rsp + 0xe8 ], r11
mov r11, 0x0 
dec r11
movzx r8, r8b
adox r8, r11
adox rax, [ rsp + 0x88 ]
adox rbx, r15
adox r14, r9
adox rcx, rdi
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, r9, [ rsi + 0x8 ]
seto dl
inc r11
adox rbp, [ rsp + 0xe0 ]
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0xf0 ], r12
mulx r12, r11, r15
adcx rbp, r13
mov r13, [ rsp + 0xd0 ]
adox r13, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], r11
mulx r11, r12, [ rsi + 0x8 ]
adox r12, [ rsp - 0x18 ]
adox r9, r11
adcx r13, rax
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, [ rsi + 0x28 ]
adcx r12, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x108 ], r12
mulx r12, rbx, r15
adcx r9, r14
mov r14, rbx
setc dl
clc
adcx r14, r12
mov [ rsp + 0x110 ], r9
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov [ rsp + 0x118 ], r11
mov [ rsp + 0x120 ], r13
mulx r13, r11, r15
mov rdx, rbx
adcx rdx, r12
adox rax, rdi
seto dil
mov [ rsp + 0x128 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r9, r9b
adox r9, r13
adox rcx, rax
setc r9b
clc
adcx rbx, r15
adcx r14, rbp
movzx rbx, r10b
mov rbp, [ rsp + 0xd8 ]
lea rbx, [ rbx + rbp ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x130 ], rcx
mulx rcx, r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r11
mov byte [ rsp + 0x140 ], r9b
mulx r9, r11, [ rsi + 0x8 ]
seto dl
mov byte [ rsp + 0x148 ], dil
mov rdi, 0x0 
dec rdi
movzx r8, r8b
adox r8, rdi
adox rbx, [ rsp + 0xc8 ]
seto r8b
inc rdi
adox r10, r14
mov r14, 0x2341f27177344 
xchg rdx, r14
mov byte [ rsp + 0x150 ], r8b
mulx r8, rdi, r10
mov [ rsp + 0x158 ], r8
mov [ rsp + 0x160 ], rdi
mulx rdi, r8, r15
adcx rbp, [ rsp + 0x120 ]
setc r15b
clc
adcx r11, rax
adcx r13, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, rax, [ rsi + 0x10 ]
adox r11, rbp
adcx rcx, [ rsp - 0x20 ]
mov rdx, [ rsp + 0x28 ]
seto bpl
mov [ rsp + 0x168 ], r11
movzx r11, byte [ rsp + 0x148 ]
mov [ rsp + 0x170 ], rcx
mov rcx, 0x0 
dec rcx
adox r11, rcx
adox rdx, [ rsp + 0x118 ]
adcx rax, [ rsp - 0x38 ]
setc r11b
movzx rcx, byte [ rsp + 0x140 ]
clc
mov [ rsp + 0x178 ], rax
mov rax, -0x1 
adcx rcx, rax
adcx r12, [ rsp + 0x138 ]
mov rcx, [ rsp + 0x128 ]
adcx rcx, [ rsp + 0xf0 ]
seto al
mov [ rsp + 0x180 ], r9
mov r9, 0x0 
dec r9
movzx r14, r14b
adox r14, r9
adox rbx, rdx
mov r14, [ rsp + 0xe8 ]
adcx r14, [ rsp + 0x100 ]
adcx r8, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x188 ], r11b
mulx r11, r9, [ rsi + 0x28 ]
movzx rdx, al
mov [ rsp + 0x190 ], r11
mov r11, [ rsp + 0x20 ]
lea rdx, [ rdx + r11 ]
mov r11, 0x0 
adcx rdi, r11
movzx rax, byte [ rsp + 0x150 ]
adox rax, rdx
clc
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx r12, [ rsp + 0x108 ]
seto r15b
inc rdx
mov r11, -0x1 
movzx rbp, bpl
adox rbp, r11
adox r12, r13
adcx rcx, [ rsp + 0x110 ]
adcx r14, [ rsp + 0x130 ]
adcx r8, rbx
mov rdx, [ rsi + 0x30 ]
mulx rbp, r13, [ rsi + 0x10 ]
seto dl
movzx rbx, byte [ rsp + 0x188 ]
inc r11
mov r11, -0x1 
adox rbx, r11
adox r9, [ rsp + 0x180 ]
adox r13, [ rsp + 0x190 ]
adcx rdi, rax
mov rbx, 0xffffffffffffffff 
xchg rdx, r10
mulx r11, rax, rbx
mov rbx, rax
mov byte [ rsp + 0x198 ], r15b
setc r15b
clc
adcx rbx, r11
mov byte [ rsp + 0x1a0 ], r15b
mov r15, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a8 ], r13
mov [ rsp + 0x1b0 ], rdi
mulx rdi, r13, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x1b8 ], r13
mov r13, 0x0 
dec r13
movzx r10, r10b
adox r10, r13
adox rcx, [ rsp + 0x170 ]
adox r14, [ rsp + 0x178 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov [ rsp + 0x1c0 ], rbp
mulx rbp, r13, r15
mov rdx, rax
adcx rdx, r11
adox r9, r8
seto r8b
mov byte [ rsp + 0x1c8 ], r10b
mov r10, -0x2 
inc r10
adox rax, r15
adox rbx, [ rsp + 0x168 ]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x1d0 ], r8b
mulx r8, r10, [ rsi + 0x30 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1d8 ], r8
mov [ rsp + 0x1e0 ], r10
mulx r10, r8, r15
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1e8 ], rbx
mov [ rsp + 0x1f0 ], r9
mulx r9, rbx, r15
adcx r13, r11
adcx rbx, rbp
adox rax, r12
adox r13, rcx
adcx r8, r9
mov rdx, [ rsi + 0x18 ]
mulx r12, r15, [ rsi + 0x8 ]
adcx r10, [ rsp + 0x160 ]
adox rbx, r14
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x28 ]
setc dl
clc
adcx rdi, [ rsp + 0x18 ]
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rsi + 0x18 ]
adox r8, [ rsp + 0x1f0 ]
seto dl
mov [ rsp + 0x1f8 ], rdi
mov rdi, -0x2 
inc rdi
adox rbp, [ rsp + 0x1e8 ]
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x200 ], r10
mov [ rsp + 0x208 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x10 ]
adcx rdx, [ rsp + 0x1e0 ]
mov byte [ rsp + 0x210 ], dil
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x218 ], rbx
mov [ rsp + 0x220 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
movzx rdx, r14b
mov [ rsp + 0x228 ], rdi
mov rdi, [ rsp + 0x158 ]
lea rdx, [ rdx + rdi ]
setc dil
clc
adcx r15, r9
adcx r12, [ rsp - 0x8 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x230 ], dil
mulx rdi, r9, [ rsi + 0x18 ]
adox r15, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x238 ], r14
mulx r14, rax, rdx
adcx rax, [ rsp - 0x10 ]
adcx r10, r14
adcx r11, r8
adcx r9, rcx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rsi + 0x10 ]
setc dl
clc
adcx rbx, [ rsp + 0x80 ]
adcx rcx, r13
mov r13, 0x7bc65c783158aea3 
xchg rdx, r13
mov [ rsp + 0x240 ], rcx
mulx rcx, r14, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x248 ], r9
mov [ rsp + 0x250 ], r11
mulx r11, r9, [ rsi + 0x28 ]
adcx r8, [ rsp - 0x28 ]
movzx rdx, r13b
lea rdx, [ rdx + rdi ]
mov rdi, [ rsp - 0x30 ]
adcx rdi, [ rsp + 0x58 ]
adox r12, [ rsp + 0x220 ]
adox rax, [ rsp + 0x218 ]
adcx r9, [ rsp + 0x50 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x258 ], r9
mov [ rsp + 0x260 ], rdi
mulx rdi, r9, rbp
movzx rdx, byte [ rsp + 0x1c8 ]
mov [ rsp + 0x268 ], r8
mov r8, [ rsp + 0x1c0 ]
lea rdx, [ rdx + r8 ]
adcx r11, [ rsp + 0xc0 ]
adox r10, [ rsp + 0x208 ]
mov r8, [ rsp + 0xb8 ]
mov [ rsp + 0x270 ], r11
mov r11, 0x0 
adcx r8, r11
mov [ rsp + 0x278 ], r8
mov r8, r9
clc
adcx r8, rdi
mov r11, r9
adcx r11, rdi
mov [ rsp + 0x280 ], r10
seto r10b
mov [ rsp + 0x288 ], r13
mov r13, -0x2 
inc r13
adox r9, rbp
adox r8, r15
adox r11, r12
mov r9, [ rsp + 0x1b0 ]
seto r15b
movzx r12, byte [ rsp + 0x1d0 ]
inc r13
mov r13, -0x1 
adox r12, r13
adox r9, [ rsp + 0x1a8 ]
setc r12b
clc
adcx r8, [ rsp + 0x78 ]
adcx rbx, r11
movzx r11, byte [ rsp + 0x1a0 ]
movzx r13, byte [ rsp + 0x198 ]
lea r11, [ r11 + r13 ]
adox rdx, r11
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x290 ], rax
mulx rax, r11, r8
setc dl
mov byte [ rsp + 0x298 ], r15b
movzx r15, byte [ rsp + 0x210 ]
clc
mov byte [ rsp + 0x2a0 ], r10b
mov r10, -0x1 
adcx r15, r10
adcx r9, [ rsp + 0x200 ]
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov byte [ rsp + 0x2a8 ], bpl
mulx rbp, r10, r15
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x2b0 ], r9
mov [ rsp + 0x2b8 ], rcx
mulx rcx, r9, r15
mov r15, 0x2341f27177344 
mov [ rsp + 0x2c0 ], rcx
mov [ rsp + 0x2c8 ], r9
mulx r9, rcx, r15
seto r15b
mov [ rsp + 0x2d0 ], r9
mov r9, 0x0 
dec r9
movzx r12, r12b
adox r12, r9
adox rdi, r10
adcx r13, [ rsp + 0x238 ]
mov r12, [ rsp + 0x70 ]
setc r10b
clc
adcx r12, [ rsp + 0x38 ]
movzx r9, r10b
movzx r15, r15b
lea r9, [ r9 + r15 ]
mov r15, r11
seto r10b
mov [ rsp + 0x2d8 ], r12
mov r12, -0x2 
inc r12
adox r15, rax
mov r12, [ rsp + 0x68 ]
adcx r12, [ rsp - 0x40 ]
mov [ rsp + 0x2e0 ], r12
mov r12, r11
mov [ rsp + 0x2e8 ], rcx
setc cl
clc
adcx r12, rdx
adcx r15, rbx
adox r11, rax
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2f0 ], r11
mulx r11, rbx, r12
adox rbx, rax
mov rax, 0x2341f27177344 
xchg rdx, rax
mov [ rsp + 0x2f8 ], rbx
mulx rbx, r12, r8
setc dl
clc
adcx r15, [ rsp + 0x30 ]
mov byte [ rsp + 0x300 ], dl
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0x308 ], r11
setc r11b
clc
mov [ rsp + 0x310 ], rbx
mov rbx, -0x1 
movzx rcx, cl
adcx rcx, rbx
adcx rdx, [ rsp + 0xb0 ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x318 ], rcx
mulx rcx, rbx, r8
mov r8, 0xffffffffffffffff 
mov rdx, r15
mov byte [ rsp + 0x320 ], r11b
mulx r11, r15, r8
setc r8b
clc
mov [ rsp + 0x328 ], r15
mov r15, -0x1 
movzx r10, r10b
adcx r10, r15
adcx rbp, r14
adcx rbx, [ rsp + 0x2b8 ]
mov r14, [ rsp + 0x2b0 ]
seto r10b
movzx r15, byte [ rsp + 0x2a0 ]
mov [ rsp + 0x330 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox r15, r11
adox r14, [ rsp + 0x250 ]
adox r13, [ rsp + 0x248 ]
adcx r12, rcx
setc r15b
movzx rcx, byte [ rsp + 0x298 ]
clc
adcx rcx, r11
adcx rdi, [ rsp + 0x290 ]
adox r9, [ rsp + 0x288 ]
movzx rcx, r15b
mov r11, [ rsp + 0x310 ]
lea rcx, [ rcx + r11 ]
adcx rbp, [ rsp + 0x280 ]
seto r11b
movzx r15, byte [ rsp + 0x2a8 ]
mov byte [ rsp + 0x338 ], r8b
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox r15, r8
adox rdi, [ rsp + 0x240 ]
adox rbp, [ rsp + 0x268 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x340 ], rbp
mulx rbp, r8, rax
adcx rbx, r14
adcx r12, r13
adox rbx, [ rsp + 0x260 ]
adox r12, [ rsp + 0x258 ]
adcx rcx, r9
movzx rax, r11b
mov r14, 0x0 
adcx rax, r14
clc
mov r13, -0x1 
movzx r10, r10b
adcx r10, r13
adcx r8, [ rsp + 0x308 ]
adcx rbp, [ rsp + 0x2c8 ]
mov r10, [ rsp + 0x2c0 ]
adcx r10, [ rsp + 0x2e8 ]
mov r11, [ rsp + 0xa8 ]
setc r9b
movzx r14, byte [ rsp + 0x338 ]
clc
adcx r14, r13
adcx r11, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, [ rsi + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x348 ], r9b
mov [ rsp + 0x350 ], r13
mulx r13, r9, r15
mov rdx, [ rsp + 0x328 ]
mov [ rsp + 0x358 ], r10
mov r10, rdx
mov [ rsp + 0x360 ], r11
setc r11b
clc
adcx r10, [ rsp + 0x330 ]
mov byte [ rsp + 0x368 ], r11b
mov r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x370 ], r10
mov [ rsp + 0x378 ], r14
mulx r14, r10, [ rsi + 0x20 ]
mov rdx, r11
adcx rdx, [ rsp + 0x330 ]
adcx r9, [ rsp + 0x330 ]
mov [ rsp + 0x380 ], r14
mov r14, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x388 ], r10
mov [ rsp + 0x390 ], r9
mulx r9, r10, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x398 ], r15
mov [ rsp + 0x3a0 ], rbp
mulx rbp, r15, r14
adcx r10, r13
adox rcx, [ rsp + 0x270 ]
mov r13, 0x2341f27177344 
mov [ rsp + 0x3a8 ], r10
mulx r10, r14, r13
adcx r15, r9
adox rax, [ rsp + 0x278 ]
adcx r14, rbp
seto r9b
movzx rbp, byte [ rsp + 0x300 ]
mov r13, 0x0 
dec r13
adox rbp, r13
adox rdi, [ rsp + 0x2f0 ]
setc bpl
movzx r13, byte [ rsp + 0x320 ]
clc
mov [ rsp + 0x3b0 ], r14
mov r14, -0x1 
adcx r13, r14
adcx rdi, [ rsp + 0x2d8 ]
mov r13, [ rsp + 0x340 ]
adox r13, [ rsp + 0x2f8 ]
adox r8, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x3b8 ], r10
mulx r10, r14, [ rsi + 0x28 ]
adcx r13, [ rsp + 0x2e0 ]
adcx r8, [ rsp + 0x318 ]
adox r12, [ rsp + 0x3a0 ]
mov rdx, [ rsp + 0x378 ]
mov byte [ rsp + 0x3c0 ], bpl
seto bpl
mov [ rsp + 0x3c8 ], r15
movzx r15, byte [ rsp + 0x230 ]
mov [ rsp + 0x3d0 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r15, r10
adox rdx, [ rsp + 0x1d8 ]
adcx r12, [ rsp + 0x360 ]
setc r15b
clc
movzx rbp, bpl
adcx rbp, r10
adcx rcx, [ rsp + 0x358 ]
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x3d8 ], rcx
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x3e0 ], rcx
mov byte [ rsp + 0x3e8 ], r15b
mulx r15, rcx, [ rsi + 0x28 ]
seto dl
mov byte [ rsp + 0x3f0 ], r9b
mov r9, -0x2 
inc r9
adox r11, rbx
adox rdi, [ rsp + 0x370 ]
setc r11b
clc
adcx rdi, [ rsp + 0x1b8 ]
adox r13, [ rsp + 0x398 ]
adcx r13, [ rsp + 0x1f8 ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov [ rsp + 0x3f8 ], r13
mulx r13, r9, rbx
adox r8, [ rsp + 0x390 ]
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0x400 ], r13
mov [ rsp + 0x408 ], r9
mulx r9, r13, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x410 ], r9
mov [ rsp + 0x418 ], r13
mulx r13, r9, rdx
adox r12, [ rsp + 0x3a8 ]
adcx r8, [ rsp + 0x228 ]
adcx rbp, r12
mov rdx, [ rsp + 0x350 ]
setc r12b
clc
mov [ rsp + 0x420 ], rbp
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx rdx, [ rsp + 0x388 ]
adcx rcx, [ rsp + 0x380 ]
adcx r10, r15
setc dil
movzx r15, byte [ rsp + 0x368 ]
clc
adcx r15, rbp
adcx r9, [ rsp + 0x98 ]
movzx r15, byte [ rsp + 0x348 ]
mov rbp, [ rsp + 0x2d0 ]
lea r15, [ r15 + rbp ]
adcx r14, r13
setc bpl
clc
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx rax, r15
movzx r11, byte [ rsp + 0x3f0 ]
mov r15, 0x0 
adcx r11, r15
movzx r15, bpl
mov r13, [ rsp + 0x3d0 ]
lea r15, [ r15 + r13 ]
movzx r13, byte [ rsp + 0x3e8 ]
clc
mov rbp, -0x1 
adcx r13, rbp
adcx r9, [ rsp + 0x3d8 ]
adox r9, [ rsp + 0x3c8 ]
adcx r14, rax
adcx r15, r11
movzx r13, byte [ rsp + 0x3c0 ]
mov rax, [ rsp + 0x3b8 ]
lea r13, [ r13 + rax ]
adox r14, [ rsp + 0x3b0 ]
adox r13, r15
seto al
adc al, 0x0
movzx rax, al
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mulx rbp, r15, rbx
add r12b, 0x7F
adox r9, r11
adox rcx, r14
mov r12, r15
adcx r12, rbx
mov r12, 0xfdc1767ae2ffffff 
mov rdx, rbx
mulx r11, rbx, r12
adox r10, r13
mov r14, r15
seto r13b
mov r12, -0x2 
inc r12
adox r14, rbp
adox r15, rbp
adox rbx, rbp
adox r11, [ rsp + 0x418 ]
adcx r14, [ rsp + 0x3f8 ]
adcx r15, r8
mov r8, [ rsp + 0x410 ]
adox r8, [ rsp + 0x408 ]
mov rbp, 0x2341f27177344 
mov [ rsp + 0x428 ], r15
mulx r15, r12, rbp
adox r12, [ rsp + 0x400 ]
adcx rbx, [ rsp + 0x420 ]
adcx r11, r9
adcx r8, rcx
adcx r12, r10
movzx rdx, dil
mov r9, [ rsp + 0x3e0 ]
lea rdx, [ rdx + r9 ]
setc r9b
clc
mov rdi, -0x1 
movzx rax, al
movzx r13, r13b
adcx r13, rdi
adcx rdx, rax
setc al
seto cl
mov r13, r14
mov r10, 0xffffffffffffffff 
sub r13, r10
mov rdi, [ rsp + 0x428 ]
sbb rdi, r10
mov rbp, rbx
sbb rbp, r10
movzx r10, cl
lea r10, [ r10 + r15 ]
mov r15, r11
mov rcx, 0xfdc1767ae2ffffff 
sbb r15, rcx
mov rcx, r8
mov [ rsp + 0x430 ], rbp
mov rbp, 0x7bc65c783158aea3 
sbb rcx, rbp
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox rdx, r10
movzx r9, al
mov r10, 0x0 
adox r9, r10
mov rax, r12
mov r10, 0x6cfc5fd681c52056 
sbb rax, r10
mov rbp, rdx
mov r10, 0x2341f27177344 
sbb rbp, r10
sbb r9, 0x00000000
cmovc r15, r11
cmovc rdi, [ rsp + 0x428 ]
cmovc rbp, rdx
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], r15
mov [ r9 + 0x8 ], rdi
cmovc rax, r12
cmovc rcx, r8
cmovc r13, r14
mov [ r9 + 0x20 ], rcx
mov r14, [ rsp + 0x430 ]
cmovc r14, rbx
mov [ r9 + 0x30 ], rbp
mov [ r9 + 0x28 ], rax
mov [ r9 + 0x0 ], r13
mov [ r9 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1208
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.7778
; seed 3923531179288353 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11115281 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 184887 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016633587580916757
; number reverted permutation / tried permutation: 49614 / 89830 =55.231%
; number reverted decision / tried decision: 41060 / 90169 =45.537%
; validated in 322.13s
