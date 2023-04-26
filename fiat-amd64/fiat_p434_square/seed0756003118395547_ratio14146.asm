SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1536
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r15
mulx r15, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r12
mulx r12, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rdi
mulx rdi, r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r12
mov [ rsp + 0x18 ], rdi
mulx rdi, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r12
mov [ rsp + 0x48 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], r9
mulx r9, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], r13
mulx r13, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r13
mulx r13, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r8
mov [ rsp + 0x88 ], r13
mulx r13, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], rbx
mulx rbx, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], r8
mulx r8, rbx, [ rsi + 0x30 ]
xor rdx, rdx
adox rax, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], rax
mulx rax, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r8
mov [ rsp + 0xc0 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], rax
mulx rax, r8, [ rsi + 0x0 ]
adcx rcx, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], rcx
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe0 ], rax
mov [ rsp + 0xe8 ], r13
mulx r13, rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], r13
mulx r13, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r8
mulx r8, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], rax
mov [ rsp + 0x118 ], r14
mulx r14, rax, [ rsi + 0x8 ]
setc dl
clc
adcx rbp, rbx
adcx r10, r9
adcx r13, rcx
mov r9b, dl
mov rdx, [ rsi + 0x30 ]
mulx rcx, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], r13
mov [ rsp + 0x128 ], r10
mulx r10, r13, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x130 ], rbp
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox rdi, r11
mov r11b, dl
mov rdx, [ rsi + 0x20 ]
mulx rbp, r9, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x138 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r11, r11b
adox r11, rdi
adox r15, rax
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mulx rdi, rax, [ rsi + 0x0 ]
adox r13, r14
adcx r12, r8
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x140 ], r12
mov [ rsp + 0x148 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r12
mov [ rsp + 0x158 ], r15
mulx r15, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], r10
mulx r10, r14, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x170 ], rdi
mov rdi, -0x2 
inc rdi
adox r9, r13
adox r8, rbp
mov rbp, [ rsp + 0x98 ]
seto r13b
inc rdi
adox rbp, [ rsp + 0x118 ]
mov dil, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], rbp
mov [ rsp + 0x180 ], r8
mulx r8, rbp, rdx
mov rdx, [ rsp + 0x78 ]
adox rdx, [ rsp + 0x70 ]
mov [ rsp + 0x188 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x190 ], r9
mov byte [ rsp + 0x198 ], r13b
mulx r13, r9, r12
mov rdx, [ rsp + 0x60 ]
adcx rdx, [ rsp + 0x68 ]
adox r14, [ rsp + 0x58 ]
mov [ rsp + 0x1a0 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1a8 ], r13
mov [ rsp + 0x1b0 ], r9
mulx r9, r13, [ rsi + 0x20 ]
adox r13, r10
mov rdx, [ rsp + 0x50 ]
adcx rdx, [ rsp + 0x48 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b8 ], r13
mov [ rsp + 0x1c0 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1c8 ], r10
mov [ rsp + 0x1d0 ], r14
mulx r14, r10, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x88 ]
mov [ rsp + 0x1d8 ], r13
setc r13b
clc
adcx rdx, [ rsp + 0x40 ]
adox rbp, r9
mov r9, [ rsp + 0x110 ]
mov [ rsp + 0x1e0 ], rbp
setc bpl
clc
mov [ rsp + 0x1e8 ], rdx
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r9, [ rsp + 0x28 ]
adox r8, [ rsp - 0x8 ]
seto r11b
inc rdx
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox rbx, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1f0 ], r8
mulx r8, rbp, [ rsi + 0x20 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1f8 ], rbx
mov [ rsp + 0x200 ], r9
mulx r9, rbx, r12
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x208 ], r13b
mov byte [ rsp + 0x210 ], r11b
mulx r11, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x218 ], r9
mov [ rsp + 0x220 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
adcx r13, [ rsp + 0xf8 ]
adox r10, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x228 ], r10
mulx r10, rcx, [ rsi + 0x28 ]
adox r14, [ rsp - 0x18 ]
setc dl
clc
adcx rax, r15
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x230 ], r14
mov [ rsp + 0x238 ], r13
mulx r13, r14, r15
mov r15, [ rsp + 0x170 ]
adcx r15, [ rsp + 0xf0 ]
mov [ rsp + 0x240 ], r15
seto r15b
mov [ rsp + 0x248 ], rax
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx r12, r12b
adox r12, rax
adox r11, [ rsp + 0x18 ]
mov r12, [ rsp + 0x38 ]
setc al
clc
mov [ rsp + 0x250 ], r11
mov r11, -0x1 
movzx rdi, dil
adcx rdi, r11
adcx r12, [ rsp + 0x168 ]
adox r9, [ rsp + 0x10 ]
mov rdi, 0x0 
adox rbx, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x258 ], rbx
mulx rbx, r11, rdi
adcx rcx, [ rsp + 0x30 ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x260 ], r9
mov [ rsp + 0x268 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
movzx rdx, byte [ rsp + 0x198 ]
mov [ rsp + 0x270 ], rcx
mov rcx, 0x0 
dec rcx
adox rdx, rcx
adox rbp, [ rsp + 0x160 ]
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x278 ], rbp
mulx rbp, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x280 ], r10
mov [ rsp + 0x288 ], r12
mulx r12, r10, [ rsi + 0x18 ]
adox r8, [ rsp + 0x1d8 ]
mov rdx, r11
mov [ rsp + 0x290 ], r8
seto r8b
mov [ rsp + 0x298 ], r13
mov r13, -0x2 
inc r13
adox rdx, rbx
mov r13, [ rsp + 0x1d0 ]
mov [ rsp + 0x2a0 ], rdx
seto dl
mov [ rsp + 0x2a8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r8, r8b
adox r8, r14
adox r13, [ rsp + 0xe8 ]
mov r8, [ rsp + 0xc0 ]
adox r8, [ rsp + 0xd0 ]
mov r14, [ rsp - 0x30 ]
mov [ rsp + 0x2b0 ], r8
setc r8b
clc
mov [ rsp + 0x2b8 ], r13
mov r13, -0x1 
movzx r15, r15b
adcx r15, r13
adcx r14, [ rsp + 0xa8 ]
seto r15b
inc r13
mov r13, -0x1 
movzx rax, al
adox rax, r13
adox r10, [ rsp + 0xe0 ]
mov rax, [ rsp + 0xa0 ]
adcx rax, [ rsp + 0x8 ]
adox r12, [ rsp + 0x108 ]
movzx r13, r15b
mov [ rsp + 0x2c0 ], rax
mov rax, [ rsp + 0xb8 ]
lea r13, [ r13 + rax ]
adox rcx, [ rsp + 0x100 ]
adox r9, rbp
mov rax, r11
setc bpl
clc
adcx rax, rdi
mov rax, rbx
seto r15b
mov [ rsp + 0x2c8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox rax, r11
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r14, r11, rdi
movzx rdi, bpl
mov rdx, [ rsp + 0x0 ]
lea rdi, [ rdi + rdx ]
adox r11, rbx
adox r14, [ rsp + 0x220 ]
mov rdx, [ rsp + 0x218 ]
adox rdx, [ rsp + 0x2a8 ]
mov rbx, [ rsp + 0x298 ]
adox rbx, [ rsp + 0x1b0 ]
movzx rbp, byte [ rsp + 0x210 ]
mov [ rsp + 0x2d0 ], rdi
mov rdi, [ rsp - 0x38 ]
lea rbp, [ rbp + rdi ]
mov rdi, [ rsp + 0x2a0 ]
adcx rdi, [ rsp + 0x248 ]
mov [ rsp + 0x2d8 ], rbp
seto bpl
mov [ rsp + 0x2e0 ], r13
mov r13, -0x2 
inc r13
adox rdi, [ rsp + 0x90 ]
mov r13, 0xffffffffffffffff 
xchg rdx, rdi
mov byte [ rsp + 0x2e8 ], r8b
mov byte [ rsp + 0x2f0 ], r15b
mulx r15, r8, r13
movzx r13, bpl
mov [ rsp + 0x2f8 ], rbx
mov rbx, [ rsp + 0x1a8 ]
lea r13, [ r13 + rbx ]
mov rbx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x300 ], r13
mulx r13, rbp, rbx
mov rbx, 0x2341f27177344 
mov [ rsp + 0x308 ], r13
mov [ rsp + 0x310 ], rbp
mulx rbp, r13, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x318 ], rbp
mov [ rsp + 0x320 ], r13
mulx r13, rbp, rbx
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0x328 ], r13
mov [ rsp + 0x330 ], rbp
mulx rbp, r13, rbx
adcx rax, [ rsp + 0x240 ]
mov rbx, r8
mov [ rsp + 0x338 ], rbp
seto bpl
mov [ rsp + 0x340 ], r13
mov r13, -0x2 
inc r13
adox rbx, rdx
seto bl
inc r13
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox rax, [ rsp + 0xb0 ]
adcx r11, r10
adox r11, [ rsp + 0x158 ]
mov r10, r8
seto bpl
mov rdx, -0x3 
inc rdx
adox r10, r15
adcx r14, r12
setc r12b
clc
mov r13, -0x1 
movzx rbx, bl
adcx rbx, r13
adcx rax, r10
setc bl
clc
movzx r12, r12b
adcx r12, r13
adcx rcx, rdi
setc dil
clc
adcx rax, [ rsp + 0xc8 ]
adox r8, r15
seto r10b
inc r13
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox r11, r8
adcx r11, [ rsp + 0x130 ]
setc bl
clc
movzx rbp, bpl
adcx rbp, r12
adcx r14, [ rsp + 0x148 ]
adcx rcx, [ rsp + 0x288 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r8, rbp, rax
mov r12, rbp
setc dl
clc
adcx r12, r8
mov [ rsp + 0x348 ], rcx
mov rcx, rbp
mov byte [ rsp + 0x350 ], bl
seto bl
mov [ rsp + 0x358 ], r14
mov r14, -0x3 
inc r14
adox rcx, rax
adox r12, r11
setc cl
clc
adcx r12, [ rsp - 0x40 ]
mov r11, r8
seto r13b
mov r14, 0x0 
dec r14
movzx rcx, cl
adox rcx, r14
adox r11, rbp
setc bpl
clc
movzx rdi, dil
adcx rdi, r14
adcx r9, [ rsp + 0x2f8 ]
seto dil
inc r14
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox r9, [ rsp + 0x268 ]
movzx rdx, byte [ rsp + 0x2f0 ]
mov r14, [ rsp + 0x270 ]
lea rdx, [ rdx + r14 ]
mov r14, 0x2341f27177344 
xchg rdx, rax
mov byte [ rsp + 0x360 ], bpl
mulx rbp, rcx, r14
adcx rax, [ rsp + 0x300 ]
setc r14b
clc
mov [ rsp + 0x368 ], rbp
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx r15, [ rsp + 0x310 ]
mov r10, [ rsp + 0x340 ]
adcx r10, [ rsp + 0x308 ]
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x370 ], r9
mov [ rsp + 0x378 ], r10
mulx r10, r9, rbp
setc bpl
clc
mov [ rsp + 0x380 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx r8, r9
adox rax, [ rsp + 0x280 ]
mov rdi, 0x6cfc5fd681c52056 
mulx rcx, r9, rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r12
mov [ rsp + 0x388 ], r8
mov [ rsp + 0x390 ], rax
mulx rax, r8, rdi
mov rdi, 0x6cfc5fd681c52056 
mov [ rsp + 0x398 ], rax
mov [ rsp + 0x3a0 ], rcx
mulx rcx, rax, rdi
mov rdi, 0x7bc65c783158aea3 
xchg rdx, r12
mov [ rsp + 0x3a8 ], rcx
mov [ rsp + 0x3b0 ], rax
mulx rax, rcx, rdi
adcx rcx, r10
adcx r9, rax
movzx rdx, byte [ rsp + 0x2e8 ]
mov r10, [ rsp - 0x48 ]
lea rdx, [ rdx + r10 ]
movzx r10, r14b
adox r10, rdx
mov r14, 0xffffffffffffffff 
mov rdx, r12
mulx rax, r12, r14
mov r14, r12
seto dil
mov [ rsp + 0x3b8 ], r9
mov r9, -0x2 
inc r9
adox r14, rax
mov r9, r12
adox r9, rax
adox r8, rax
seto al
mov [ rsp + 0x3c0 ], r8
mov r8, 0x0 
dec r8
movzx rbx, bl
adox rbx, r8
adox r15, [ rsp + 0x358 ]
mov rbx, [ rsp + 0x338 ]
seto r8b
mov byte [ rsp + 0x3c8 ], al
mov rax, 0x0 
dec rax
movzx rbp, bpl
adox rbp, rax
adox rbx, [ rsp + 0x330 ]
setc bpl
movzx rax, byte [ rsp + 0x350 ]
clc
mov [ rsp + 0x3d0 ], r9
mov r9, -0x1 
adcx rax, r9
adcx r15, [ rsp + 0x128 ]
setc al
clc
movzx r13, r13b
adcx r13, r9
adcx r15, r11
mov r13, [ rsp + 0x328 ]
adox r13, [ rsp + 0x320 ]
mov r11, [ rsp + 0x3a0 ]
setc r9b
clc
mov [ rsp + 0x3d8 ], rcx
mov rcx, -0x1 
movzx rbp, bpl
adcx rbp, rcx
adcx r11, [ rsp + 0x380 ]
mov rbp, [ rsp + 0x348 ]
seto cl
mov [ rsp + 0x3e0 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox rbp, [ rsp + 0x378 ]
adox rbx, [ rsp + 0x370 ]
movzx r8, byte [ rsp + 0x208 ]
mov r11, [ rsp - 0x10 ]
lea r8, [ r8 + r11 ]
seto r11b
mov byte [ rsp + 0x3e8 ], r9b
movzx r9, byte [ rsp + 0x360 ]
mov [ rsp + 0x3f0 ], r8
mov r8, 0x0 
dec r8
adox r9, r8
adox r15, [ rsp + 0xd8 ]
movzx r9, cl
mov r8, [ rsp + 0x318 ]
lea r9, [ r9 + r8 ]
setc r8b
clc
adcx r12, rdx
movzx r12, r8b
mov rcx, [ rsp + 0x368 ]
lea r12, [ r12 + rcx ]
seto cl
mov r8, 0x0 
dec r8
movzx rax, al
adox rax, r8
adox rbp, [ rsp + 0x120 ]
adcx r14, r15
setc al
clc
movzx r11, r11b
adcx r11, r8
adcx r13, [ rsp + 0x390 ]
adox rbx, [ rsp + 0x140 ]
adcx r9, r10
setc r10b
clc
adcx r14, [ rsp + 0x150 ]
mov r11, 0xffffffffffffffff 
xchg rdx, r14
mulx r8, r15, r11
mov r11, r15
mov [ rsp + 0x3f8 ], r12
setc r12b
clc
adcx r11, r8
mov [ rsp + 0x400 ], r11
mov r11, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x408 ], r12b
mov byte [ rsp + 0x410 ], al
mulx rax, r12, r11
mov r11, 0x6cfc5fd681c52056 
mov [ rsp + 0x418 ], rax
mov [ rsp + 0x420 ], r12
mulx r12, rax, r11
mov r11, r15
adcx r11, r8
mov [ rsp + 0x428 ], r12
mov r12, 0x2341f27177344 
mov [ rsp + 0x430 ], r11
mov [ rsp + 0x438 ], rax
mulx rax, r11, r12
adox r13, [ rsp + 0x1c0 ]
movzx r12, r10b
movzx rdi, dil
lea r12, [ r12 + rdi ]
adox r9, [ rsp + 0x1c8 ]
adox r12, [ rsp + 0x3f0 ]
setc dil
movzx r10, byte [ rsp + 0x3e8 ]
clc
mov [ rsp + 0x440 ], rax
mov rax, -0x1 
adcx r10, rax
adcx rbp, [ rsp + 0x388 ]
adcx rbx, [ rsp + 0x3d8 ]
seto r10b
inc rax
mov rax, -0x1 
movzx rcx, cl
adox rcx, rax
adox rbp, [ rsp + 0x138 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x448 ], r11
mulx r11, rax, rcx
seto cl
mov byte [ rsp + 0x450 ], r10b
movzx r10, byte [ rsp + 0x410 ]
mov byte [ rsp + 0x458 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r10, rdi
adox rbp, [ rsp + 0x3d0 ]
seto r10b
movzx rdi, byte [ rsp + 0x3c8 ]
mov [ rsp + 0x460 ], r12
mov r12, 0x0 
dec r12
adox rdi, r12
adox rax, [ rsp + 0x398 ]
setc dil
movzx r12, byte [ rsp + 0x408 ]
clc
mov [ rsp + 0x468 ], rax
mov rax, -0x1 
adcx r12, rax
adcx rbp, [ rsp + 0x190 ]
mov r12, 0x2341f27177344 
mov byte [ rsp + 0x470 ], r10b
mulx r10, rax, r12
adox r11, [ rsp + 0x3b0 ]
adox rax, [ rsp + 0x3a8 ]
setc dl
clc
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx rbx, [ rsp + 0x200 ]
seto cl
inc r12
mov r12, -0x1 
movzx rdi, dil
adox rdi, r12
adox r13, [ rsp + 0x3b8 ]
adox r9, [ rsp + 0x3e0 ]
movzx rdi, cl
lea rdi, [ rdi + r10 ]
mov r10, [ rsp + 0x3f8 ]
adox r10, [ rsp + 0x460 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r14
mov [ rsp + 0x478 ], rdi
mulx rdi, r12, rcx
seto cl
mov [ rsp + 0x480 ], rax
movzx rax, byte [ rsp + 0x458 ]
mov [ rsp + 0x488 ], r11
mov r11, 0x0 
dec r11
adox rax, r11
adox r8, [ rsp + 0x420 ]
setc al
clc
adcx r15, rdx
adcx rbp, [ rsp + 0x400 ]
setc r15b
clc
movzx rax, al
adcx rax, r11
adcx r13, [ rsp + 0x238 ]
adcx r9, [ rsp + 0x250 ]
setc dl
movzx rax, byte [ rsp + 0x470 ]
clc
adcx rax, r11
adcx rbx, [ rsp + 0x3c0 ]
adox r12, [ rsp + 0x418 ]
seto al
inc r11
mov r11, -0x1 
movzx r14, r14b
adox r14, r11
adox rbx, [ rsp + 0x180 ]
seto r14b
inc r11
mov r11, -0x1 
movzx rax, al
adox rax, r11
adox rdi, [ rsp + 0x438 ]
seto al
inc r11
mov r11, -0x1 
movzx r15, r15b
adox r15, r11
adox rbx, [ rsp + 0x430 ]
seto r15b
inc r11
mov r11, -0x1 
movzx rdx, dl
adox rdx, r11
adox r10, [ rsp + 0x260 ]
adcx r13, [ rsp + 0x468 ]
seto dl
inc r11
adox rbp, [ rsp - 0x20 ]
adcx r9, [ rsp + 0x488 ]
mov r11, 0x7bc65c783158aea3 
xchg rdx, rbp
mov [ rsp + 0x490 ], rdi
mov byte [ rsp + 0x498 ], al
mulx rax, rdi, r11
adox rbx, [ rsp + 0x178 ]
mov r11, 0x2341f27177344 
mov [ rsp + 0x4a0 ], rax
mov [ rsp + 0x4a8 ], rdi
mulx rdi, rax, r11
setc r11b
clc
mov [ rsp + 0x4b0 ], rdi
mov rdi, -0x1 
movzx r14, r14b
adcx r14, rdi
adcx r13, [ rsp + 0x278 ]
movzx r14, cl
movzx rdi, byte [ rsp + 0x450 ]
lea r14, [ r14 + rdi ]
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x4b8 ], rax
mulx rax, rcx, rdi
adcx r9, [ rsp + 0x290 ]
mov rdi, rcx
mov [ rsp + 0x4c0 ], rbx
seto bl
mov [ rsp + 0x4c8 ], rax
mov rax, -0x2 
inc rax
adox rdi, rdx
setc dil
clc
movzx r11, r11b
adcx r11, rax
adcx r10, [ rsp + 0x480 ]
seto r11b
inc rax
mov rax, -0x1 
movzx rbp, bpl
adox rbp, rax
adox r14, [ rsp + 0x258 ]
setc bpl
clc
movzx r15, r15b
adcx r15, rax
adcx r13, r8
mov r8, 0xfdc1767ae2ffffff 
mulx rax, r15, r8
adcx r12, r9
mov r9, rcx
setc r8b
clc
adcx r9, [ rsp + 0x4c8 ]
adcx rcx, [ rsp + 0x4c8 ]
adcx r15, [ rsp + 0x4c8 ]
mov [ rsp + 0x4d0 ], r15
seto r15b
mov [ rsp + 0x4d8 ], rcx
mov rcx, 0x0 
dec rcx
movzx rbp, bpl
adox rbp, rcx
adox r14, [ rsp + 0x478 ]
movzx rbp, r15b
mov rcx, 0x0 
adox rbp, rcx
dec rcx
movzx r11, r11b
adox r11, rcx
adox r9, [ rsp + 0x4c0 ]
seto r11b
inc rcx
adox r9, [ rsp + 0x80 ]
adcx rax, [ rsp + 0x4a8 ]
mov r15, 0x6cfc5fd681c52056 
mov [ rsp + 0x4e0 ], rax
mulx rax, rcx, r15
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x4e8 ], r11b
mulx r11, r15, r9
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4f0 ], r11
mov [ rsp + 0x4f8 ], r12
mulx r12, r11, r9
adcx rcx, [ rsp + 0x4a0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x500 ], rcx
mov [ rsp + 0x508 ], r12
mulx r12, rcx, r9
mov rdx, [ rsp + 0x448 ]
mov [ rsp + 0x510 ], r11
seto r11b
mov [ rsp + 0x518 ], r13
movzx r13, byte [ rsp + 0x498 ]
mov byte [ rsp + 0x520 ], bl
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r13, rbx
adox rdx, [ rsp + 0x428 ]
mov r13, rcx
setc bl
clc
adcx r13, r9
setc r13b
clc
mov byte [ rsp + 0x528 ], r11b
mov r11, -0x1 
movzx rdi, dil
adcx rdi, r11
adcx r10, [ rsp + 0x2b8 ]
setc dil
clc
movzx r8, r8b
adcx r8, r11
adcx r10, [ rsp + 0x490 ]
mov r8, rcx
setc r11b
clc
adcx r8, r12
adcx rcx, r12
mov [ rsp + 0x530 ], rcx
mov rcx, [ rsp + 0x440 ]
mov [ rsp + 0x538 ], r8
mov r8, 0x0 
adox rcx, r8
adcx r15, r12
dec r8
movzx rbx, bl
adox rbx, r8
adox rax, [ rsp + 0x4b8 ]
setc bl
clc
movzx rdi, dil
adcx rdi, r8
adcx r14, [ rsp + 0x2b0 ]
adcx rbp, [ rsp + 0x2e0 ]
seto r12b
inc r8
mov rdi, -0x1 
movzx r11, r11b
adox r11, rdi
adox r14, rdx
movzx rdx, r12b
mov r11, [ rsp + 0x4b0 ]
lea rdx, [ rdx + r11 ]
adox rcx, rbp
mov r11, [ rsp + 0x518 ]
setc r12b
movzx rbp, byte [ rsp + 0x520 ]
clc
adcx rbp, rdi
adcx r11, [ rsp + 0x188 ]
mov rbp, 0x7bc65c783158aea3 
xchg rdx, r9
mulx rdi, r8, rbp
mov rbp, 0x2341f27177344 
mov [ rsp + 0x540 ], r9
mov [ rsp + 0x548 ], r15
mulx r15, r9, rbp
mov rdx, [ rsp + 0x4f8 ]
adcx rdx, [ rsp + 0x1a0 ]
setc bpl
clc
mov [ rsp + 0x550 ], rax
mov rax, -0x1 
movzx rbx, bl
adcx rbx, rax
adcx r8, [ rsp + 0x4f0 ]
adcx rdi, [ rsp + 0x510 ]
adcx r9, [ rsp + 0x508 ]
seto bl
movzx rax, byte [ rsp + 0x4e8 ]
mov [ rsp + 0x558 ], r9
mov r9, 0x0 
dec r9
adox rax, r9
adox r11, [ rsp + 0x4d8 ]
setc al
clc
movzx rbp, bpl
adcx rbp, r9
adcx r10, [ rsp + 0x1b8 ]
movzx rbp, al
lea rbp, [ rbp + r15 ]
adox rdx, [ rsp + 0x4d0 ]
seto r15b
movzx rax, byte [ rsp + 0x528 ]
inc r9
mov r9, -0x1 
adox rax, r9
adox r11, [ rsp + 0x1e8 ]
setc al
clc
movzx r15, r15b
adcx r15, r9
adcx r10, [ rsp + 0x4e0 ]
seto r15b
inc r9
mov r9, -0x1 
movzx rax, al
adox rax, r9
adox r14, [ rsp + 0x1e0 ]
adcx r14, [ rsp + 0x500 ]
setc al
clc
movzx r15, r15b
adcx r15, r9
adcx rdx, [ rsp + 0x1f8 ]
adox rcx, [ rsp + 0x1f0 ]
setc r15b
clc
movzx r13, r13b
adcx r13, r9
adcx r11, [ rsp + 0x538 ]
adcx rdx, [ rsp + 0x530 ]
setc r13b
seto r9b
mov [ rsp + 0x560 ], rbp
mov rbp, r11
mov [ rsp + 0x568 ], rdi
mov rdi, 0xffffffffffffffff 
sub rbp, rdi
mov [ rsp + 0x570 ], rbp
mov rbp, rdx
sbb rbp, rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r15, r15b
adox r15, rdi
adox r10, [ rsp + 0x228 ]
adox r14, [ rsp + 0x230 ]
movzx r15, bl
movzx r12, r12b
lea r15, [ r15 + r12 ]
seto r12b
inc rdi
mov rbx, -0x1 
movzx r9, r9b
adox r9, rbx
adox r15, [ rsp + 0x2d8 ]
setc r9b
clc
movzx rax, al
adcx rax, rbx
adcx rcx, [ rsp + 0x550 ]
setc al
clc
movzx r12, r12b
adcx r12, rbx
adcx rcx, [ rsp + 0x2c8 ]
setc r12b
clc
movzx r13, r13b
adcx r13, rbx
adcx r10, [ rsp + 0x548 ]
adcx r8, r14
adcx rcx, [ rsp + 0x568 ]
seto r13b
dec rdi
movzx rax, al
adox rax, rdi
adox r15, [ rsp + 0x540 ]
setc bl
clc
movzx r12, r12b
adcx r12, rdi
adcx r15, [ rsp + 0x2c0 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, rdi
adcx r15, [ rsp + 0x558 ]
movzx rax, r13b
mov r12, 0x0 
adox rax, r12
setc r13b
movzx rbx, r9b
add rbx, -0x1
mov r9, r10
mov rbx, 0xffffffffffffffff 
sbb r9, rbx
inc rdi
mov r12, -0x1 
movzx r14, r14b
adox r14, r12
adox rax, [ rsp + 0x2d0 ]
seto r14b
mov rdi, r8
mov r12, 0xfdc1767ae2ffffff 
sbb rdi, r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox rax, [ rsp + 0x560 ]
movzx r13, r14b
mov r12, 0x0 
adox r13, r12
mov r14, rcx
mov r12, 0x7bc65c783158aea3 
sbb r14, r12
mov rbx, r15
mov r12, 0x6cfc5fd681c52056 
sbb rbx, r12
mov r12, rax
mov [ rsp + 0x578 ], r14
mov r14, 0x2341f27177344 
sbb r12, r14
sbb r13, 0x00000000
cmovc rdi, r8
cmovc rbx, r15
cmovc r9, r10
cmovc r12, rax
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x28 ], rbx
mov [ r13 + 0x30 ], r12
cmovc rbp, rdx
mov [ r13 + 0x8 ], rbp
mov rdx, [ rsp + 0x570 ]
cmovc rdx, r11
mov [ r13 + 0x18 ], rdi
mov r11, [ rsp + 0x578 ]
cmovc r11, rcx
mov [ r13 + 0x20 ], r11
mov [ r13 + 0x0 ], rdx
mov [ r13 + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1536
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4146
; seed 0756003118395547 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 54958 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=47, initial num_batches=31): 972 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01768623312347611
; number reverted permutation / tried permutation: 289 / 510 =56.667%
; number reverted decision / tried decision: 243 / 489 =49.693%
; validated in 180.363s
