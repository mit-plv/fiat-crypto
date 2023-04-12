SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1656
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rdi
mulx rdi, r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rdi
mulx rdi, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r12
mulx r12, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r12
mov [ rsp + 0x18 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x40 ], rcx
mov [ rsp + 0x48 ], r15
mulx r15, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], rcx
mov [ rsp + 0x68 ], r15
mulx r15, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r15
mov [ rsp + 0x78 ], r14
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], rdi
mov [ rsp + 0x88 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r9
mov [ rsp + 0x98 ], rdi
mulx rdi, r9, [ rsi + 0x30 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], r9
mulx r9, rdi, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], r9
mov [ rsp + 0xb8 ], rdi
mulx rdi, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r9
mov [ rsp + 0xc8 ], rcx
mulx rcx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r11
mov [ rsp + 0xd8 ], rbp
mulx rbp, r11, rdx
test al, al
adox r9, r10
adox r15, rcx
mov rdx, 0x2341f27177344 
mulx rcx, r10, rax
adox r12, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rcx
mulx rcx, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], rcx
mov [ rsp + 0xf0 ], r14
mulx r14, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], r10
mov [ rsp + 0x100 ], r14
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], r12
mov [ rsp + 0x110 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x118 ], rcx
mov [ rsp + 0x120 ], r15
mulx r15, rcx, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x128 ], r11
mov [ rsp + 0x130 ], rbp
mulx rbp, r11, [ rsi + 0x28 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x138 ], r11
mov [ rsp + 0x140 ], r12
mulx r12, r11, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], r12
mov [ rsp + 0x150 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, rcx
adcx rdx, rax
mov rdx, rcx
seto al
mov [ rsp + 0x158 ], r12
mov r12, -0x2 
inc r12
adox rdx, r15
seto r12b
mov byte [ rsp + 0x160 ], al
mov rax, -0x2 
inc rax
adox r10, rbp
adcx rdx, r9
setc r9b
clc
adcx r13, rdx
adox r8, r14
setc r14b
clc
adcx rbx, rdi
mov rdi, [ rsp + 0xd8 ]
adcx rdi, [ rsp + 0xd0 ]
mov rbp, r15
setc dl
clc
movzx r12, r12b
adcx r12, rax
adcx rbp, rcx
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mulx rax, r12, rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x168 ], rdi
mov [ rsp + 0x170 ], rbx
mulx rbx, rdi, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], rbx
mov [ rsp + 0x180 ], rdi
mulx rdi, rbx, [ rsi + 0x10 ]
adcx r11, r15
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x188 ], r8
mulx r8, r15, r13
mov rdx, [ rsp + 0x150 ]
mov [ rsp + 0x190 ], r10
setc r10b
clc
adcx rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x198 ], rdx
mov rdx, [ rsp + 0x140 ]
adox rdx, [ rsp + 0x88 ]
mov [ rsp + 0x1a0 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a8 ], r15
mov [ rsp + 0x1b0 ], rax
mulx rax, r15, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x130 ]
adox rdx, [ rsp + 0x80 ]
mov [ rsp + 0x1b8 ], rdx
mov rdx, [ rsp + 0x78 ]
mov [ rsp + 0x1c0 ], r8
setc r8b
clc
adcx rdx, [ rsp + 0x128 ]
adox rbx, [ rsp + 0x48 ]
mov [ rsp + 0x1c8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1d0 ], r12
mov [ rsp + 0x1d8 ], r11
mulx r11, r12, [ rsi + 0x18 ]
seto dl
mov byte [ rsp + 0x1e0 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox r12, [ rsp + 0x40 ]
mov rcx, [ rsp + 0x70 ]
seto r10b
mov [ rsp + 0x1e8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r8, r8b
adox r8, r12
adox rcx, [ rsp + 0x98 ]
seto r8b
inc r12
mov r12, -0x1 
movzx r9, r9b
adox r9, r12
adox rbp, [ rsp + 0x120 ]
seto r9b
inc r12
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox r11, [ rsp + 0x38 ]
mov r10, [ rsp + 0x90 ]
seto r12b
mov [ rsp + 0x1f0 ], rcx
mov rcx, 0x0 
dec rcx
movzx r8, r8b
adox r8, rcx
adox r10, [ rsp + 0x118 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, rcx
adcx rdi, r15
mov rdx, [ rsi + 0x8 ]
mulx rcx, r15, [ rsi + 0x18 ]
setc dl
clc
mov [ rsp + 0x1f8 ], r10
mov r10, -0x1 
movzx r14, r14b
adcx r14, r10
adcx rbp, rbx
mov r14b, dl
mov rdx, [ rsi + 0x20 ]
mulx r10, rbx, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x68 ]
mov [ rsp + 0x200 ], r11
seto r11b
mov [ rsp + 0x208 ], rdi
mov rdi, 0x0 
dec rdi
movzx r8, r8b
adox r8, rdi
adox rdx, [ rsp + 0x110 ]
mov r8, [ rsp + 0x60 ]
adox r8, [ rsp + 0x30 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x210 ], r10
mov [ rsp + 0x218 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], rcx
mov [ rsp + 0x228 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
movzx rdx, r14b
lea rdx, [ rdx + rax ]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x230 ], rcx
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x238 ], rax
mov [ rsp + 0x240 ], rcx
mulx rcx, rax, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x148 ]
mov [ rsp + 0x248 ], rax
setc al
mov [ rsp + 0x250 ], r14
movzx r14, byte [ rsp + 0x1e0 ]
clc
mov [ rsp + 0x258 ], rdi
mov rdi, -0x1 
adcx r14, rdi
adcx rdx, [ rsp + 0xb8 ]
setc r14b
clc
adcx r15, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x260 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x268 ], al
mov [ rsp + 0x270 ], r15
mulx r15, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x278 ], r14b
mov [ rsp + 0x280 ], r15
mulx r15, r14, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x288 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox rbx, [ rsp + 0x28 ]
mov r12b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x290 ], rbx
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x1d8 ]
mov byte [ rsp + 0x298 ], r12b
setc r12b
clc
mov [ rsp + 0x2a0 ], rbx
mov rbx, -0x1 
movzx r9, r9b
adcx r9, rbx
adcx rdx, [ rsp + 0x108 ]
seto r9b
movzx rbx, byte [ rsp + 0x160 ]
mov byte [ rsp + 0x2a8 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox rbx, r12
adox r10, [ rsp + 0x20 ]
adox rdi, rbp
adcx rcx, r10
mov rbx, rdx
mov rdx, [ rsi + 0x30 ]
mulx r10, rbp, [ rsi + 0x28 ]
seto dl
inc r12
adox rax, r8
setc r8b
clc
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r14, [ rsp + 0x100 ]
adox r15, [ rsp + 0x280 ]
mov r11, [ rsp + 0x2a0 ]
adox r11, [ rsp - 0x8 ]
mov r12, [ rsp + 0x1d0 ]
adcx r12, [ rsp + 0x288 ]
mov [ rsp + 0x2b0 ], r11
mov r11, [ rsp + 0x58 ]
adcx r11, [ rsp + 0x1b0 ]
mov [ rsp + 0x2b8 ], r11
mov r11, [ rsp - 0x18 ]
mov [ rsp + 0x2c0 ], r12
setc r12b
mov [ rsp + 0x2c8 ], r14
movzx r14, byte [ rsp + 0x278 ]
clc
mov [ rsp + 0x2d0 ], r15
mov r15, -0x1 
adcx r14, r15
adcx r11, [ rsp + 0xb0 ]
mov r14, [ rsp - 0x48 ]
adcx r14, [ rsp + 0xf8 ]
mov r15, [ rsp + 0x270 ]
mov [ rsp + 0x2d8 ], rax
seto al
mov byte [ rsp + 0x2e0 ], r9b
mov r9, 0x0 
dec r9
movzx rdx, dl
adox rdx, r9
adox r15, [ rsp + 0xa8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x2e8 ], r10
mulx r10, r9, [ rsi + 0x8 ]
mov rdx, [ rsp + 0xe0 ]
mov [ rsp + 0x2f0 ], r10
mov r10, 0x0 
adcx rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2f8 ], r9
mov [ rsp + 0x300 ], r14
mulx r14, r9, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x308 ], r10
mov [ rsp + 0x310 ], r14
mulx r14, r10, r13
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx rdi, r11
mov r8, r10
seto r11b
inc rdx
adox r8, r13
mov r8, r10
mov [ rsp + 0x318 ], r9
setc r9b
clc
adcx r8, r14
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x320 ], r11b
mov [ rsp + 0x328 ], rdi
mulx rdi, r11, r13
mov rdx, [ rsp + 0xf0 ]
mov [ rsp + 0x330 ], rdi
setc dil
clc
mov [ rsp + 0x338 ], r8
mov r8, -0x1 
movzx rax, al
adcx rax, r8
adcx rdx, [ rsp - 0x20 ]
adcx rbp, [ rsp + 0xe8 ]
setc al
movzx r8, byte [ rsp + 0x268 ]
clc
mov [ rsp + 0x340 ], rbp
mov rbp, -0x1 
adcx r8, rbp
adcx rbx, [ rsp + 0x258 ]
adcx rcx, [ rsp + 0x228 ]
mov r8, [ rsp + 0x220 ]
setc bpl
mov [ rsp + 0x348 ], rdx
movzx rdx, byte [ rsp + 0x2a8 ]
clc
mov byte [ rsp + 0x350 ], al
mov rax, -0x1 
adcx rdx, rax
adcx r8, [ rsp + 0x250 ]
movzx rdx, r12b
mov rax, [ rsp + 0x50 ]
lea rdx, [ rdx + rax ]
setc al
clc
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx r15, [ rsp + 0x300 ]
mov r9, r14
setc r12b
clc
mov [ rsp + 0x358 ], rdx
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx r9, r10
adcx r11, r14
mov r10, [ rsp - 0x10 ]
seto r14b
movzx rdi, byte [ rsp + 0x298 ]
inc rdx
mov rdx, -0x1 
adox rdi, rdx
adox r10, [ rsp + 0x8 ]
mov rdi, [ rsp + 0x0 ]
adox rdi, [ rsp + 0x2f8 ]
mov rdx, [ rsp + 0x218 ]
mov [ rsp + 0x360 ], r8
seto r8b
mov byte [ rsp + 0x368 ], r12b
mov r12, 0x0 
dec r12
movzx r14, r14b
adox r14, r12
adox rdx, [ rsp + 0x338 ]
adox r9, rbx
mov r14, [ rsp + 0x330 ]
adcx r14, [ rsp + 0x1a8 ]
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x370 ], r8b
mulx r8, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x378 ], r8
mov [ rsp + 0x380 ], r14
mulx r14, r8, [ rsi + 0x28 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x388 ], r14
mov [ rsp + 0x390 ], r8
mulx r8, r14, r13
mov r13, [ rsp + 0x240 ]
seto dl
mov [ rsp + 0x398 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
movzx rax, al
adox rax, r8
adox r13, [ rsp + 0x18 ]
adcx r14, [ rsp + 0x1a0 ]
adox r12, [ rsp + 0x10 ]
setc al
clc
movzx rdx, dl
adcx rdx, r8
adcx rcx, r11
setc r11b
clc
adcx rbx, [ rsp + 0x158 ]
adcx r9, [ rsp + 0x190 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x3a0 ], r12
mulx r12, r8, rbx
mov rdx, [ rsp - 0x28 ]
mov [ rsp + 0x3a8 ], r13
seto r13b
mov [ rsp + 0x3b0 ], r12
movzx r12, byte [ rsp + 0x350 ]
mov [ rsp + 0x3b8 ], r8
mov r8, 0x0 
dec r8
adox r12, r8
adox rdx, [ rsp + 0x2e8 ]
seto r12b
inc r8
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox r10, [ rsp + 0x328 ]
adcx rcx, [ rsp + 0x188 ]
adox rdi, r15
setc bpl
clc
movzx r11, r11b
adcx r11, r8
adcx r10, [ rsp + 0x380 ]
mov r15, 0xffffffffffffffff 
xchg rdx, rbx
mulx r8, r11, r15
mov r15, r11
mov [ rsp + 0x3c0 ], rbx
seto bl
mov [ rsp + 0x3c8 ], rcx
mov rcx, -0x2 
inc rcx
adox r15, r8
movzx rcx, byte [ rsp + 0x320 ]
mov [ rsp + 0x3d0 ], r10
mov r10, [ rsp + 0xa0 ]
lea rcx, [ rcx + r10 ]
movzx r10, r12b
mov byte [ rsp + 0x3d8 ], bpl
mov rbp, [ rsp - 0x30 ]
lea r10, [ r10 + rbp ]
mov rbp, [ rsp + 0x398 ]
setc r12b
clc
mov [ rsp + 0x3e0 ], r10
mov r10, -0x1 
movzx rax, al
adcx rax, r10
adcx rbp, [ rsp + 0x180 ]
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x3e8 ], rbp
mulx rbp, r10, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x2f0 ]
mov [ rsp + 0x3f0 ], r14
seto r14b
mov [ rsp + 0x3f8 ], rdi
movzx rdi, byte [ rsp + 0x370 ]
mov byte [ rsp + 0x400 ], r12b
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox rdi, r12
adox rdx, [ rsp + 0x318 ]
mov rdi, [ rsp + 0x310 ]
mov r12, 0x0 
adox rdi, r12
mov r12, [ rsp + 0x378 ]
mov [ rsp + 0x408 ], r15
mov r15, 0x0 
dec r15
movzx r13, r13b
adox r13, r15
adox r12, [ rsp + 0x390 ]
seto r13b
movzx r15, byte [ rsp + 0x368 ]
mov [ rsp + 0x410 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r15, r12
adox rcx, [ rsp + 0x308 ]
seto r15b
inc r12
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rcx, rdx
movzx rbx, r15b
adox rbx, rdi
setc dl
movzx rdi, byte [ rsp + 0x2e0 ]
clc
adcx rdi, r12
adcx r10, [ rsp + 0x210 ]
mov rdi, [ rsp + 0x388 ]
setc r15b
clc
movzx r13, r13b
adcx r13, r12
adcx rdi, [ rsp - 0x38 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x418 ], r10
mulx r10, r12, r13
mov r13, r8
mov [ rsp + 0x420 ], rdi
setc dil
clc
mov [ rsp + 0x428 ], r10
mov r10, -0x1 
movzx r14, r14b
adcx r14, r10
adcx r13, r11
movzx r14, r15b
lea r14, [ r14 + rbp ]
seto bpl
inc r10
adox r11, rdx
adox r9, [ rsp + 0x408 ]
adcx r12, r8
mov r11, 0x6cfc5fd681c52056 
mulx r15, r8, r11
mov r10, [ rsp + 0x3f8 ]
setc r11b
mov [ rsp + 0x430 ], r14
movzx r14, byte [ rsp + 0x400 ]
clc
mov byte [ rsp + 0x438 ], dil
mov rdi, -0x1 
adcx r14, rdi
adcx r10, [ rsp + 0x3f0 ]
movzx r14, al
mov rdi, [ rsp + 0x178 ]
lea r14, [ r14 + rdi ]
seto dil
mov rax, -0x2 
inc rax
adox r9, [ rsp + 0x248 ]
mov rax, 0x7bc65c783158aea3 
mov [ rsp + 0x440 ], r12
mov [ rsp + 0x448 ], r10
mulx r10, r12, rax
adcx rcx, [ rsp + 0x3e8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x450 ], rcx
mulx rcx, rax, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x458 ], rax
mov [ rsp + 0x460 ], rcx
mulx rcx, rax, r9
mov rdx, 0x2341f27177344 
mov [ rsp + 0x468 ], rcx
mov [ rsp + 0x470 ], rax
mulx rax, rcx, r9
adcx r14, rbx
seto bl
mov rdx, 0x0 
dec rdx
movzx r11, r11b
adox r11, rdx
adox r12, [ rsp + 0x428 ]
movzx r11, bpl
mov rdx, 0x0 
adcx r11, rdx
adox r8, r10
adox r15, [ rsp + 0x3b8 ]
mov rbp, [ rsp + 0x3b0 ]
adox rbp, rdx
mov r10, [ rsp + 0x1c0 ]
add byte [ rsp + 0x3d8 ], 0xFF
adcx r10, [ rsp + 0x3d0 ]
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox r13, [ rsp + 0x3c8 ]
seto dil
inc rdx
mov rdx, -0x1 
movzx rbx, bl
adox rbx, rdx
adox r13, [ rsp + 0x260 ]
mov rbx, [ rsp + 0x448 ]
adcx rbx, [ rsp + 0x1b8 ]
seto dl
mov [ rsp + 0x478 ], rax
mov rax, 0x0 
dec rax
movzx rdi, dil
adox rdi, rax
adox r10, [ rsp + 0x440 ]
adox r12, rbx
mov rdi, [ rsp + 0x458 ]
mov rbx, rdi
setc al
clc
adcx rbx, [ rsp + 0x460 ]
mov [ rsp + 0x480 ], r12
mov r12, rdi
mov [ rsp + 0x488 ], r10
seto r10b
mov byte [ rsp + 0x490 ], dl
mov rdx, -0x2 
inc rdx
adox r12, r9
adox rbx, r13
mov r12, 0x7bc65c783158aea3 
mov rdx, r12
mulx r13, r12, r9
adcx rdi, [ rsp + 0x460 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x498 ], rdi
mov [ rsp + 0x4a0 ], rbx
mulx rbx, rdi, r9
mov r9, [ rsp + 0x1c8 ]
seto dl
mov [ rsp + 0x4a8 ], rbp
mov rbp, 0x0 
dec rbp
movzx rax, al
adox rax, rbp
adox r9, [ rsp + 0x450 ]
mov rax, [ rsp + 0x470 ]
adcx rax, [ rsp + 0x460 ]
adcx r12, [ rsp + 0x468 ]
adcx rdi, r13
adcx rcx, rbx
adox r14, [ rsp + 0x208 ]
seto r13b
inc rbp
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox r9, r8
adox r15, r14
seto r8b
dec rbp
movzx r13, r13b
adox r13, rbp
adox r11, [ rsp + 0x238 ]
seto bl
inc rbp
mov r10, -0x1 
movzx r8, r8b
adox r8, r10
adox r11, [ rsp + 0x4a8 ]
movzx r13, bl
adox r13, rbp
mov r14, [ rsp + 0x360 ]
movzx r8, byte [ rsp + 0x490 ]
inc r10
mov rbp, -0x1 
adox r8, rbp
adox r14, [ rsp + 0x488 ]
mov r8, [ rsp + 0x4a0 ]
setc bl
clc
adcx r8, [ rsp + 0xc0 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov byte [ rsp + 0x4b0 ], bl
mulx rbx, rbp, r8
mov rdx, 0x2341f27177344 
mov [ rsp + 0x4b8 ], rbx
mov [ rsp + 0x4c0 ], r13
mulx r13, rbx, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x4c8 ], r13
mov [ rsp + 0x4d0 ], rbx
mulx rbx, r13, r8
mov rdx, [ rsp + 0x480 ]
adox rdx, [ rsp + 0x3a8 ]
mov [ rsp + 0x4d8 ], rcx
mov rcx, r13
mov [ rsp + 0x4e0 ], r11
seto r11b
mov [ rsp + 0x4e8 ], rdi
mov rdi, -0x2 
inc rdi
adox rcx, rbx
setc dil
clc
mov [ rsp + 0x4f0 ], r12
mov r12, -0x1 
movzx r10, r10b
adcx r10, r12
adcx r14, [ rsp + 0x498 ]
adcx rax, rdx
mov r10, r13
adox r10, rbx
setc dl
clc
movzx rdi, dil
adcx rdi, r12
adcx r14, [ rsp + 0x170 ]
adox rbp, rbx
seto dil
inc r12
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r9, [ rsp + 0x3a0 ]
adox r15, [ rsp + 0x410 ]
seto r11b
mov rbx, -0x3 
inc rbx
adox r13, r8
adox rcx, r14
seto r13b
dec r12
movzx rdx, dl
adox rdx, r12
adox r9, [ rsp + 0x4f0 ]
adcx rax, [ rsp + 0x168 ]
movzx rdx, byte [ rsp + 0x438 ]
mov r14, [ rsp - 0x40 ]
lea rdx, [ rdx + r14 ]
adox r15, [ rsp + 0x4e8 ]
mov r14, [ rsp + 0x4e0 ]
setc r12b
clc
mov rbx, -0x1 
movzx r11, r11b
adcx r11, rbx
adcx r14, [ rsp + 0x420 ]
adox r14, [ rsp + 0x4d8 ]
adcx rdx, [ rsp + 0x4c0 ]
movzx r11, byte [ rsp + 0x4b0 ]
mov rbx, [ rsp + 0x478 ]
lea r11, [ r11 + rbx ]
adox r11, rdx
seto bl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox rax, r10
movzx r10, bl
mov r13, 0x0 
adcx r10, r13
clc
movzx r12, r12b
adcx r12, rdx
adcx r9, [ rsp + 0x1e8 ]
setc r12b
clc
adcx rcx, [ rsp + 0x138 ]
mov rbx, 0xfdc1767ae2ffffff 
mov rdx, rbx
mulx r13, rbx, rcx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4f8 ], r13
mov [ rsp + 0x500 ], rbx
mulx rbx, r13, rcx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x508 ], rbx
mov [ rsp + 0x510 ], r13
mulx r13, rbx, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x518 ], r13
mov [ rsp + 0x520 ], rbx
mulx rbx, r13, r8
setc dl
clc
mov [ rsp + 0x528 ], rbx
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r15, [ rsp + 0x200 ]
adox rbp, r9
seto r9b
inc rbx
mov r12, -0x1 
movzx rdi, dil
adox rdi, r12
adox r13, [ rsp + 0x4b8 ]
setc dil
clc
movzx r9, r9b
adcx r9, r12
adcx r15, r13
mov r9, 0x7bc65c783158aea3 
xchg rdx, rcx
mulx rbx, r13, r9
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x530 ], rbx
mulx rbx, r9, r8
mov r8, 0xffffffffffffffff 
mov rdx, r12
mov [ rsp + 0x538 ], r13
mulx r13, r12, r8
setc r8b
clc
mov [ rsp + 0x540 ], r15
mov r15, -0x1 
movzx rdi, dil
adcx rdi, r15
adcx r14, [ rsp + 0x290 ]
adcx r11, [ rsp + 0x418 ]
adcx r10, [ rsp + 0x430 ]
mov rdi, r12
setc r15b
clc
adcx rdi, r13
mov byte [ rsp + 0x548 ], r15b
setc r15b
clc
mov [ rsp + 0x550 ], r10
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx rax, [ rsp + 0x198 ]
adcx rbp, [ rsp + 0x1f0 ]
mov rcx, r12
setc r10b
clc
adcx rcx, rdx
adcx rdi, rax
adox r9, [ rsp + 0x528 ]
adox rbx, [ rsp + 0x4d0 ]
mov rcx, [ rsp + 0x1f8 ]
seto dl
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx r10, r10b
adox r10, rax
adox rcx, [ rsp + 0x540 ]
seto r10b
inc rax
adox rdi, [ rsp + 0x230 ]
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov byte [ rsp + 0x558 ], dil
mov byte [ rsp + 0x560 ], r10b
mulx r10, rdi, rax
mov rax, 0x2341f27177344 
mov [ rsp + 0x568 ], r10
mov [ rsp + 0x570 ], rcx
mulx rcx, r10, rax
mov rax, r13
mov [ rsp + 0x578 ], rcx
seto cl
mov [ rsp + 0x580 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r15, r15b
adox r15, r10
adox rax, r12
mov r12, 0xffffffffffffffff 
mulx r10, r15, r12
mov r12, r15
mov byte [ rsp + 0x588 ], cl
setc cl
clc
adcx r12, r10
adox r13, [ rsp + 0x500 ]
mov [ rsp + 0x590 ], r13
mov r13, [ rsp + 0x4f8 ]
adox r13, [ rsp + 0x538 ]
mov [ rsp + 0x598 ], r13
mov r13, [ rsp + 0x530 ]
adox r13, [ rsp + 0x510 ]
mov [ rsp + 0x5a0 ], r13
seto r13b
mov [ rsp + 0x5a8 ], r12
mov r12, 0x0 
dec r12
movzx rcx, cl
adox rcx, r12
adox rbp, rax
mov rcx, r15
adcx rcx, r10
seto al
inc r12
mov r12, -0x1 
movzx r8, r8b
adox r8, r12
adox r14, r9
adcx rdi, r10
adox rbx, r11
seto r8b
inc r12
adox r15, rdx
mov r15, [ rsp + 0x508 ]
setc r11b
clc
mov r9, -0x1 
movzx r13, r13b
adcx r13, r9
adcx r15, [ rsp + 0x520 ]
seto r10b
movzx r13, byte [ rsp + 0x588 ]
dec r12
adox r13, r12
adox rbp, [ rsp + 0x2d8 ]
setc r9b
clc
movzx r10, r10b
adcx r10, r12
adcx rbp, [ rsp + 0x5a8 ]
mov r13, [ rsp + 0x570 ]
setc r10b
clc
movzx rax, al
adcx rax, r12
adcx r13, [ rsp + 0x590 ]
adox r13, [ rsp + 0x2d0 ]
seto al
movzx r12, byte [ rsp + 0x560 ]
mov [ rsp + 0x5b0 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r12, r15
adox r14, [ rsp + 0x2c8 ]
adox rbx, [ rsp + 0x2c0 ]
adcx r14, [ rsp + 0x598 ]
setc r12b
clc
movzx rax, al
adcx rax, r15
adcx r14, [ rsp + 0x2b0 ]
seto al
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox rbx, [ rsp + 0x5a0 ]
mov r12, 0x7bc65c783158aea3 
mov byte [ rsp + 0x5b8 ], r9b
mulx r9, r15, r12
seto r12b
mov [ rsp + 0x5c0 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r11, r11b
adox r11, rbp
adox r15, [ rsp + 0x568 ]
movzx r11, byte [ rsp + 0x558 ]
mov rbp, [ rsp + 0x4c8 ]
lea r11, [ r11 + rbp ]
mov rbp, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x5c8 ], r12b
mov [ rsp + 0x5d0 ], r15
mulx r15, r12, rbp
setc dl
clc
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx r13, rcx
adcx rdi, r14
adox r12, r9
adox r15, [ rsp + 0x580 ]
setc cl
clc
movzx r8, r8b
adcx r8, rbp
adcx r11, [ rsp + 0x550 ]
mov r8, [ rsp + 0x578 ]
mov r10, 0x0 
adox r8, r10
movzx r14, byte [ rsp + 0x548 ]
adc r14, 0x0
add dl, 0xFF
adcx rbx, [ rsp + 0x348 ]
movzx rax, al
adox rax, rbp
adox r11, [ rsp + 0x2b8 ]
adox r14, [ rsp + 0x358 ]
setc al
seto dl
mov r9, [ rsp + 0x5c0 ]
mov rbp, 0xffffffffffffffff 
sub r9, rbp
dec r10
movzx rcx, cl
adox rcx, r10
adox rbx, [ rsp + 0x5d0 ]
seto cl
mov r10, r13
sbb r10, rbp
mov [ rsp + 0x5d8 ], r10
mov r10, rdi
sbb r10, rbp
movzx rbp, byte [ rsp + 0x5b8 ]
mov [ rsp + 0x5e0 ], r10
mov r10, [ rsp + 0x518 ]
lea rbp, [ rbp + r10 ]
mov r10, rbx
mov [ rsp + 0x5e8 ], r9
mov r9, 0xfdc1767ae2ffffff 
sbb r10, r9
movzx r9, byte [ rsp + 0x5c8 ]
mov [ rsp + 0x5f0 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r9, r10
adox r11, [ rsp + 0x5b0 ]
setc r9b
clc
movzx rax, al
adcx rax, r10
adcx r11, [ rsp + 0x340 ]
adox rbp, r14
adcx rbp, [ rsp + 0x3c0 ]
movzx rax, dl
mov r14, 0x0 
adox rax, r14
inc r10
mov r14, -0x1 
movzx rcx, cl
adox rcx, r14
adox r11, r12
adox r15, rbp
adcx rax, [ rsp + 0x3e0 ]
setc r12b
seto dl
movzx rcx, r9b
add rcx, -0x1
mov rcx, r11
mov r9, 0x7bc65c783158aea3 
sbb rcx, r9
mov rbp, r15
mov r10, 0x6cfc5fd681c52056 
sbb rbp, r10
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox rax, r8
seto r8b
mov rdx, rax
mov r14, 0x2341f27177344 
sbb rdx, r14
movzx r10, r8b
movzx r12, r12b
lea r10, [ r10 + r12 ]
sbb r10, 0x00000000
mov r10, [ rsp + 0x5f0 ]
cmovc r10, rbx
cmovc rbp, r15
cmovc rcx, r11
mov rbx, [ rsp + 0x5e8 ]
cmovc rbx, [ rsp + 0x5c0 ]
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x20 ], rcx
mov r15, [ rsp + 0x5e0 ]
cmovc r15, rdi
mov [ r11 + 0x28 ], rbp
mov [ r11 + 0x10 ], r15
cmovc rdx, rax
mov rdi, [ rsp + 0x5d8 ]
cmovc rdi, r13
mov [ r11 + 0x0 ], rbx
mov [ r11 + 0x8 ], rdi
mov [ r11 + 0x30 ], rdx
mov [ r11 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1656
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3218
; seed 3202706397630319 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 74373 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 1149 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.015449154935258762
; number reverted permutation / tried permutation: 250 / 496 =50.403%
; number reverted decision / tried decision: 224 / 503 =44.533%
; validated in 362.571s
