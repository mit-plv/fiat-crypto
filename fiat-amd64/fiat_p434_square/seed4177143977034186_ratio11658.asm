SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1728
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rdi
mulx rdi, r12, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], rbx
mulx rbx, rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], r13
mulx r13, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], r10
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], r8
mulx r8, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], r8
mov [ rsp + 0x38 ], r10
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r10
mov [ rsp + 0x48 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r8
mov [ rsp + 0x58 ], r10
mulx r10, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], r8
mulx r8, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], r8
mov [ rsp + 0x78 ], r10
mulx r10, r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x80 ], r10
mov [ rsp + 0x88 ], r8
mulx r8, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r10
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], r10
mov [ rsp + 0xa8 ], r8
mulx r8, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r10
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r13
mulx r13, r8, [ rsi + 0x8 ]
add rbx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r10, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r10
mulx r10, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], r10
mov [ rsp + 0xe8 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], rbx
mov [ rsp + 0x108 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], r10
mov [ rsp + 0x118 ], r13
mulx r13, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x120 ], r13
mov [ rsp + 0x128 ], r10
mulx r10, r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x130 ], r8
mov [ rsp + 0x138 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x140 ], rbx
mov rbx, -0x2 
inc rbx
adox r13, rdi
adcx r8, rbp
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mulx rbx, rdi, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x148 ], r8
mov r8, -0x2 
inc r8
adox rdi, r9
mov r9b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], rdi
mulx rdi, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], rdi
mov [ rsp + 0x170 ], r13
mulx r13, rdi, [ rsi + 0x30 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x178 ], r8
mov byte [ rsp + 0x180 ], bpl
mulx rbp, r8, r12
adox r14, rbx
adox rax, r15
setc r15b
clc
mov rbx, -0x1 
movzx r9, r9b
adcx r9, rbx
adcx r10, r11
adcx rcx, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x188 ], rax
mulx rax, rbx, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xc8 ]
mov [ rsp + 0x190 ], r14
seto r14b
mov [ rsp + 0x198 ], rbp
mov rbp, -0x2 
inc rbp
adox rdx, [ rsp + 0x130 ]
mov rbp, [ rsp + 0x128 ]
mov [ rsp + 0x1a0 ], rdx
setc dl
clc
mov [ rsp + 0x1a8 ], rcx
mov rcx, -0x1 
movzx r14, r14b
adcx r14, rcx
adcx rbp, [ rsp + 0x18 ]
mov r14, [ rsp + 0x118 ]
adox r14, [ rsp + 0x108 ]
adox rdi, [ rsp + 0xf8 ]
setc cl
clc
mov [ rsp + 0x1b0 ], rdi
mov rdi, -0x1 
movzx rdx, dl
adcx rdx, rdi
adcx rbx, [ rsp + 0x110 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1b8 ], r14
mulx r14, rdi, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c0 ], rbp
mov [ rsp + 0x1c8 ], rbx
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d0 ], r10
mov [ rsp + 0x1d8 ], r9
mulx r9, r10, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1e0 ], r11
mov [ rsp + 0x1e8 ], r8
mulx r8, r11, r12
adox r13, [ rsp + 0x8 ]
setc dl
clc
mov [ rsp + 0x1f0 ], r13
mov r13, -0x1 
movzx r15, r15b
adcx r15, r13
adcx r10, [ rsp + 0x140 ]
mov r15, [ rsp - 0x18 ]
adox r15, [ rsp + 0x0 ]
adcx r9, [ rsp + 0xa8 ]
mov r13, 0x6cfc5fd681c52056 
xchg rdx, r12
mov [ rsp + 0x1f8 ], r15
mov [ rsp + 0x200 ], r9
mulx r9, r15, r13
mov r13, [ rsp + 0x88 ]
mov [ rsp + 0x208 ], r10
setc r10b
clc
mov [ rsp + 0x210 ], r9
mov r9, -0x1 
movzx rcx, cl
adcx rcx, r9
adcx r13, [ rsp + 0x120 ]
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x218 ], r13
mulx r13, r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], rax
mov byte [ rsp + 0x228 ], r12b
mulx r12, rax, [ rsi + 0x20 ]
mov rdx, r9
mov [ rsp + 0x230 ], rax
setc al
clc
adcx rdx, r13
mov byte [ rsp + 0x238 ], al
mov rax, [ rsp - 0x8 ]
adox rax, [ rsp - 0x20 ]
mov [ rsp + 0x240 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x248 ], r15
mov [ rsp + 0x250 ], r8
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x258 ], r8
mov [ rsp + 0x260 ], r15
mulx r15, r8, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xf0 ]
mov [ rsp + 0x268 ], r15
seto r15b
mov [ rsp + 0x270 ], r8
movzx r8, byte [ rsp + 0x180 ]
mov [ rsp + 0x278 ], rax
mov rax, -0x1 
inc rax
mov rax, -0x1 
adox r8, rax
adox rdx, [ rsp + 0x48 ]
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x280 ], r15b
mulx r15, rax, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x288 ], r8
mov r8, 0x0 
dec r8
movzx r10, r10b
adox r10, r8
adox rax, [ rsp + 0xa0 ]
setc r10b
clc
adcx rbp, r12
mov r12, [ rsp + 0x40 ]
seto r8b
mov [ rsp + 0x290 ], rax
mov rax, 0x0 
dec rax
movzx rdx, dl
adox rdx, rax
adox r12, [ rsp - 0x28 ]
adcx rbx, [ rsp + 0x28 ]
mov rdx, r13
seto al
mov [ rsp + 0x298 ], rbx
mov rbx, 0x0 
dec rbx
movzx r10, r10b
adox r10, rbx
adox rdx, r9
adox rdi, r13
adox r11, r14
setc r14b
clc
movzx r8, r8b
adcx r8, rbx
adcx r15, [ rsp - 0x30 ]
setc r13b
clc
adcx r9, rcx
mov r9, [ rsp + 0x278 ]
adcx r9, [ rsp + 0xd8 ]
mov rcx, [ rsp + 0x250 ]
adox rcx, [ rsp + 0x248 ]
mov r10, [ rsp + 0x220 ]
seto r8b
movzx rbx, byte [ rsp + 0x228 ]
mov [ rsp + 0x2a0 ], r15
mov r15, 0x0 
dec r15
adox rbx, r15
adox r10, [ rsp + 0x260 ]
mov rbx, [ rsp + 0x258 ]
adox rbx, [ rsp + 0x178 ]
mov r15, [ rsp + 0x160 ]
mov [ rsp + 0x2a8 ], rbp
mov rbp, 0x0 
adox r15, rbp
adcx rdx, [ rsp + 0x288 ]
mov rbp, [ rsp + 0x98 ]
mov [ rsp + 0x2b0 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r14, r14b
adox r14, r15
adox rbp, [ rsp + 0x20 ]
adcx rdi, r12
mov r12, [ rsp + 0x210 ]
setc r14b
clc
movzx r8, r8b
adcx r8, r15
adcx r12, [ rsp + 0x1e8 ]
mov r8, [ rsp + 0x90 ]
adox r8, [ rsp + 0xb8 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2b8 ], r8
mov [ rsp + 0x2c0 ], rbp
mulx rbp, r8, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0x2c8 ], rbx
setc bl
clc
mov [ rsp + 0x2d0 ], r10
mov r10, -0x1 
movzx rax, al
adcx rax, r10
adcx rdx, [ rsp + 0x78 ]
mov rax, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x1e0 ]
seto r10b
mov byte [ rsp + 0x2d8 ], bl
mov rbx, -0x2 
inc rbx
adox r9, [ rsp + 0x100 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mov [ rsp + 0x2e0 ], r12
mov [ rsp + 0x2e8 ], rcx
mulx rcx, r12, r9
mov rdx, r12
mov [ rsp + 0x2f0 ], rax
setc al
clc
adcx rdx, rcx
mov [ rsp + 0x2f8 ], r11
mov r11, r12
mov [ rsp + 0x300 ], rbx
setc bl
clc
adcx r11, r9
mov r11, 0x6cfc5fd681c52056 
xchg rdx, r9
mov byte [ rsp + 0x308 ], r14b
mov byte [ rsp + 0x310 ], bl
mulx rbx, r14, r11
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x318 ], rbx
mov [ rsp + 0x320 ], r14
mulx r14, rbx, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x328 ], r14
mov [ rsp + 0x330 ], rbx
mulx rbx, r14, r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x338 ], rbx
mov [ rsp + 0x340 ], r14
mulx r14, rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x348 ], r14
mov [ rsp + 0x350 ], rbx
mulx rbx, r14, [ rsi + 0x28 ]
adox r15, [ rsp + 0x158 ]
movzx rdx, r13b
mov [ rsp + 0x358 ], rbx
mov rbx, [ rsp - 0x40 ]
lea rdx, [ rdx + rbx ]
adcx r9, r15
mov rbx, [ rsp + 0x1d8 ]
setc r13b
clc
mov r15, -0x1 
movzx rax, al
adcx rax, r15
adcx rbx, [ rsp + 0xe8 ]
movzx rax, byte [ rsp + 0x280 ]
mov r15, [ rsp - 0x10 ]
lea rax, [ rax + r15 ]
mov r15, [ rsp + 0xe0 ]
mov [ rsp + 0x360 ], rax
mov rax, 0x0 
adcx r15, rax
adox rdi, [ rsp + 0x1d0 ]
clc
adcx rbp, [ rsp + 0x58 ]
mov [ rsp + 0x368 ], rdx
setc dl
clc
adcx r8, r9
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov [ rsp + 0x370 ], r15
mulx r15, rax, r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x378 ], r15
mov [ rsp + 0x380 ], rax
mulx rax, r15, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x388 ], rax
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx r10, r10b
adox r10, rax
adox r14, [ rsp + 0xb0 ]
mov r10, [ rsp + 0x50 ]
seto al
mov [ rsp + 0x390 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r8, r8b
adox r8, r14
adox r10, [ rsp + 0x350 ]
mov r8, [ rsp + 0x348 ]
adox r8, [ rsp + 0x170 ]
mov r14, rcx
mov [ rsp + 0x398 ], r8
setc r8b
mov [ rsp + 0x3a0 ], r10
movzx r10, byte [ rsp + 0x310 ]
clc
mov byte [ rsp + 0x3a8 ], al
mov rax, -0x1 
adcx r10, rax
adcx r14, r12
mov r12, [ rsp + 0x168 ]
adox r12, [ rsp + 0x270 ]
adox r15, [ rsp + 0x268 ]
adcx rcx, [ rsp + 0x330 ]
mov r10, [ rsp + 0x340 ]
adcx r10, [ rsp + 0x328 ]
mov rax, [ rsp + 0x320 ]
adcx rax, [ rsp + 0x338 ]
mov [ rsp + 0x3b0 ], r15
setc r15b
clc
mov [ rsp + 0x3b8 ], r12
mov r12, -0x1 
movzx r13, r13b
adcx r13, r12
adcx rdi, r14
mov r13, [ rsp + 0x300 ]
seto r14b
movzx r12, byte [ rsp + 0x308 ]
mov [ rsp + 0x3c0 ], rax
mov rax, 0x0 
dec rax
adox r12, rax
adox r13, [ rsp + 0x2f8 ]
setc r12b
clc
movzx r8, r8b
adcx r8, rax
adcx rdi, rbp
mov rbp, [ rsp + 0x2f0 ]
adox rbp, [ rsp + 0x2e8 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, rax
adcx r13, [ rsp + 0x1a8 ]
adox rbx, [ rsp + 0x2e0 ]
mov rdx, [ rsp + 0x358 ]
setc al
mov byte [ rsp + 0x3c8 ], r8b
movzx r8, byte [ rsp + 0x3a8 ]
clc
mov [ rsp + 0x3d0 ], r10
mov r10, -0x1 
adcx r8, r10
adcx rdx, [ rsp + 0x38 ]
seto r8b
inc r10
mov r10, -0x1 
movzx rax, al
adox rax, r10
adox rbp, [ rsp + 0x1c8 ]
mov rax, [ rsp + 0x388 ]
setc r10b
clc
mov [ rsp + 0x3d8 ], rdx
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx rax, [ rsp + 0x68 ]
mov r14, 0x2341f27177344 
mov rdx, r11
mov byte [ rsp + 0x3e0 ], r10b
mulx r10, r11, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x3e8 ], rax
mulx rax, r14, r9
adox rbx, [ rsp + 0x2d0 ]
mov rdx, r14
mov [ rsp + 0x3f0 ], rbx
seto bl
mov byte [ rsp + 0x3f8 ], r8b
mov r8, -0x2 
inc r8
adox rdx, r9
setc dl
clc
movzx r12, r12b
adcx r12, r8
adcx r13, rcx
mov rcx, r14
setc r12b
clc
adcx rcx, rax
seto r8b
mov byte [ rsp + 0x400 ], dl
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox r11, [ rsp + 0x318 ]
mov r15, 0x0 
adox r10, r15
inc rdx
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox rdi, rcx
setc r8b
clc
movzx r12, r12b
adcx r12, r15
adcx rbp, [ rsp + 0x3d0 ]
movzx r12, byte [ rsp + 0x2d8 ]
mov rcx, [ rsp + 0x198 ]
lea r12, [ r12 + rcx ]
seto cl
movzx rdx, byte [ rsp + 0x3f8 ]
inc r15
mov r15, -0x1 
adox rdx, r15
adox r12, [ rsp + 0x370 ]
mov rdx, [ rsp + 0x3f0 ]
adcx rdx, [ rsp + 0x3c0 ]
mov r15, rax
mov [ rsp + 0x408 ], r10
seto r10b
mov byte [ rsp + 0x410 ], cl
mov rcx, 0x0 
dec rcx
movzx r8, r8b
adox r8, rcx
adox r15, r14
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r9
mulx rcx, r8, r14
mov r14, 0x7bc65c783158aea3 
mov [ rsp + 0x418 ], r15
mov [ rsp + 0x420 ], r11
mulx r11, r15, r14
seto r14b
mov [ rsp + 0x428 ], rcx
movzx rcx, byte [ rsp + 0x3c8 ]
mov [ rsp + 0x430 ], r8
mov r8, -0x1 
inc r8
mov r8, -0x1 
adox rcx, r8
adox r13, [ rsp + 0x3a0 ]
setc cl
clc
movzx r14, r14b
adcx r14, r8
adcx rax, [ rsp + 0x380 ]
seto r14b
inc r8
mov r8, -0x1 
movzx rbx, bl
adox rbx, r8
adox r12, [ rsp + 0x2c8 ]
adcx r15, [ rsp + 0x378 ]
movzx r10, r10b
movzx rbx, r10b
adox rbx, [ rsp + 0x2b0 ]
seto r10b
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rbp, [ rsp + 0x398 ]
mov r14, 0x2341f27177344 
mov byte [ rsp + 0x438 ], r10b
mulx r10, r8, r14
adox r9, [ rsp + 0x3b8 ]
setc dl
clc
adcx rdi, [ rsp + 0xc0 ]
setc r14b
clc
mov [ rsp + 0x440 ], r10
mov r10, -0x1 
movzx rdx, dl
adcx rdx, r10
adcx r11, [ rsp + 0x430 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x448 ], r11
mulx r11, r10, rdi
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x450 ], r11
mov [ rsp + 0x458 ], r10
mulx r10, r11, rdi
adcx r8, [ rsp + 0x428 ]
setc dl
clc
mov [ rsp + 0x460 ], r10
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx r12, [ rsp + 0x420 ]
adox r12, [ rsp + 0x3b0 ]
seto cl
movzx r10, byte [ rsp + 0x410 ]
mov [ rsp + 0x468 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox r10, r11
adox r13, [ rsp + 0x418 ]
seto r10b
inc r11
mov r11, -0x1 
movzx r14, r14b
adox r14, r11
adox r13, [ rsp + 0xd0 ]
mov r14, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov [ rsp + 0x470 ], r8
mulx r8, r11, r14
mov r14, 0xfdc1767ae2ffffff 
mov [ rsp + 0x478 ], r8
mov [ rsp + 0x480 ], r11
mulx r11, r8, r14
seto r14b
mov [ rsp + 0x488 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox rbp, rax
mov rax, 0xffffffffffffffff 
mulx r11, r10, rax
adox r15, r9
mov r9, r10
setc al
clc
adcx r9, r11
mov [ rsp + 0x490 ], r12
mov r12, r10
adcx r12, r11
mov [ rsp + 0x498 ], r12
seto r12b
mov byte [ rsp + 0x4a0 ], cl
mov rcx, 0x0 
dec rcx
movzx rax, al
adox rax, rcx
adox rbx, [ rsp + 0x408 ]
movzx rax, byte [ rsp + 0x438 ]
mov rcx, 0x0 
adox rax, rcx
mov [ rsp + 0x4a8 ], rax
mov rax, -0x3 
inc rax
adox r10, rdx
seto r10b
dec rcx
movzx r14, r14b
adox r14, rcx
adox rbp, [ rsp + 0x148 ]
seto dl
inc rcx
mov r14, -0x1 
movzx r10, r10b
adox r10, r14
adox r13, r9
seto r9b
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r15, [ rsp + 0x208 ]
adcx r8, r11
movzx r14, dil
mov r11, [ rsp + 0x440 ]
lea r14, [ r14 + r11 ]
movzx r11, byte [ rsp + 0x400 ]
mov rdi, [ rsp + 0x60 ]
lea r11, [ r11 + rdi ]
setc dil
movzx r10, byte [ rsp + 0x4a0 ]
clc
adcx r10, rcx
adcx rbx, [ rsp + 0x3e8 ]
mov r10, [ rsp + 0x490 ]
setc dl
clc
movzx r12, r12b
adcx r12, rcx
adcx r10, [ rsp + 0x448 ]
adcx rbx, [ rsp + 0x470 ]
seto r12b
inc rcx
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox r11, [ rsp + 0x4a8 ]
adcx r14, r11
setc dl
clc
adcx r13, [ rsp + 0x230 ]
mov r11, 0x2341f27177344 
xchg rdx, r11
mulx rax, rcx, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x4b0 ], r14
mov [ rsp + 0x4b8 ], rax
mulx rax, r14, r13
setc dl
clc
mov [ rsp + 0x4c0 ], rcx
mov rcx, -0x1 
movzx r9, r9b
adcx r9, rcx
adcx rbp, [ rsp + 0x498 ]
movzx r9, r11b
mov rcx, 0x0 
adox r9, rcx
dec rcx
movzx rdx, dl
adox rdx, rcx
adox rbp, [ rsp + 0x2a8 ]
setc r11b
clc
movzx r12, r12b
adcx r12, rcx
adcx r10, [ rsp + 0x200 ]
adcx rbx, [ rsp + 0x290 ]
mov r12, [ rsp + 0x488 ]
setc dl
clc
movzx rdi, dil
adcx rdi, rcx
adcx r12, [ rsp + 0x468 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov [ rsp + 0x4c8 ], r9
mulx r9, rcx, r13
mov rdx, [ rsp + 0x460 ]
adcx rdx, [ rsp + 0x480 ]
mov byte [ rsp + 0x4d0 ], dil
mov rdi, r14
mov [ rsp + 0x4d8 ], rdx
setc dl
clc
adcx rdi, rax
mov byte [ rsp + 0x4e0 ], dl
mov rdx, r14
mov [ rsp + 0x4e8 ], rbx
seto bl
mov [ rsp + 0x4f0 ], r12
mov r12, -0x2 
inc r12
adox rdx, r13
adox rdi, rbp
mov rdx, 0x7bc65c783158aea3 
mulx r12, rbp, r13
seto dl
mov [ rsp + 0x4f8 ], r10
mov r10, -0x2 
inc r10
adox rdi, [ rsp - 0x48 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov byte [ rsp + 0x500 ], r10b
mov byte [ rsp + 0x508 ], bl
mulx rbx, r10, r13
mov [ rsp + 0x510 ], r9
mulx r9, r13, rdi
adcx r14, rax
adcx r10, rax
adcx rbp, rbx
adcx rcx, r12
seto al
mov r12, -0x1 
inc r12
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox r15, r8
mov r8, [ rsp + 0x510 ]
adcx r8, [ rsp + 0x4c0 ]
mov r11, [ rsp + 0x4b8 ]
adcx r11, r12
movzx r12, byte [ rsp + 0x508 ]
clc
adcx r12, rbx
adcx r15, [ rsp + 0x298 ]
mov r12, [ rsp + 0x4f0 ]
adox r12, [ rsp + 0x4f8 ]
adcx r12, [ rsp + 0x2c0 ]
setc bl
movzx rdx, byte [ rsp + 0x500 ]
clc
mov [ rsp + 0x518 ], r11
mov r11, -0x1 
adcx rdx, r11
adcx r15, r14
adcx r10, r12
mov rdx, [ rsp + 0x4d8 ]
adox rdx, [ rsp + 0x4e8 ]
seto r14b
inc r11
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rdx, [ rsp + 0x2b8 ]
mov rbx, [ rsp + 0x2a0 ]
seto r11b
movzx r12, byte [ rsp + 0x4d0 ]
mov [ rsp + 0x520 ], r8
mov r8, 0x0 
dec r8
adox r12, r8
adox rbx, [ rsp + 0x4b0 ]
mov r12, [ rsp + 0x368 ]
adox r12, [ rsp + 0x4c8 ]
adcx rbp, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x528 ], rcx
mulx rcx, r8, [ rsi + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x530 ], r11b
mov [ rsp + 0x538 ], r12
mulx r12, r11, rdi
setc dl
mov [ rsp + 0x540 ], rbx
movzx rbx, byte [ rsp + 0x238 ]
clc
mov byte [ rsp + 0x548 ], r14b
mov r14, -0x1 
adcx rbx, r14
adcx r8, [ rsp + 0x80 ]
seto bl
inc r14
mov r14, -0x1 
movzx rax, al
adox rax, r14
adox r15, [ rsp + 0x150 ]
mov rax, r11
seto r14b
mov [ rsp + 0x550 ], r8
mov r8, -0x2 
inc r8
adox rax, rdi
mov rax, r11
setc r8b
clc
adcx rax, r12
adox rax, r15
seto r15b
mov byte [ rsp + 0x558 ], bl
mov rbx, -0x2 
inc rbx
adox rax, [ rsp + 0x10 ]
adcx r11, r12
movzx rbx, r8b
lea rbx, [ rbx + rcx ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x560 ], rbx
mulx rbx, r8, rcx
mov rcx, 0x7bc65c783158aea3 
mov [ rsp + 0x568 ], rbx
mov [ rsp + 0x570 ], r8
mulx r8, rbx, rcx
xchg rdx, rdi
mov [ rsp + 0x578 ], r8
mov [ rsp + 0x580 ], rbx
mulx rbx, r8, rcx
mov rcx, [ rsp + 0x478 ]
mov [ rsp + 0x588 ], r11
seto r11b
mov byte [ rsp + 0x590 ], r15b
movzx r15, byte [ rsp + 0x4e0 ]
mov byte [ rsp + 0x598 ], al
mov rax, 0x0 
dec rax
adox r15, rax
adox rcx, [ rsp + 0x458 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov byte [ rsp + 0x5a0 ], r11b
mulx r11, rax, r15
mov r15, [ rsp + 0x450 ]
mov [ rsp + 0x5a8 ], r11
mov r11, 0x0 
adox r15, r11
adcx r13, r12
dec r11
movzx r14, r14b
adox r14, r11
adox r10, [ rsp + 0x190 ]
adcx r8, r9
adox rbp, [ rsp + 0x188 ]
movzx r9, byte [ rsp + 0x3e0 ]
mov r12, [ rsp + 0x30 ]
lea r9, [ r9 + r12 ]
mov r12, 0xffffffffffffffff 
mulx r11, r14, r12
seto r12b
mov [ rsp + 0x5b0 ], r9
movzx r9, byte [ rsp + 0x548 ]
mov [ rsp + 0x5b8 ], rax
mov rax, 0x0 
dec rax
adox r9, rax
adox rcx, [ rsp + 0x540 ]
mov r9, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x5c0 ], r8
mulx r8, rax, rdi
adox r15, [ rsp + 0x538 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x5c8 ], r8
mov [ rsp + 0x5d0 ], r15
mulx r15, r8, rdi
adcx r8, rbx
seto dil
movzx rbx, byte [ rsp + 0x530 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox rbx, rdx
adox rcx, [ rsp + 0x390 ]
mov rbx, r14
setc dl
clc
adcx rbx, r11
mov [ rsp + 0x5d8 ], r8
setc r8b
mov [ rsp + 0x5e0 ], rbx
movzx rbx, byte [ rsp + 0x598 ]
clc
mov byte [ rsp + 0x5e8 ], dil
mov rdi, -0x1 
adcx rbx, rdi
adcx rcx, [ rsp + 0x528 ]
seto bl
inc rdi
mov rdi, -0x1 
movzx rdx, dl
adox rdx, rdi
adox r15, rax
setc al
clc
movzx r12, r12b
adcx r12, rdi
adcx rcx, [ rsp + 0x1c0 ]
setc r12b
movzx rdx, byte [ rsp + 0x590 ]
clc
adcx rdx, rdi
adcx r10, [ rsp + 0x588 ]
adcx r13, rbp
adcx rcx, [ rsp + 0x5c0 ]
setc dl
movzx rbp, byte [ rsp + 0x5a0 ]
clc
adcx rbp, rdi
adcx r10, [ rsp + 0x1a0 ]
movzx rbp, byte [ rsp + 0x5e8 ]
movzx rdi, byte [ rsp + 0x558 ]
lea rbp, [ rbp + rdi ]
mov rdi, r14
mov [ rsp + 0x5f0 ], r15
setc r15b
clc
adcx rdi, r9
adcx r10, [ rsp + 0x5e0 ]
mov rdi, r11
mov byte [ rsp + 0x5f8 ], dl
setc dl
clc
mov byte [ rsp + 0x600 ], r12b
mov r12, -0x1 
movzx r8, r8b
adcx r8, r12
adcx rdi, r14
seto r14b
inc r12
mov r8, -0x1 
movzx r15, r15b
adox r15, r8
adox r13, [ rsp + 0x1b8 ]
adcx r11, [ rsp + 0x570 ]
mov r15, [ rsp + 0x568 ]
adcx r15, [ rsp + 0x580 ]
mov r12, [ rsp + 0x578 ]
adcx r12, [ rsp + 0x5b8 ]
setc r8b
mov byte [ rsp + 0x608 ], r14b
seto r14b
mov [ rsp + 0x610 ], r12
mov r12, r10
mov [ rsp + 0x618 ], r15
mov r15, 0xffffffffffffffff 
sub r12, r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox r13, rdi
seto dl
mov rdi, r13
mov r15, 0xffffffffffffffff 
sbb rdi, r15
mov r15, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x620 ], r12
mov [ rsp + 0x628 ], rdi
mulx rdi, r12, r15
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r12, [ rsp + 0x5a8 ]
mov r8, 0x0 
adox rdi, r8
dec r8
movzx r14, r14b
adox r14, r8
adox rcx, [ rsp + 0x1b0 ]
mov rdx, [ rsp + 0x3d8 ]
setc r14b
clc
movzx rbx, bl
adcx rbx, r8
adcx rdx, [ rsp + 0x5d0 ]
adcx rbp, [ rsp + 0x5b0 ]
setc bl
clc
movzx r9, r9b
adcx r9, r8
adcx rcx, r11
setc r11b
seto r9b
movzx r8, r14b
add r8, -0x1
mov r8, rcx
mov r14, 0xffffffffffffffff 
sbb r8, r14
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rax, al
adox rax, r15
adox rdx, [ rsp + 0x520 ]
setc al
movzx r15, byte [ rsp + 0x600 ]
clc
mov r14, -0x1 
adcx r15, r14
adcx rdx, [ rsp + 0x218 ]
adox rbp, [ rsp + 0x518 ]
movzx r15, bl
mov r14, 0x0 
adox r15, r14
adcx rbp, [ rsp + 0x550 ]
adcx r15, [ rsp + 0x560 ]
movzx rbx, byte [ rsp + 0x5f8 ]
dec r14
adox rbx, r14
adox rdx, [ rsp + 0x5d8 ]
setc bl
clc
movzx r9, r9b
adcx r9, r14
adcx rdx, [ rsp + 0x1f0 ]
adox rbp, [ rsp + 0x5f0 ]
adcx rbp, [ rsp + 0x1f8 ]
seto r9b
inc r14
mov r14, -0x1 
movzx r11, r11b
adox r11, r14
adox rdx, [ rsp + 0x618 ]
adox rbp, [ rsp + 0x610 ]
setc r11b
seto r14b
mov [ rsp + 0x630 ], r8
movzx r8, al
add r8, -0x1
mov rax, rdx
mov r8, 0xfdc1767ae2ffffff 
sbb rax, r8
movzx r8, byte [ rsp + 0x608 ]
mov [ rsp + 0x638 ], rax
mov rax, [ rsp + 0x5c8 ]
lea r8, [ r8 + rax ]
mov rax, 0x0 
dec rax
movzx r9, r9b
adox r9, rax
adox r15, r8
setc r9b
clc
movzx r11, r11b
adcx r11, rax
adcx r15, [ rsp + 0x240 ]
movzx r11, bl
mov r8, 0x0 
adox r11, r8
adcx r11, [ rsp + 0x360 ]
inc rax
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox r15, r12
adox rdi, r11
setc r12b
seto bl
movzx r14, r9b
add r14, -0x1
mov r9, rbp
mov r14, 0x7bc65c783158aea3 
sbb r9, r14
movzx r11, bl
movzx r12, r12b
lea r11, [ r11 + r12 ]
mov r12, r15
mov rbx, 0x6cfc5fd681c52056 
sbb r12, rbx
mov rax, rdi
mov r8, 0x2341f27177344 
sbb rax, r8
sbb r11, 0x00000000
cmovc rax, rdi
mov r11, [ rsp + 0x630 ]
cmovc r11, rcx
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r11
mov [ rcx + 0x30 ], rax
mov rdi, [ rsp + 0x628 ]
cmovc rdi, r13
mov [ rcx + 0x8 ], rdi
mov r13, [ rsp + 0x638 ]
cmovc r13, rdx
cmovc r9, rbp
mov [ rcx + 0x18 ], r13
mov rdx, [ rsp + 0x620 ]
cmovc rdx, r10
mov [ rcx + 0x20 ], r9
cmovc r12, r15
mov [ rcx + 0x0 ], rdx
mov [ rcx + 0x28 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1728
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1658
; seed 4177143977034186 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 64672 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 957 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.014797748639287482
; number reverted permutation / tried permutation: 288 / 511 =56.360%
; number reverted decision / tried decision: 250 / 488 =51.230%
; validated in 272.507s
