SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1592
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r8
mulx r8, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r13
mulx r13, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], r10
mulx r10, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r9
mulx r9, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], rax
mulx rax, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rax
mov [ rsp + 0x38 ], r12
mulx r12, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], r15
mulx r15, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r8
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x60 ], r14
mov [ rsp + 0x68 ], r12
mulx r12, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r12
mov [ rsp + 0x78 ], r14
mulx r14, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r12
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r12
mov [ rsp + 0x98 ], r14
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r12
mov [ rsp + 0xa8 ], rax
mulx rax, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], rax
mov [ rsp + 0xb8 ], r12
mulx r12, rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], rax
mulx rax, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd0 ], rbp
mov [ rsp + 0xd8 ], rbx
mulx rbx, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], rbx
mulx rbx, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x100 ], rbx
mov [ rsp + 0x108 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], r9
mov [ rsp + 0x118 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], rcx
mov [ rsp + 0x138 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], rcx
mov [ rsp + 0x148 ], rdi
mulx rdi, rcx, rdx
test al, al
adox r15, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r15
mulx r15, r13, [ rsi + 0x18 ]
adcx rcx, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x158 ], r13
mulx r13, r14, [ rsi + 0x28 ]
adcx r12, rdi
adox r9, r8
adcx rbp, rax
setc dl
clc
adcx r11, r15
adox r10, rbx
mov r8, [ rsp + 0x148 ]
adcx r8, [ rsp + 0x138 ]
mov al, dl
mov rdx, [ rsi + 0x28 ]
mulx rdi, rbx, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x128 ]
seto r15b
mov [ rsp + 0x160 ], rdi
mov rdi, -0x2 
inc rdi
adox rdx, [ rsp + 0x120 ]
mov rdi, [ rsp + 0xd8 ]
adox rdi, [ rsp + 0x108 ]
mov [ rsp + 0x168 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r8
mov [ rsp + 0x178 ], r11
mulx r11, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x180 ], rdi
mov [ rsp + 0x188 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
mov rdx, [ rsp + 0xd0 ]
adox rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x190 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x198 ], rbp
mov [ rsp + 0x1a0 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsp + 0x60 ]
adox rdx, [ rsp + 0x68 ]
adox r8, [ rsp + 0x48 ]
mov [ rsp + 0x1a8 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b0 ], r9
mov [ rsp + 0x1b8 ], rcx
mulx rcx, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1c0 ], r8
mov [ rsp + 0x1c8 ], r13
mulx r13, r8, [ rsi + 0x8 ]
setc dl
clc
adcx r9, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x28 ]
mov [ rsp + 0x1d0 ], rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x1d8 ], r9
mov [ rsp + 0x1e0 ], r13
mulx r13, r9, rbp
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1e8 ], r13
mov [ rsp + 0x1f0 ], r9
mulx r9, r13, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1f8 ], r9
mov [ rsp + 0x200 ], r13
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x208 ], r14
mov [ rsp + 0x210 ], r8
mulx r8, r14, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x218 ], r8
mov [ rsp + 0x220 ], r14
mulx r14, r8, [ rsi + 0x0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x228 ], r8
mov byte [ rsp + 0x230 ], al
mulx rax, r8, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x238 ], rax
mov [ rsp + 0x240 ], r8
mulx r8, rax, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x248 ], r13
mov [ rsp + 0x250 ], r9
mulx r9, r13, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x20 ]
mov [ rsp + 0x258 ], r12
setc r12b
clc
mov byte [ rsp + 0x260 ], r15b
mov r15, -0x1 
movzx rcx, cl
adcx rcx, r15
adcx rdx, [ rsp + 0x18 ]
adcx rdi, [ rsp + 0x10 ]
adcx r10, [ rsp + 0xb8 ]
adox rbx, r11
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, r11, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x268 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r12, r12b
adox r12, rbx
adox r13, [ rsp - 0x8 ]
mov r12, rax
setc bl
clc
adcx r12, r8
adox r9, [ rsp - 0x10 ]
mov [ rsp + 0x270 ], r9
seto r9b
mov [ rsp + 0x278 ], r13
mov r13, -0x2 
inc r13
adox r11, r14
mov r14, [ rsp + 0xb0 ]
setc r13b
clc
mov byte [ rsp + 0x280 ], dl
mov rdx, -0x1 
movzx rbx, bl
adcx rbx, rdx
adcx r14, [ rsp + 0x8 ]
mov rbx, [ rsp + 0x130 ]
seto dl
mov [ rsp + 0x288 ], r11
movzx r11, byte [ rsp + 0x260 ]
mov [ rsp + 0x290 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r11, r14
adox rbx, [ rsp + 0x38 ]
mov r11, [ rsp + 0x30 ]
adox r11, [ rsp - 0x18 ]
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x298 ], r10
mov [ rsp + 0x2a0 ], rdi
mulx rdi, r10, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x258 ]
mov [ rsp + 0x2a8 ], rcx
seto cl
mov [ rsp + 0x2b0 ], r11
mov r11, -0x2 
inc r11
adox rdx, [ rsp + 0x250 ]
mov r11, [ rsp + 0x58 ]
adox r11, [ rsp + 0x248 ]
adox r10, [ rsp + 0x50 ]
mov [ rsp + 0x2b8 ], rbx
mov rbx, [ rsp + 0x210 ]
mov [ rsp + 0x2c0 ], r10
setc r10b
mov [ rsp + 0x2c8 ], r11
movzx r11, byte [ rsp + 0x230 ]
clc
mov [ rsp + 0x2d0 ], r15
mov r15, -0x1 
adcx r11, r15
adcx rbx, [ rsp + 0x100 ]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x2d8 ], r10b
mulx r10, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2e0 ], rbx
mov byte [ rsp + 0x2e8 ], r14b
mulx r14, rbx, [ rsi + 0x0 ]
adox r15, rdi
adox r10, [ rsp + 0x208 ]
mov rdx, [ rsp - 0x20 ]
seto dil
mov [ rsp + 0x2f0 ], r10
mov r10, 0x0 
dec r10
movzx r9, r9b
adox r9, r10
adox rdx, [ rsp + 0x118 ]
mov r9, r8
setc r10b
clc
mov [ rsp + 0x2f8 ], rdx
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r9, rax
adcx r8, [ rsp + 0x1f0 ]
setc r13b
clc
movzx rdi, dil
adcx rdi, rdx
adcx rbx, [ rsp + 0x1c8 ]
mov rdi, [ rsp + 0x1e0 ]
setc dl
clc
mov [ rsp + 0x300 ], rbx
mov rbx, -0x1 
movzx r10, r10b
adcx r10, rbx
adcx rdi, [ rsp + 0xf8 ]
movzx r10, dl
lea r10, [ r10 + r14 ]
mov r14, [ rsp + 0xf0 ]
adcx r14, [ rsp + 0x88 ]
mov rdx, [ rsp + 0x110 ]
adox rdx, [ rsp + 0xc8 ]
mov rbx, [ rsp + 0x80 ]
mov [ rsp + 0x308 ], rdx
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, [ rsp + 0xc0 ]
mov [ rsp + 0x310 ], rbx
mov rbx, 0x0 
adox rdx, rbx
mov rbx, [ rsp + 0x78 ]
add cl, 0xFF
adcx rbx, [ rsp - 0x28 ]
adox rax, rbp
adox r12, r11
setc al
clc
adcx r12, [ rsp + 0xa0 ]
mov rbp, 0x2341f27177344 
xchg rdx, rbp
mulx r11, rcx, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x318 ], rbp
mov byte [ rsp + 0x320 ], al
mulx rax, rbp, [ rsi + 0x20 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x328 ], rbx
mov [ rsp + 0x330 ], r11
mulx r11, rbx, r12
mov rdx, [ rsp + 0x220 ]
mov [ rsp + 0x338 ], r14
seto r14b
mov [ rsp + 0x340 ], rdi
mov rdi, 0x0 
dec rdi
movzx r13, r13b
adox r13, rdi
adox rdx, [ rsp + 0x1e8 ]
mov r13, [ rsp + 0x218 ]
adox r13, [ rsp + 0x200 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x348 ], rcx
mov [ rsp + 0x350 ], r11
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x1f8 ]
adox rdx, [ rsp + 0x240 ]
mov [ rsp + 0x358 ], rbx
seto bl
mov [ rsp + 0x360 ], r10
movzx r10, byte [ rsp + 0x2e8 ]
mov [ rsp + 0x368 ], rdx
mov rdx, 0x0 
dec rdx
adox r10, rdx
adox rcx, [ rsp + 0x2d0 ]
adox rbp, r11
adox rax, [ rsp - 0x38 ]
mov r10, [ rsp - 0x40 ]
adox r10, [ rsp + 0x98 ]
setc r11b
clc
movzx r14, r14b
adcx r14, rdx
adcx r9, [ rsp + 0x2c8 ]
adcx r8, [ rsp + 0x2c0 ]
adcx rdi, r15
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, r12
mov rdx, [ rsp + 0xe8 ]
adox rdx, [ rsp + 0x90 ]
mov [ rsp + 0x370 ], rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x378 ], r10
mov [ rsp + 0x380 ], rax
mulx rax, r10, r12
mov rdx, r15
mov [ rsp + 0x388 ], rbp
seto bpl
mov [ rsp + 0x390 ], rcx
mov rcx, -0x2 
inc rcx
adox rdx, r14
mov rcx, r15
adox rcx, r14
adox r10, r14
seto r14b
mov [ rsp + 0x398 ], rax
mov rax, 0x0 
dec rax
movzx r11, r11b
adox r11, rax
adox r9, [ rsp + 0x1b8 ]
adcx r13, [ rsp + 0x2f0 ]
seto r11b
inc rax
adox r15, r12
movzx r15, bpl
mov rax, [ rsp + 0xe0 ]
lea r15, [ r15 + rax ]
adox rdx, r9
seto al
mov rbp, -0x2 
inc rbp
adox rdx, [ rsp + 0x140 ]
mov r9, [ rsp + 0x300 ]
adcx r9, [ rsp + 0x368 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov [ rsp + 0x3a0 ], r15
mov [ rsp + 0x3a8 ], r9
mulx r9, r15, r12
movzx r12, bl
mov rdx, [ rsp + 0x238 ]
lea r12, [ r12 + rdx ]
adcx r12, [ rsp + 0x360 ]
setc dl
clc
mov rbx, -0x1 
movzx r11, r11b
adcx r11, rbx
adcx r8, [ rsp + 0x1a0 ]
mov r11, 0x2341f27177344 
xchg rdx, r11
mov byte [ rsp + 0x3b0 ], r11b
mulx r11, rbx, rbp
adcx rdi, [ rsp + 0x198 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x3b8 ], r11
mov [ rsp + 0x3c0 ], rbx
mulx rbx, r11, rbp
setc dl
clc
mov [ rsp + 0x3c8 ], rbx
mov rbx, -0x1 
movzx rax, al
adcx rax, rbx
adcx r8, rcx
adox r8, [ rsp + 0x150 ]
adcx r10, rdi
adox r10, [ rsp + 0x190 ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, rbp
mulx rdi, rax, rcx
mov rbx, [ rsp + 0x398 ]
seto cl
mov [ rsp + 0x3d0 ], rdi
mov rdi, 0x0 
dec rdi
movzx r14, r14b
adox r14, rdi
adox rbx, [ rsp + 0x358 ]
adox r15, [ rsp + 0x350 ]
adox r9, [ rsp + 0x348 ]
seto r14b
inc rdi
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox r13, [ rsp + 0x2e0 ]
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x3d8 ], rax
mulx rax, rdi, rbp
adcx rbx, r13
mov r13, [ rsp + 0x3a8 ]
adox r13, [ rsp + 0x340 ]
adox r12, [ rsp + 0x338 ]
setc bpl
clc
mov [ rsp + 0x3e0 ], r11
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx rbx, [ rsp + 0x188 ]
mov rcx, [ rsp + 0x310 ]
movzx r11, byte [ rsp + 0x3b0 ]
adox r11, rcx
mov rcx, rdi
mov [ rsp + 0x3e8 ], r11
seto r11b
mov [ rsp + 0x3f0 ], rbx
mov rbx, -0x2 
inc rbx
adox rcx, rdx
mov rcx, rdi
setc bl
clc
adcx rcx, rax
adcx rdi, rax
adox rcx, r8
mov r8, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x3f8 ], r11b
mov byte [ rsp + 0x400 ], r14b
mulx r14, r11, r8
adox rdi, r10
seto dl
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox r13, r15
adox r9, r12
seto r15b
inc r10
mov rbp, -0x1 
movzx rbx, bl
adox rbx, rbp
adox r13, [ rsp + 0x2b8 ]
adcx r11, rax
seto al
mov r12, -0x3 
inc r12
adox rcx, [ rsp + 0x158 ]
movzx rbx, byte [ rsp + 0x400 ]
mov r10, [ rsp + 0x330 ]
lea rbx, [ rbx + r10 ]
seto r10b
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r11, [ rsp + 0x3f0 ]
setc dl
clc
movzx rax, al
adcx rax, rbp
adcx r9, [ rsp + 0x2b0 ]
setc al
clc
movzx r15, r15b
adcx r15, rbp
adcx rbx, [ rsp + 0x3e8 ]
movzx r15, byte [ rsp + 0x3f8 ]
mov rbp, 0x0 
adcx r15, rbp
clc
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx rdi, [ rsp + 0x178 ]
setc r10b
clc
movzx rax, al
adcx rax, rbp
adcx rbx, [ rsp + 0x328 ]
xchg rdx, r8
mulx rbp, rax, rcx
mov r12, 0x7bc65c783158aea3 
mov rdx, rcx
mov [ rsp + 0x408 ], rdi
mulx rdi, rcx, r12
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x410 ], rbx
mov [ rsp + 0x418 ], rdi
mulx rdi, rbx, r12
mov r12, rbx
mov [ rsp + 0x420 ], r9
seto r9b
mov [ rsp + 0x428 ], r13
mov r13, -0x2 
inc r13
adox r12, rdi
mov r13, rbx
adox r13, rdi
mov [ rsp + 0x430 ], r13
movzx r13, byte [ rsp + 0x320 ]
mov [ rsp + 0x438 ], r12
mov r12, [ rsp + 0x70 ]
lea r13, [ r13 + r12 ]
mov r12, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x440 ], r9b
mov [ rsp + 0x448 ], rcx
mulx rcx, r9, r12
adcx r13, r15
setc r15b
clc
mov r12, -0x1 
movzx r8, r8b
adcx r8, r12
adcx r14, [ rsp + 0x3e0 ]
adox rax, rdi
setc r8b
clc
movzx r10, r10b
adcx r10, r12
adcx r11, [ rsp + 0x170 ]
mov r10, [ rsp + 0x3c8 ]
setc dil
clc
movzx r8, r8b
adcx r8, r12
adcx r10, [ rsp + 0x3d8 ]
adox rbp, [ rsp + 0x448 ]
setc r8b
clc
adcx rbx, rdx
setc bl
movzx r12, byte [ rsp + 0x440 ]
clc
mov [ rsp + 0x450 ], rcx
mov rcx, -0x1 
adcx r12, rcx
adcx r14, [ rsp + 0x428 ]
adcx r10, [ rsp + 0x420 ]
adox r9, [ rsp + 0x418 ]
mov r12, [ rsp + 0x3d0 ]
seto cl
mov [ rsp + 0x458 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox r12, [ rsp + 0x3c0 ]
mov r8, [ rsp + 0x3b8 ]
mov r9, 0x0 
adox r8, r9
dec r9
movzx rdi, dil
adox rdi, r9
adox r14, [ rsp + 0x2a8 ]
adcx r12, [ rsp + 0x410 ]
adox r10, [ rsp + 0x2a0 ]
adcx r8, r13
movzx r13, r15b
mov rdi, 0x0 
adcx r13, rdi
adox r12, [ rsp + 0x298 ]
mov r15, [ rsp + 0x438 ]
clc
movzx rbx, bl
adcx rbx, r9
adcx r15, [ rsp + 0x408 ]
adcx r11, [ rsp + 0x430 ]
movzx rbx, byte [ rsp + 0x2d8 ]
mov rdi, [ rsp + 0x0 ]
lea rbx, [ rbx + rdi ]
adcx rax, r14
adox r8, [ rsp + 0x290 ]
setc dil
clc
adcx r15, [ rsp + 0x228 ]
adcx r11, [ rsp + 0x288 ]
adcx rax, [ rsp + 0x390 ]
mov r14, 0x2341f27177344 
xchg rdx, r14
mov [ rsp + 0x460 ], rax
mulx rax, r9, r15
adox rbx, r13
mov r13, 0xfdc1767ae2ffffff 
mov rdx, r13
mov [ rsp + 0x468 ], rax
mulx rax, r13, r15
seto dl
mov [ rsp + 0x470 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx rdi, dil
adox rdi, r9
adox r10, rbp
adox r12, [ rsp + 0x458 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mulx r9, rdi, r15
adcx r10, [ rsp + 0x388 ]
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x478 ], bpl
mov [ rsp + 0x480 ], rax
mulx rax, rbp, r14
adcx r12, [ rsp + 0x380 ]
mov r14, rdi
seto dl
mov [ rsp + 0x488 ], r12
mov r12, -0x2 
inc r12
adox r14, r15
mov r14, rdi
seto r12b
mov [ rsp + 0x490 ], r10
mov r10, -0x2 
inc r10
adox r14, r9
mov r10, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x498 ], r13
mov [ rsp + 0x4a0 ], r14
mulx r14, r13, r10
setc r10b
clc
mov [ rsp + 0x4a8 ], r14
mov r14, -0x1 
movzx rcx, cl
adcx rcx, r14
adcx rbp, [ rsp + 0x450 ]
mov rcx, 0x0 
adcx rax, rcx
clc
movzx r15, r15b
adcx r15, r14
adcx r8, rbp
adcx rax, rbx
setc bl
clc
movzx r12, r12b
adcx r12, r14
adcx r11, [ rsp + 0x4a0 ]
adox rdi, r9
adox r9, [ rsp + 0x498 ]
adcx rdi, [ rsp + 0x460 ]
seto r15b
mov r12, -0x3 
inc r12
adox r11, [ rsp - 0x48 ]
adcx r9, [ rsp + 0x490 ]
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, r11
mulx r12, rcx, rbp
seto r14b
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox r8, [ rsp + 0x378 ]
adox rax, [ rsp + 0x370 ]
mov r10, 0x2341f27177344 
mov byte [ rsp + 0x4b0 ], bl
mulx rbx, rbp, r10
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r10
mov [ rsp + 0x4b8 ], rbx
mov [ rsp + 0x4c0 ], rbp
mulx rbp, rbx, r11
mov r11, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp + 0x4c8 ], rax
mulx rax, r10, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x4d0 ], rbp
mov [ rsp + 0x4d8 ], r12
mulx r12, rbp, r11
mov r11, r10
mov [ rsp + 0x4e0 ], r12
setc r12b
clc
adcx r11, rdx
mov r11, r10
mov [ rsp + 0x4e8 ], rbp
setc bpl
clc
adcx r11, rax
adcx r10, rax
mov [ rsp + 0x4f0 ], r10
seto r10b
mov [ rsp + 0x4f8 ], r8
mov r8, 0x0 
dec r8
movzx r15, r15b
adox r15, r8
adox r13, [ rsp + 0x480 ]
adox rbx, [ rsp + 0x4a8 ]
seto r15b
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rdi, [ rsp + 0x180 ]
setc r14b
clc
movzx rbp, bpl
adcx rbp, r8
adcx rdi, r11
seto bpl
inc r8
adox rdi, [ rsp - 0x30 ]
seto r11b
dec r8
movzx rbp, bpl
adox rbp, r8
adox r9, [ rsp + 0x168 ]
seto bpl
inc r8
mov r8, -0x1 
movzx r12, r12b
adox r12, r8
adox r13, [ rsp + 0x488 ]
seto r12b
inc r8
mov r8, -0x1 
movzx r14, r14b
adox r14, r8
adox rax, rcx
setc cl
clc
movzx r12, r12b
adcx r12, r8
adcx rbx, [ rsp + 0x4f8 ]
mov r14, 0x6cfc5fd681c52056 
mulx r8, r12, r14
mov rdx, [ rsp + 0x4d8 ]
adox rdx, [ rsp + 0x4e8 ]
adox r12, [ rsp + 0x4e0 ]
mov r14, [ rsp + 0x4d0 ]
mov [ rsp + 0x500 ], r12
seto r12b
mov [ rsp + 0x508 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r15, r15b
adox r15, rdx
adox r14, [ rsp + 0x470 ]
mov r15, 0xfdc1767ae2ffffff 
mov rdx, rdi
mov [ rsp + 0x510 ], rax
mulx rax, rdi, r15
adcx r14, [ rsp + 0x4c8 ]
movzx r15, byte [ rsp + 0x4b0 ]
mov [ rsp + 0x518 ], rax
movzx rax, byte [ rsp + 0x478 ]
lea r15, [ r15 + rax ]
mov rax, 0x6cfc5fd681c52056 
mov [ rsp + 0x520 ], r14
mov [ rsp + 0x528 ], rbx
mulx rbx, r14, rax
mov rax, [ rsp + 0x468 ]
mov [ rsp + 0x530 ], rbx
mov rbx, 0x0 
adox rax, rbx
dec rbx
movzx r10, r10b
adox r10, rbx
adox r15, [ rsp + 0x3a0 ]
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x538 ], r14
mulx r14, rbx, r10
seto r10b
mov [ rsp + 0x540 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r12, r12b
adox r12, r14
adox r8, [ rsp + 0x4c0 ]
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x548 ], r8
mulx r8, r14, r12
mov r12, r14
mov [ rsp + 0x550 ], rbx
seto bl
mov byte [ rsp + 0x558 ], r10b
mov r10, -0x2 
inc r10
adox r12, r8
mov r10, r14
mov byte [ rsp + 0x560 ], bl
setc bl
clc
adcx r10, rdx
mov r10, 0x2341f27177344 
mov [ rsp + 0x568 ], rax
mov [ rsp + 0x570 ], r15
mulx r15, rax, r10
setc dl
clc
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx r9, [ rsp + 0x4f0 ]
setc cl
clc
movzx r11, r11b
adcx r11, r10
adcx r9, [ rsp + 0x1d8 ]
adox r14, r8
movzx r11, byte [ rsp + 0x280 ]
mov r10, [ rsp + 0x160 ]
lea r11, [ r11 + r10 ]
adox rdi, r8
setc r10b
clc
mov r8, -0x1 
movzx rbp, bpl
adcx rbp, r8
adcx r13, [ rsp + 0x1b0 ]
mov rbp, [ rsp + 0x528 ]
adcx rbp, [ rsp + 0x1c0 ]
mov r8, [ rsp + 0x1a8 ]
adcx r8, [ rsp + 0x520 ]
mov [ rsp + 0x578 ], r11
setc r11b
clc
mov [ rsp + 0x580 ], r15
mov r15, -0x1 
movzx rcx, cl
adcx rcx, r15
adcx r13, [ rsp + 0x510 ]
adcx rbp, [ rsp + 0x508 ]
setc cl
clc
movzx rdx, dl
adcx rdx, r15
adcx r9, r12
setc r12b
clc
movzx r10, r10b
adcx r10, r15
adcx r13, [ rsp + 0x1d0 ]
setc dl
seto r10b
mov r15, r9
mov [ rsp + 0x588 ], rax
mov rax, 0xffffffffffffffff 
sub r15, rax
mov rax, [ rsp + 0x570 ]
mov [ rsp + 0x590 ], r15
mov r15, 0x0 
dec r15
movzx rbx, bl
adox rbx, r15
adox rax, [ rsp + 0x568 ]
seto bl
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox r13, r14
movzx r14, bl
movzx r12, byte [ rsp + 0x558 ]
lea r14, [ r14 + r12 ]
setc r12b
clc
movzx rdx, dl
adcx rdx, r15
adcx rbp, [ rsp + 0x278 ]
adox rdi, rbp
seto dl
inc r15
mov rbx, -0x1 
movzx r11, r11b
adox r11, rbx
adox rax, [ rsp + 0x268 ]
seto r11b
dec r15
movzx rcx, cl
adox rcx, r15
adox r8, [ rsp + 0x500 ]
adcx r8, [ rsp + 0x270 ]
setc bl
seto cl
movzx rbp, r12b
add rbp, -0x1
mov rbp, r13
mov r12, 0xffffffffffffffff 
sbb rbp, r12
mov r15, [ rsp + 0x518 ]
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox r15, [ rsp + 0x550 ]
mov r10, [ rsp + 0x540 ]
adox r10, [ rsp + 0x538 ]
seto r12b
mov [ rsp + 0x598 ], rbp
mov rbp, rdi
mov [ rsp + 0x5a0 ], r10
mov r10, 0xffffffffffffffff 
sbb rbp, r10
mov r10, [ rsp + 0x530 ]
mov [ rsp + 0x5a8 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r12, r12b
adox r12, rbp
adox r10, [ rsp + 0x588 ]
mov r12, [ rsp + 0x580 ]
mov rbp, 0x0 
adox r12, rbp
dec rbp
movzx rdx, dl
adox rdx, rbp
adox r8, r15
seto dl
mov r15, r8
mov rbp, 0xfdc1767ae2ffffff 
sbb r15, rbp
movzx rbp, byte [ rsp + 0x560 ]
mov [ rsp + 0x5b0 ], r15
mov r15, [ rsp + 0x4b8 ]
lea rbp, [ rbp + r15 ]
mov r15, 0x0 
dec r15
movzx r11, r11b
adox r11, r15
adox r14, [ rsp + 0x578 ]
setc r11b
clc
movzx rcx, cl
adcx rcx, r15
adcx rax, [ rsp + 0x548 ]
adcx rbp, r14
seto cl
inc r15
mov r14, -0x1 
movzx rbx, bl
adox rbx, r14
adox rax, [ rsp + 0x2f8 ]
setc bl
clc
movzx rdx, dl
adcx rdx, r14
adcx rax, [ rsp + 0x5a0 ]
setc dl
seto r15b
movzx r14, r11b
add r14, -0x1
mov r11, rax
mov r14, 0x7bc65c783158aea3 
sbb r11, r14
mov r14, 0x0 
dec r14
movzx r15, r15b
adox r15, r14
adox rbp, [ rsp + 0x308 ]
movzx r15, bl
movzx rcx, cl
lea r15, [ r15 + rcx ]
adox r15, [ rsp + 0x318 ]
seto cl
inc r14
mov rbx, -0x1 
movzx rdx, dl
adox rdx, rbx
adox rbp, r10
adox r12, r15
movzx r10, cl
adox r10, r14
mov rdx, rbp
mov rcx, 0x6cfc5fd681c52056 
sbb rdx, rcx
mov r15, r12
mov r14, 0x2341f27177344 
sbb r15, r14
sbb r10, 0x00000000
mov r10, [ rsp + 0x5a8 ]
cmovc r10, rdi
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], r10
cmovc r15, r12
cmovc rdx, rbp
mov [ rdi + 0x28 ], rdx
cmovc r11, rax
mov rax, [ rsp + 0x590 ]
cmovc rax, r9
mov r9, [ rsp + 0x5b0 ]
cmovc r9, r8
mov [ rdi + 0x20 ], r11
mov [ rdi + 0x18 ], r9
mov [ rdi + 0x0 ], rax
mov r8, [ rsp + 0x598 ]
cmovc r8, r13
mov [ rdi + 0x30 ], r15
mov [ rdi + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1592
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4398
; seed 2660759037521995 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 53728 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=47, initial num_batches=31): 937 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.017439696247766527
; number reverted permutation / tried permutation: 277 / 479 =57.829%
; number reverted decision / tried decision: 294 / 520 =56.538%
; validated in 192.841s
