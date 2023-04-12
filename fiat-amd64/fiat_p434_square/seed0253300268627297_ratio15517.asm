SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1520
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r8
mulx r8, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], rbx
mulx rbx, rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r11
mulx r11, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], rbx
mulx rbx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r8
mulx r8, rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], rdi
mulx rdi, r8, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], rdi
mulx rdi, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r9
mov [ rsp + 0x58 ], r15
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], r9
mulx r9, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r15
mov [ rsp + 0x78 ], r14
mulx r14, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r15
mov [ rsp + 0x98 ], r14
mulx r14, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], r14
mov [ rsp + 0xb8 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r15
mov [ rsp + 0xc8 ], r14
mulx r14, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r15, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r15
mulx r15, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], r15
mov [ rsp + 0xe0 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], r15
mov [ rsp + 0xf0 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], rdi
mov [ rsp + 0x100 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x108 ], r13
mov [ rsp + 0x110 ], r8
mulx r8, r13, [ rsi + 0x8 ]
adox r11, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x118 ], r11
mulx r11, r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], r14
mulx r14, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r14
mov [ rsp + 0x138 ], r11
mulx r11, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r11
mov [ rsp + 0x148 ], r14
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r14
mov [ rsp + 0x158 ], r11
mulx r11, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], r8
mulx r8, r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r13
mov [ rsp + 0x178 ], r9
mulx r9, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x180 ], r9
mov [ rsp + 0x188 ], r13
mulx r13, r9, [ rsi + 0x10 ]
adcx r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], r14
mulx r14, r11, [ rsi + 0x0 ]
adcx r9, r8
setc dl
clc
adcx rdi, rcx
adox rax, rbx
mov cl, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, [ rsi + 0x10 ]
adox rbp, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x198 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
adcx r12, r15
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1a0 ], r10
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x110 ]
mov [ rsp + 0x1a8 ], r12
seto r12b
mov [ rsp + 0x1b0 ], rbp
mov rbp, -0x2 
inc rbp
adox rdx, [ rsp + 0x178 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], rax
mov [ rsp + 0x1c0 ], r9
mulx r9, rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c8 ], rbp
mov [ rsp + 0x1d0 ], r10
mulx r10, rbp, rdx
mov rdx, [ rsp + 0x108 ]
adcx rdx, [ rsp + 0x188 ]
adox rbx, [ rsp + 0xf0 ]
mov [ rsp + 0x1d8 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1e0 ], r15
mov byte [ rsp + 0x1e8 ], r12b
mulx r12, r15, [ rsi + 0x18 ]
adox rax, r8
mov rdx, [ rsp + 0x170 ]
seto r8b
mov [ rsp + 0x1f0 ], rbx
mov rbx, -0x2 
inc rbx
adox rdx, [ rsp + 0xa8 ]
seto bl
mov [ rsp + 0x1f8 ], rax
mov rax, 0x0 
dec rax
movzx rcx, cl
adox rcx, rax
adox r13, r15
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mulx rax, r15, [ rsi + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x200 ], rcx
mov [ rsp + 0x208 ], r13
mulx r13, rcx, rbp
setc dl
clc
adcx rdi, [ rsp + 0x78 ]
mov [ rsp + 0x210 ], rdi
mov rdi, [ rsp + 0x128 ]
mov [ rsp + 0x218 ], r13
seto r13b
mov [ rsp + 0x220 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox rdi, [ rsp + 0x168 ]
adcx r15, [ rsp + 0x58 ]
mov rbx, [ rsp + 0x120 ]
adox rbx, [ rsp + 0x158 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, rbp
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], rbx
mulx rbx, r15, rcx
seto cl
mov [ rsp + 0x238 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r13, r13b
adox r13, rdi
adox r12, [ rsp + 0x68 ]
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x240 ], r12
mulx r12, rdi, r13
mov r13, rdi
mov [ rsp + 0x248 ], rbx
seto bl
mov byte [ rsp + 0x250 ], cl
mov rcx, -0x2 
inc rcx
adox r13, r12
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x258 ], bl
mov [ rsp + 0x260 ], r15
mulx r15, rbx, [ rsi + 0x30 ]
adcx rax, [ rsp + 0x88 ]
adcx rbx, [ rsp + 0x80 ]
mov rdx, rdi
mov [ rsp + 0x268 ], rbx
setc bl
clc
adcx rdx, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x270 ], rax
mov [ rsp + 0x278 ], r15
mulx r15, rax, [ rsi + 0x20 ]
setc dl
clc
mov [ rsp + 0x280 ], r15
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r9, [ rsp + 0x50 ]
seto r8b
inc r15
adox r11, r10
mov r10b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x288 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x18 ]
adcx rdx, [ rsp + 0x48 ]
adox r14, [ rsp + 0x98 ]
mov [ rsp + 0x290 ], rdx
seto dl
mov [ rsp + 0x298 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r10, r10b
adox r10, r9
adox r11, r13
mov r13b, dl
mov rdx, [ rsi + 0x30 ]
mulx r9, r10, [ rsi + 0x28 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2a0 ], r11
mov [ rsp + 0x2a8 ], r14
mulx r14, r11, rcx
mov rdx, r12
mov byte [ rsp + 0x2b0 ], bl
setc bl
clc
mov [ rsp + 0x2b8 ], r9
mov r9, -0x1 
movzx r8, r8b
adcx r8, r9
adcx rdx, rdi
adcx r11, r12
mov rdi, [ rsp + 0x180 ]
setc r12b
clc
movzx rbp, bpl
adcx rbp, r9
adcx rdi, [ rsp + 0x10 ]
seto bpl
inc r9
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox r15, [ rsp + 0x90 ]
setc r13b
clc
movzx r12, r12b
adcx r12, r8
adcx r14, [ rsp + 0x260 ]
setc r12b
movzx r9, byte [ rsp + 0x1e8 ]
clc
adcx r9, r8
adcx rax, [ rsp + 0x8 ]
mov r9, [ rsp + 0x28 ]
setc r8b
clc
mov [ rsp + 0x2c0 ], rdi
mov rdi, -0x1 
movzx r13, r13b
adcx r13, rdi
adcx r9, [ rsp + 0x0 ]
adcx r10, [ rsp + 0x20 ]
mov r13, 0x2341f27177344 
xchg rdx, r13
mov [ rsp + 0x2c8 ], r10
mulx r10, rdi, rcx
mov rcx, [ rsp + 0x150 ]
seto dl
mov [ rsp + 0x2d0 ], r9
movzx r9, byte [ rsp + 0x250 ]
mov [ rsp + 0x2d8 ], rax
mov rax, -0x1 
inc rax
mov rax, -0x1 
adox r9, rax
adox rcx, [ rsp - 0x18 ]
mov r9, [ rsp - 0x20 ]
adox r9, [ rsp + 0x1e0 ]
mov rax, [ rsp + 0x2b8 ]
mov [ rsp + 0x2e0 ], r9
mov r9, 0x0 
adcx rax, r9
mov r9, [ rsp + 0x220 ]
clc
mov [ rsp + 0x2e8 ], rax
mov rax, -0x1 
movzx r12, r12b
adcx r12, rax
adcx r9, [ rsp + 0x248 ]
mov r12, [ rsp + 0x1d0 ]
adox r12, [ rsp + 0x138 ]
adcx rdi, [ rsp + 0x218 ]
mov rax, [ rsp + 0xc8 ]
mov [ rsp + 0x2f0 ], r12
seto r12b
mov [ rsp + 0x2f8 ], rcx
movzx rcx, byte [ rsp + 0x2b0 ]
mov [ rsp + 0x300 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox rcx, rdi
adox rax, [ rsp + 0x278 ]
setc cl
clc
movzx rbp, bpl
adcx rbp, rdi
adcx r13, [ rsp + 0x2a8 ]
mov rbp, [ rsp - 0x8 ]
seto dil
mov [ rsp + 0x308 ], rax
movzx rax, byte [ rsp + 0x258 ]
mov [ rsp + 0x310 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox rax, r9
adox rbp, [ rsp + 0x60 ]
mov rax, [ rsp - 0x10 ]
adox rax, [ rsp + 0x100 ]
mov r9, [ rsp + 0x160 ]
mov [ rsp + 0x318 ], rax
setc al
clc
adcx r9, [ rsp + 0x2a0 ]
mov [ rsp + 0x320 ], rbp
movzx rbp, r12b
mov [ rsp + 0x328 ], r14
mov r14, [ rsp + 0x130 ]
lea rbp, [ rbp + r14 ]
mov r14, [ rsp + 0xb8 ]
setc r12b
clc
mov [ rsp + 0x330 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx r14, [ rsp + 0x280 ]
mov r8, [ rsp - 0x28 ]
seto bpl
mov [ rsp + 0x338 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rdx, dl
adox rdx, r14
adox r8, [ rsp + 0x298 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x340 ], r8
mulx r8, r14, r9
mov rdx, [ rsp + 0xe0 ]
adox rdx, [ rsp - 0x30 ]
mov [ rsp + 0x348 ], r8
mov r8, [ rsp + 0x40 ]
mov [ rsp + 0x350 ], r14
seto r14b
mov [ rsp + 0x358 ], rdx
mov rdx, 0x0 
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r8, [ rsp - 0x38 ]
mov rbx, [ rsp + 0xd8 ]
setc dl
clc
mov [ rsp + 0x360 ], r8
mov r8, -0x1 
movzx r14, r14b
adcx r14, r8
adcx rbx, [ rsp + 0x148 ]
mov r14, [ rsp + 0x140 ]
mov r8, 0x0 
adcx r14, r8
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r9
mov byte [ rsp + 0x368 ], r9b
mov [ rsp + 0x370 ], r14
mulx r14, r9, r8
mov r8, [ rsp + 0xc0 ]
clc
mov [ rsp + 0x378 ], r14
mov r14, -0x1 
movzx rdi, dil
adcx rdi, r14
adcx r8, [ rsp + 0x38 ]
movzx rdi, bpl
mov r14, [ rsp + 0xf8 ]
lea rdi, [ rdi + r14 ]
mov r14, [ rsp - 0x40 ]
mov rbp, 0x0 
adox r14, rbp
mov rbp, 0x7bc65c783158aea3 
mov [ rsp + 0x380 ], r8
mov [ rsp + 0x388 ], r14
mulx r14, r8, rbp
mov rbp, [ rsp + 0x30 ]
adc rbp, 0x0
add r12b, 0x7F
adox r13, [ rsp + 0x190 ]
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx r15, r11
mov r11, 0xffffffffffffffff 
mulx r12, rax, r11
mov r11, rax
mov [ rsp + 0x390 ], rbp
setc bpl
clc
adcx r11, r12
adox r15, [ rsp + 0x1c0 ]
mov [ rsp + 0x398 ], r15
movzx r15, cl
lea r15, [ r15 + r10 ]
mov r10, [ rsp + 0x340 ]
seto cl
mov [ rsp + 0x3a0 ], rdi
mov rdi, 0x0 
dec rdi
movzx rbp, bpl
adox rbp, rdi
adox r10, [ rsp + 0x328 ]
mov rbp, rax
adcx rbp, r12
mov rdi, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3a8 ], rbp
mov [ rsp + 0x3b0 ], r11
mulx r11, rbp, rdi
mov rdi, [ rsp + 0x310 ]
adox rdi, [ rsp + 0x358 ]
adox rbx, [ rsp + 0x300 ]
adcx rbp, r12
adcx r8, r11
adcx r9, r14
mov r14, [ rsp + 0x378 ]
adcx r14, [ rsp + 0x350 ]
setc r12b
clc
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx r10, [ rsp + 0x208 ]
adox r15, [ rsp + 0x370 ]
movzx rcx, r12b
mov r11, [ rsp + 0x348 ]
lea rcx, [ rcx + r11 ]
adcx rdi, [ rsp + 0x240 ]
adcx rbx, [ rsp + 0x320 ]
movzx r11, byte [ rsp + 0x368 ]
mov r12, [ rsp + 0xb0 ]
lea r11, [ r11 + r12 ]
setc r12b
clc
adcx rax, rdx
adcx r13, [ rsp + 0x3b0 ]
setc al
clc
mov rdx, -0x1 
movzx r12, r12b
adcx r12, rdx
adcx r15, [ rsp + 0x318 ]
seto r12b
movzx r12, r12b
adcx r12, [ rsp + 0x3a0 ]
mov rdx, [ rsp + 0x3a8 ]
mov [ rsp + 0x3b8 ], r11
mov r11, 0x0 
dec r11
movzx rax, al
adox rax, r11
adox rdx, [ rsp + 0x398 ]
setc al
clc
adcx r13, [ rsp + 0xa0 ]
mov r11, 0x7bc65c783158aea3 
xchg rdx, r13
mov byte [ rsp + 0x3c0 ], al
mov [ rsp + 0x3c8 ], rcx
mulx rcx, rax, r11
adcx r13, [ rsp + 0x200 ]
mov r11, 0x6cfc5fd681c52056 
mov [ rsp + 0x3d0 ], rcx
mov [ rsp + 0x3d8 ], rax
mulx rax, rcx, r11
adox rbp, r10
adox r8, rdi
mov r10, 0x2341f27177344 
mulx r11, rdi, r10
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3e0 ], r11
mov [ rsp + 0x3e8 ], rdi
mulx rdi, r11, r10
adox r9, rbx
adox r14, r15
adcx rbp, [ rsp + 0x238 ]
mov rbx, 0xffffffffffffffff 
mulx r10, r15, rbx
adcx r8, [ rsp + 0x230 ]
mov rbx, r15
mov [ rsp + 0x3f0 ], r8
setc r8b
clc
adcx rbx, r10
mov [ rsp + 0x3f8 ], rbp
mov rbp, r15
mov [ rsp + 0x400 ], rax
setc al
clc
adcx rbp, rdx
adox r12, [ rsp + 0x3c8 ]
adcx rbx, r13
movzx rbp, byte [ rsp + 0x3c0 ]
mov rdx, 0x0 
adox rbp, rdx
mov r13, r10
dec rdx
movzx rax, al
adox rax, rdx
adox r13, r15
adox r11, r10
seto r15b
inc rdx
mov r10, -0x1 
movzx r8, r8b
adox r8, r10
adox r9, [ rsp + 0x2f8 ]
setc r8b
clc
movzx r15, r15b
adcx r15, r10
adcx rdi, [ rsp + 0x3d8 ]
adcx rcx, [ rsp + 0x3d0 ]
adox r14, [ rsp + 0x2e0 ]
mov rax, [ rsp + 0x400 ]
adcx rax, [ rsp + 0x3e8 ]
setc r15b
clc
adcx rbx, [ rsp + 0xe8 ]
movzx rdx, r15b
mov r10, [ rsp + 0x3e0 ]
lea rdx, [ rdx + r10 ]
setc r10b
clc
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r13, [ rsp + 0x3f8 ]
adcx r11, [ rsp + 0x3f0 ]
adcx rdi, r9
adcx rcx, r14
adox r12, [ rsp + 0x2f0 ]
mov r8, 0x2341f27177344 
xchg rdx, rbx
mulx r14, r9, r8
adox rbp, [ rsp + 0x330 ]
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x408 ], r14
mulx r14, r8, r15
mov r15, 0x7bc65c783158aea3 
mov [ rsp + 0x410 ], r9
mov [ rsp + 0x418 ], rbx
mulx rbx, r9, r15
mov r15, r8
mov [ rsp + 0x420 ], rbx
seto bl
mov [ rsp + 0x428 ], r9
mov r9, -0x2 
inc r9
adox r15, r14
setc r9b
clc
mov byte [ rsp + 0x430 ], bl
mov rbx, -0x1 
movzx r10, r10b
adcx r10, rbx
adcx r13, [ rsp + 0x1c8 ]
mov r10, r8
adox r10, r14
adcx r11, [ rsp + 0x1d8 ]
mov rbx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x438 ], r10
mov [ rsp + 0x440 ], r11
mulx r11, r10, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x448 ], r11
mov [ rsp + 0x450 ], r10
mulx r10, r11, rbx
adcx rdi, [ rsp + 0x1f8 ]
seto bl
mov [ rsp + 0x458 ], rdi
mov rdi, -0x2 
inc rdi
adox r8, rdx
adcx rcx, [ rsp + 0x288 ]
adox r15, r13
seto r8b
inc rdi
adox r15, [ rsp + 0x70 ]
seto dl
dec rdi
movzx r9, r9b
adox r9, rdi
adox r12, rax
mov rax, 0xffffffffffffffff 
xchg rdx, r15
mulx r13, r9, rax
mov rdi, 0x6cfc5fd681c52056 
mov [ rsp + 0x460 ], rcx
mulx rcx, rax, rdi
adcx r12, [ rsp + 0x290 ]
adox rbp, [ rsp + 0x418 ]
mov rdi, 0x7bc65c783158aea3 
mov [ rsp + 0x468 ], rcx
mov [ rsp + 0x470 ], rax
mulx rax, rcx, rdi
seto dil
mov [ rsp + 0x478 ], rax
mov rax, -0x1 
inc rax
mov rax, -0x1 
movzx rbx, bl
adox rbx, rax
adox r14, [ rsp + 0x450 ]
mov rbx, [ rsp + 0x448 ]
adox rbx, [ rsp + 0x428 ]
mov rax, r9
mov [ rsp + 0x480 ], rcx
setc cl
clc
adcx rax, r13
mov [ rsp + 0x488 ], rax
mov rax, r9
adcx rax, r13
adox r11, [ rsp + 0x420 ]
adox r10, [ rsp + 0x410 ]
mov [ rsp + 0x490 ], rax
movzx rax, dil
mov [ rsp + 0x498 ], r10
movzx r10, byte [ rsp + 0x430 ]
lea rax, [ rax + r10 ]
setc r10b
clc
mov rdi, -0x1 
movzx rcx, cl
adcx rcx, rdi
adcx rbp, [ rsp + 0x360 ]
mov rcx, [ rsp + 0x440 ]
seto dil
mov [ rsp + 0x4a0 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox rcx, [ rsp + 0x438 ]
adcx rax, [ rsp + 0x388 ]
setc r8b
clc
movzx r15, r15b
adcx r15, rbp
adcx rcx, [ rsp + 0xd0 ]
adox r14, [ rsp + 0x458 ]
adcx r14, [ rsp + 0x118 ]
adox rbx, [ rsp + 0x460 ]
adox r11, r12
adcx rbx, [ rsp + 0x1b8 ]
seto r15b
inc rbp
adox r9, rdx
mov r9, 0x2341f27177344 
mulx rbp, r12, r9
adox rcx, [ rsp + 0x488 ]
seto r9b
mov [ rsp + 0x4a8 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, [ rsp - 0x48 ]
mov rbp, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x4b0 ], r8b
mov [ rsp + 0x4b8 ], rax
mulx rax, r8, rbp
seto dl
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox r13, r8
adox rax, [ rsp + 0x480 ]
adcx r11, [ rsp + 0x1b0 ]
mov r10, [ rsp + 0x478 ]
adox r10, [ rsp + 0x470 ]
adox r12, [ rsp + 0x468 ]
mov r8, [ rsp + 0x498 ]
seto bpl
mov [ rsp + 0x4c0 ], r12
mov r12, 0x0 
dec r12
movzx r15, r15b
adox r15, r12
adox r8, [ rsp + 0x4a0 ]
adcx r8, [ rsp + 0x2d8 ]
movzx r15, dil
mov r12, [ rsp + 0x408 ]
lea r15, [ r15 + r12 ]
seto r12b
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r14, [ rsp + 0x490 ]
adox r13, rbx
mov rbx, 0x2341f27177344 
xchg rdx, rbx
mulx rdi, r9, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x4c8 ], rdi
mov byte [ rsp + 0x4d0 ], bpl
mulx rbp, rdi, rcx
adox rax, r11
mov r11, 0x7bc65c783158aea3 
mov rdx, r11
mov [ rsp + 0x4d8 ], rax
mulx rax, r11, rcx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4e0 ], r13
mov [ rsp + 0x4e8 ], r10
mulx r10, r13, rcx
seto dl
mov [ rsp + 0x4f0 ], r8
mov r8, 0x0 
dec r8
movzx r12, r12b
adox r12, r8
adox r15, [ rsp + 0x4b8 ]
mov r12, rdi
seto r8b
mov byte [ rsp + 0x4f8 ], dl
mov rdx, -0x2 
inc rdx
adox r12, rbp
adcx r15, [ rsp + 0x338 ]
movzx rdx, r8b
mov [ rsp + 0x500 ], r12
movzx r12, byte [ rsp + 0x4b0 ]
lea rdx, [ rdx + r12 ]
mov r12, rdi
adox r12, rbp
adox r13, rbp
adcx rdx, [ rsp + 0x3b8 ]
setc bpl
clc
mov r8, -0x1 
movzx rbx, bl
adcx rbx, r8
adcx r14, [ rsp + 0x198 ]
setc bl
clc
adcx rdi, rcx
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov byte [ rsp + 0x508 ], bpl
mulx rbp, r8, rdi
adox r11, r10
adox r8, rax
adox r9, rbp
mov rdx, [ rsp + 0x4f0 ]
seto al
movzx r10, byte [ rsp + 0x4f8 ]
mov rbp, 0x0 
dec rbp
adox r10, rbp
adox rdx, [ rsp + 0x4e8 ]
adox r15, [ rsp + 0x4c0 ]
mov r10, [ rsp + 0x4e0 ]
seto bpl
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rbx, bl
adox rbx, rdi
adox r10, [ rsp + 0x1a8 ]
mov rbx, [ rsp + 0x4d8 ]
adox rbx, [ rsp + 0x1f0 ]
adcx r14, [ rsp + 0x500 ]
movzx rdi, byte [ rsp + 0x4d0 ]
mov byte [ rsp + 0x510 ], al
mov rax, [ rsp + 0x4a8 ]
lea rdi, [ rdi + rax ]
adox rdx, [ rsp + 0x2c0 ]
adcx r12, r10
adcx r13, rbx
adcx r11, rdx
setc al
clc
mov r10, -0x1 
movzx rbp, bpl
adcx rbp, r10
adcx rcx, rdi
setc bpl
clc
adcx r14, [ rsp + 0x1a0 ]
movzx rbx, bpl
movzx rdi, byte [ rsp + 0x508 ]
lea rbx, [ rbx + rdi ]
adcx r12, [ rsp + 0x210 ]
mov rdi, 0x6cfc5fd681c52056 
mov rdx, r14
mulx rbp, r14, rdi
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x518 ], rbp
mulx rbp, rdi, r10
adox r15, [ rsp + 0x2d0 ]
mov r10, rdi
mov [ rsp + 0x520 ], r11
setc r11b
clc
adcx r10, rdx
setc r10b
clc
mov [ rsp + 0x528 ], r12
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r13, [ rsp + 0x228 ]
adox rcx, [ rsp + 0x2c8 ]
setc r11b
clc
movzx rax, al
adcx rax, r12
adcx r15, r8
adox rbx, [ rsp + 0x2e8 ]
mov r8, 0x2341f27177344 
mulx r12, rax, r8
adcx r9, rcx
mov rcx, rdi
seto r8b
mov [ rsp + 0x530 ], r12
mov r12, -0x2 
inc r12
adox rcx, rbp
adox rdi, rbp
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x538 ], rax
mov [ rsp + 0x540 ], r9
mulx r9, rax, r12
mov r12, 0x7bc65c783158aea3 
mov [ rsp + 0x548 ], rdi
mov [ rsp + 0x550 ], r13
mulx r13, rdi, r12
movzx rdx, byte [ rsp + 0x510 ]
mov r12, [ rsp + 0x4c8 ]
lea rdx, [ rdx + r12 ]
adox rax, rbp
adox rdi, r9
adox r14, r13
adcx rdx, rbx
seto r12b
mov rbp, -0x1 
inc rbp
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rcx, [ rsp + 0x528 ]
movzx r10, r8b
adcx r10, rbp
mov r8, [ rsp + 0x520 ]
clc
movzx r11, r11b
adcx r11, rbx
adcx r8, [ rsp + 0x270 ]
adcx r15, [ rsp + 0x268 ]
mov r11, [ rsp + 0x550 ]
adox r11, [ rsp + 0x548 ]
mov r9, [ rsp + 0x308 ]
adcx r9, [ rsp + 0x540 ]
adox rax, r8
adox rdi, r15
adox r14, r9
adcx rdx, [ rsp + 0x380 ]
setc r13b
seto r8b
mov r15, rcx
mov r9, 0xffffffffffffffff 
sub r15, r9
mov rbp, r11
sbb rbp, r9
inc rbx
mov rbx, -0x1 
movzx r13, r13b
adox r13, rbx
adox r10, [ rsp + 0x390 ]
seto r13b
mov rbx, rax
sbb rbx, r9
mov r9, rdi
mov [ rsp + 0x558 ], rbx
mov rbx, 0xfdc1767ae2ffffff 
sbb r9, rbx
mov rbx, [ rsp + 0x518 ]
mov [ rsp + 0x560 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r12, r12b
adox r12, r9
adox rbx, [ rsp + 0x538 ]
mov r12, [ rsp + 0x530 ]
mov r9, 0x0 
adox r12, r9
dec r9
movzx r8, r8b
adox r8, r9
adox rdx, rbx
adox r12, r10
seto r8b
mov r10, r14
mov rbx, 0x7bc65c783158aea3 
sbb r10, rbx
mov r9, rdx
mov rbx, 0x6cfc5fd681c52056 
sbb r9, rbx
mov rbx, r12
mov [ rsp + 0x568 ], r9
mov r9, 0x2341f27177344 
sbb rbx, r9
movzx r9, r8b
movzx r13, r13b
lea r9, [ r9 + r13 ]
sbb r9, 0x00000000
cmovc r10, r14
cmovc r15, rcx
cmovc rbp, r11
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r15
mov rcx, [ rsp + 0x558 ]
cmovc rcx, rax
mov [ r9 + 0x10 ], rcx
cmovc rbx, r12
mov [ r9 + 0x30 ], rbx
mov r11, [ rsp + 0x568 ]
cmovc r11, rdx
mov [ r9 + 0x28 ], r11
mov [ r9 + 0x8 ], rbp
mov [ r9 + 0x20 ], r10
mov rax, [ rsp + 0x560 ]
cmovc rax, rdi
mov [ r9 + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1520
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.5517
; seed 0253300268627297 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56520 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=41, initial num_batches=31): 961 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.017002830856334042
; number reverted permutation / tried permutation: 320 / 513 =62.378%
; number reverted decision / tried decision: 283 / 486 =58.230%
; validated in 208.503s
