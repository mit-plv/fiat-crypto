SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1568
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rdi
mulx rdi, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r8
mulx r8, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r8
mov [ rsp + 0x20 ], rdi
mulx rdi, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r11
mulx r11, r10, [ rax + 0x20 ]
test al, al
adox r8, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x38 ], r11
mulx r11, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r10
mov [ rsp + 0x48 ], r11
mulx r11, r10, [ rax + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], r11
mulx r11, r12, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r10
mov [ rsp + 0x68 ], r14
mulx r14, r10, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x70 ], r10
mov [ rsp + 0x78 ], r14
mulx r14, r10, rbp
mov rdx, r10
adcx rdx, rbp
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], rbx
mov [ rsp + 0x98 ], rcx
mulx rcx, rbx, [ rax + 0x30 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], rbx
mulx rbx, rcx, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb0 ], rbx
mov [ rsp + 0xb8 ], rcx
mulx rcx, rbx, [ rsi + 0x10 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xc0 ], rcx
mov [ rsp + 0xc8 ], rbx
mulx rbx, rcx, rbp
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], r9
mulx r9, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd8 ], r9
mov [ rsp + 0xe0 ], rbp
mulx rbp, r9, [ rsi + 0x30 ]
mov rdx, r10
mov [ rsp + 0xe8 ], rbp
seto bpl
mov [ rsp + 0xf0 ], r9
mov r9, -0x2 
inc r9
adox rdx, r14
mov r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xf8 ], rdi
mov byte [ rsp + 0x100 ], bpl
mulx rbp, rdi, [ rsi + 0x28 ]
adcx r9, r8
setc dl
clc
adcx r13, r9
mov r8, 0x7bc65c783158aea3 
xchg rdx, r13
mov [ rsp + 0x108 ], rbp
mulx rbp, r9, r8
mov r8, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x110 ], r13b
mov [ rsp + 0x118 ], rdi
mulx rdi, r13, r8
mov r8, 0x6cfc5fd681c52056 
mov [ rsp + 0x120 ], rbp
mov [ rsp + 0x128 ], r9
mulx r9, rbp, r8
adox r10, r14
adox rcx, r14
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x130 ], r9
mulx r9, r8, [ rax + 0x10 ]
adox r12, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x138 ], r12
mulx r12, rbx, r14
adox r15, r11
mov r11, rbx
setc dl
clc
adcx r11, r12
mov [ rsp + 0x140 ], r11
mov r11, rbx
mov byte [ rsp + 0x148 ], dl
setc dl
clc
adcx r11, r14
mov r11, r12
mov [ rsp + 0x150 ], r15
setc r15b
clc
mov [ rsp + 0x158 ], rcx
mov rcx, -0x1 
movzx rdx, dl
adcx rdx, rcx
adcx r11, rbx
mov rdx, [ rax + 0x20 ]
mulx rcx, rbx, [ rsi + 0x0 ]
adcx r13, r12
seto dl
movzx r12, byte [ rsp + 0x100 ]
mov [ rsp + 0x160 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox r12, r13
adox r8, [ rsp + 0xf8 ]
adox r9, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0x128 ]
adcx rbp, [ rsp + 0x120 ]
adox rbx, [ rsp + 0x88 ]
mov r12, [ rsp + 0x80 ]
setc r13b
clc
adcx r12, [ rsp + 0x118 ]
mov [ rsp + 0x168 ], r12
setc r12b
mov [ rsp + 0x170 ], rbp
movzx rbp, byte [ rsp + 0x110 ]
clc
mov byte [ rsp + 0x178 ], r13b
mov r13, -0x1 
adcx rbp, r13
adcx r8, r10
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, [ rax + 0x18 ]
adcx r9, [ rsp + 0x158 ]
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x180 ], r12b
mov byte [ rsp + 0x188 ], bpl
mulx rbp, r12, [ rsi + 0x8 ]
adcx rbx, [ rsp + 0x138 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x190 ], rdi
mov [ rsp + 0x198 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
adox rdi, rcx
adcx rdi, [ rsp + 0x150 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x1a0 ], r11
mulx r11, rcx, [ rsi + 0x8 ]
seto dl
mov byte [ rsp + 0x1a8 ], r15b
mov r15, -0x2 
inc r15
adox rcx, [ rsp + 0x68 ]
mov r15b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1b0 ], rdi
mov [ rsp + 0x1b8 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
adox r12, r11
adox r10, rbp
adox r13, [ rsp + 0x30 ]
setc dl
movzx rbp, byte [ rsp + 0x148 ]
clc
mov r11, -0x1 
adcx rbp, r11
adcx r8, rcx
adcx r12, r9
adcx r10, [ rsp + 0x1b8 ]
mov rbp, [ rsp + 0x28 ]
adox rbp, [ rsp + 0x98 ]
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x8 ]
adcx r13, [ rsp + 0x1b0 ]
mov rdx, [ rsp + 0x20 ]
adox rdx, [ rsp + 0x90 ]
mov [ rsp + 0x1c0 ], rdx
seto dl
mov [ rsp + 0x1c8 ], rbp
movzx rbp, byte [ rsp + 0x1a8 ]
mov byte [ rsp + 0x1d0 ], r9b
mov r9, 0x0 
dec r9
adox rbp, r9
adox r8, [ rsp + 0x140 ]
setc bpl
clc
adcx r8, [ rsp + 0xc8 ]
movzx r9, dl
mov byte [ rsp + 0x1d8 ], bpl
mov rbp, [ rsp + 0x18 ]
lea r9, [ r9 + rbp ]
adox r12, [ rsp + 0x198 ]
adox r10, [ rsp + 0x160 ]
adox r13, [ rsp + 0x190 ]
mov rbp, [ rsp + 0x10 ]
setc dl
clc
adcx rbp, [ rsp + 0xc0 ]
adcx rdi, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0x60 ]
mov [ rsp + 0x1e0 ], r9
seto r9b
mov byte [ rsp + 0x1e8 ], r15b
mov r15, 0x0 
dec r15
movzx rdx, dl
adox rdx, r15
adox r12, rbp
adox rdi, r10
seto dl
inc r15
adox rcx, [ rsp + 0x78 ]
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r8
mulx r15, rbp, r10
adox r11, [ rsp - 0x10 ]
mov r10, [ rsp + 0x58 ]
adcx r10, [ rsp + 0x50 ]
mov [ rsp + 0x1f0 ], r10
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1f8 ], r11
mov byte [ rsp + 0x200 ], r9b
mulx r9, r11, r10
seto r10b
mov [ rsp + 0x208 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r8, r8b
adox r8, r15
adox r13, rbx
mov rbx, 0xffffffffffffffff 
mulx r15, r8, rbx
mov rbx, r8
mov [ rsp + 0x210 ], rbp
setc bpl
clc
adcx rbx, rdx
mov rbx, r8
mov [ rsp + 0x218 ], r9
setc r9b
clc
adcx rbx, r15
adcx r8, r15
adcx r11, r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x220 ], r11
mov [ rsp + 0x228 ], r13
mulx r13, r11, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x230 ], r13
mov byte [ rsp + 0x238 ], r10b
mulx r10, r13, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x240 ], r10
movzx r10, byte [ rsp + 0x1e8 ]
mov [ rsp + 0x248 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox r10, r11
adox r13, [ rsp + 0x1a0 ]
setc r10b
clc
movzx r9, r9b
adcx r9, r11
adcx r12, rbx
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mulx r11, rbx, [ rax + 0x28 ]
adcx r8, rdi
setc dl
clc
adcx r12, [ rsp + 0x70 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r12
mov byte [ rsp + 0x250 ], r9b
mov byte [ rsp + 0x258 ], r10b
mulx r10, r9, rdi
mov rdi, 0xffffffffffffffff 
mov byte [ rsp + 0x260 ], r12b
mov [ rsp + 0x268 ], r10
mulx r10, r12, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x270 ], r13
mov [ rsp + 0x278 ], r9
mulx r9, r13, [ rax + 0x18 ]
setc dl
clc
mov [ rsp + 0x280 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rbx, [ rsp + 0x48 ]
seto bpl
inc r9
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox r8, rcx
adcx r11, [ rsp + 0x248 ]
mov rcx, r12
setc dl
clc
adcx rcx, r10
mov r9, r12
adcx r9, r10
adcx r10, [ rsp + 0x278 ]
mov [ rsp + 0x288 ], r10
movzx r10, bpl
mov byte [ rsp + 0x290 ], dl
mov rdx, [ rsp + 0x240 ]
lea r10, [ r10 + rdx ]
seto dl
mov rbp, -0x2 
inc rbp
adox r12, rdi
adox rcx, r8
setc r12b
clc
adcx rcx, [ rsp + 0x0 ]
setc r8b
movzx rbp, byte [ rsp + 0x238 ]
clc
mov [ rsp + 0x298 ], r11
mov r11, -0x1 
adcx rbp, r11
adcx r13, [ rsp - 0x18 ]
mov rbp, 0x7bc65c783158aea3 
xchg rdx, rcx
mov [ rsp + 0x2a0 ], r13
mulx r13, r11, rbp
mov rbp, [ rsp - 0x20 ]
mov byte [ rsp + 0x2a8 ], r8b
seto r8b
mov [ rsp + 0x2b0 ], rbx
movzx rbx, byte [ rsp + 0x188 ]
mov [ rsp + 0x2b8 ], r13
mov r13, 0x0 
dec r13
adox rbx, r13
adox rbp, [ rsp + 0xb8 ]
mov rbx, 0x2341f27177344 
mov [ rsp + 0x2c0 ], r9
mulx r9, r13, rbx
mov rbx, 0xffffffffffffffff 
mov [ rsp + 0x2c8 ], r9
mov [ rsp + 0x2d0 ], r13
mulx r13, r9, rbx
mov rbx, r9
mov byte [ rsp + 0x2d8 ], r8b
seto r8b
mov byte [ rsp + 0x2e0 ], cl
mov rcx, -0x2 
inc rcx
adox rbx, rdx
movzx rbx, r8b
mov rcx, [ rsp + 0xb0 ]
lea rbx, [ rbx + rcx ]
seto cl
movzx r8, byte [ rsp + 0x1d0 ]
mov [ rsp + 0x2e8 ], r11
mov r11, 0x0 
dec r11
adox r8, r11
adox rbp, [ rsp + 0x270 ]
mov r8, r9
setc r11b
clc
adcx r8, r13
adox rbx, r10
mov r10, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x2f0 ], r11b
mov [ rsp + 0x2f8 ], r8
mulx r8, r11, r10
adcx r9, r13
mov r10, 0x7bc65c783158aea3 
xchg rdx, rdi
mov [ rsp + 0x300 ], r9
mov byte [ rsp + 0x308 ], cl
mulx rcx, r9, r10
adcx r11, r13
setc r13b
movzx r10, byte [ rsp + 0x1d8 ]
clc
mov [ rsp + 0x310 ], r11
mov r11, -0x1 
adcx r10, r11
adcx rbp, [ rsp + 0x1c8 ]
seto r10b
inc r11
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox r9, [ rsp + 0x268 ]
adcx rbx, [ rsp + 0x1c0 ]
seto r12b
inc r11
mov r11, -0x1 
movzx r13, r13b
adox r13, r11
adox r8, [ rsp + 0x2e8 ]
mov r13, 0x2341f27177344 
xchg rdx, r13
mov [ rsp + 0x318 ], r8
mulx r8, r11, r14
mov r14, 0x7bc65c783158aea3 
mov rdx, r15
mov [ rsp + 0x320 ], r9
mulx r9, r15, r14
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x328 ], r10b
mov [ rsp + 0x330 ], r8
mulx r8, r10, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x338 ], r8
movzx r8, byte [ rsp + 0x178 ]
mov [ rsp + 0x340 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r8, r10
adox r11, [ rsp + 0x130 ]
mov r8, [ rsp + 0x220 ]
seto r10b
mov byte [ rsp + 0x348 ], dl
movzx rdx, byte [ rsp + 0x260 ]
mov [ rsp + 0x350 ], r11
mov r11, 0x0 
dec r11
adox rdx, r11
adox r8, [ rsp + 0x228 ]
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x358 ], r10b
mulx r10, r11, r13
seto dl
mov [ rsp + 0x360 ], r8
movzx r8, byte [ rsp + 0x258 ]
mov [ rsp + 0x368 ], rbx
mov rbx, 0x0 
dec rbx
adox r8, rbx
adox r15, [ rsp + 0x218 ]
adox r9, [ rsp + 0x210 ]
mov r8, 0x2341f27177344 
xchg rdx, r8
mov [ rsp + 0x370 ], r9
mulx r9, rbx, r14
adox rbx, [ rsp + 0x208 ]
mov [ rsp + 0x378 ], rbx
mulx rbx, r14, r13
mov r13, 0x0 
adox r9, r13
dec r13
movzx r12, r12b
adox r12, r13
adox rcx, r11
setc r12b
movzx r11, byte [ rsp + 0x200 ]
clc
adcx r11, r13
adcx rbp, [ rsp + 0x170 ]
adox r14, r10
mov r11, [ rsp + 0x368 ]
adcx r11, [ rsp + 0x350 ]
mov r10, 0x0 
adox rbx, r10
mov r10, [ rsp + 0x360 ]
movzx r13, byte [ rsp + 0x2e0 ]
mov rdx, 0x0 
dec rdx
adox r13, rdx
adox r10, [ rsp + 0x1f8 ]
setc r13b
movzx rdx, byte [ rsp + 0x2d8 ]
clc
mov [ rsp + 0x380 ], rbx
mov rbx, -0x1 
adcx rdx, rbx
adcx r10, [ rsp + 0x2c0 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x388 ], r14
mulx r14, rbx, rdi
setc dil
movzx rdx, byte [ rsp + 0x250 ]
clc
mov [ rsp + 0x390 ], rcx
mov rcx, -0x1 
adcx rdx, rcx
adcx rbp, [ rsp + 0x1f0 ]
mov rdx, [ rsp + 0x340 ]
seto cl
mov byte [ rsp + 0x398 ], dil
mov rdi, -0x2 
inc rdi
adox rdx, [ rsp - 0x8 ]
seto dil
mov [ rsp + 0x3a0 ], r9
movzx r9, byte [ rsp + 0x348 ]
mov byte [ rsp + 0x3a8 ], cl
mov rcx, 0x0 
dec rcx
adox r9, rcx
adox rbx, [ rsp + 0x2b8 ]
adcx r11, [ rsp + 0x2b0 ]
setc r9b
movzx rcx, byte [ rsp + 0x2a8 ]
clc
mov [ rsp + 0x3b0 ], rbx
mov rbx, -0x1 
adcx rcx, rbx
adcx r10, rdx
setc cl
movzx rdx, byte [ rsp + 0x308 ]
clc
adcx rdx, rbx
adcx r10, [ rsp + 0x2f8 ]
seto dl
inc rbx
adox r10, [ rsp - 0x28 ]
setc bl
clc
mov byte [ rsp + 0x3b8 ], cl
mov rcx, -0x1 
movzx rdx, dl
adcx rdx, rcx
adcx r14, [ rsp + 0x2d0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x3c0 ], r14
mulx r14, rcx, r10
movzx rdx, byte [ rsp + 0x358 ]
mov [ rsp + 0x3c8 ], r14
mov r14, [ rsp + 0x330 ]
lea rdx, [ rdx + r14 ]
mov r14, rcx
mov byte [ rsp + 0x3d0 ], bl
seto bl
mov byte [ rsp + 0x3d8 ], dil
mov rdi, -0x2 
inc rdi
adox r14, r10
movzx r14, byte [ rsp + 0x328 ]
setc dil
clc
mov byte [ rsp + 0x3e0 ], bl
mov rbx, -0x1 
movzx r12, r12b
adcx r12, rbx
adcx r14, [ rsp + 0x1e0 ]
setc r12b
clc
movzx r13, r13b
adcx r13, rbx
adcx r14, rdx
setc r13b
clc
movzx r8, r8b
adcx r8, rbx
adcx rbp, r15
adcx r11, [ rsp + 0x370 ]
movzx r8, r13b
movzx r12, r12b
lea r8, [ r8 + r12 ]
setc r15b
movzx rdx, byte [ rsp + 0x3a8 ]
clc
adcx rdx, rbx
adcx rbp, [ rsp + 0x2a0 ]
setc dl
clc
movzx r9, r9b
adcx r9, rbx
adcx r14, [ rsp + 0x298 ]
movzx r9, byte [ rsp + 0x290 ]
mov r12, [ rsp + 0x230 ]
lea r9, [ r9 + r12 ]
adcx r9, r8
mov r12b, dl
mov rdx, [ rsi + 0x20 ]
mulx r8, r13, [ rax + 0x28 ]
seto dl
inc rbx
mov rbx, -0x1 
movzx r15, r15b
adox r15, rbx
adox r14, [ rsp + 0x378 ]
adox r9, [ rsp + 0x3a0 ]
mov r15b, dl
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x3e8 ], dil
mulx rdi, rbx, [ rsi + 0x18 ]
seto dl
adc dl, 0x0
movzx rdx, dl
mov byte [ rsp + 0x3f0 ], r15b
mov r15, [ rsp + 0x280 ]
add byte [ rsp + 0x2f0 ], 0xFF
adcx r15, [ rsp + 0x40 ]
adcx rbx, [ rsp + 0x38 ]
mov [ rsp + 0x3f8 ], r8
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x400 ], r13
mov [ rsp + 0x408 ], rbp
mulx rbp, r13, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x410 ], r8b
mov [ rsp + 0x418 ], r9
mulx r9, r8, [ rax + 0x18 ]
adcx r13, rdi
adc rbp, 0x0
add r12b, 0x7F
adox r11, r15
mov rdx, [ rax + 0x18 ]
mulx rdi, r12, [ rsi + 0x20 ]
adox rbx, r14
adox r13, [ rsp + 0x418 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r14, [ rax + 0x10 ]
mov rdx, [ rsp + 0x408 ]
mov [ rsp + 0x420 ], r9
movzx r9, byte [ rsp + 0x398 ]
mov [ rsp + 0x428 ], r8
mov r8, -0x1 
adcx r9, r8
adcx rdx, [ rsp + 0x288 ]
setc r9b
movzx r8, byte [ rsp + 0x3d8 ]
clc
mov [ rsp + 0x430 ], r13
mov r13, -0x1 
adcx r8, r13
adcx r14, [ rsp + 0x338 ]
adcx r12, r15
adcx rdi, [ rsp + 0xe0 ]
mov r8, [ rsp + 0x400 ]
adcx r8, [ rsp + 0xd8 ]
mov r15, [ rsp + 0x3f8 ]
adcx r15, [ rsp + 0xa8 ]
mov r13, [ rsp + 0xa0 ]
mov [ rsp + 0x438 ], r15
mov r15, 0x0 
adcx r13, r15
movzx r15, byte [ rsp + 0x3b8 ]
clc
mov [ rsp + 0x440 ], r13
mov r13, -0x1 
adcx r15, r13
adcx rdx, r14
movzx r15, byte [ rsp + 0x410 ]
adox r15, rbp
seto bpl
inc r13
mov r14, -0x1 
movzx r9, r9b
adox r9, r14
adox r11, [ rsp + 0x320 ]
adox rbx, [ rsp + 0x390 ]
mov r9, [ rsp + 0x430 ]
adox r9, [ rsp + 0x388 ]
seto r13b
movzx r14, byte [ rsp + 0x3d0 ]
mov byte [ rsp + 0x448 ], bpl
mov rbp, 0x0 
dec rbp
adox r14, rbp
adox rdx, [ rsp + 0x300 ]
adcx r12, r11
adox r12, [ rsp + 0x310 ]
adcx rdi, rbx
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mulx rbx, r11, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x450 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
adox rdi, [ rsp + 0x318 ]
adcx r8, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x458 ], r11
mulx r11, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x460 ], r11
mov [ rsp + 0x468 ], r9
mulx r9, r11, [ rax + 0x28 ]
adox r8, [ rsp + 0x3b0 ]
mov rdx, rcx
mov [ rsp + 0x470 ], r9
seto r9b
mov [ rsp + 0x478 ], r15
mov r15, -0x2 
inc r15
adox rdx, [ rsp + 0x3c8 ]
seto r15b
mov byte [ rsp + 0x480 ], r9b
movzx r9, byte [ rsp + 0x180 ]
mov byte [ rsp + 0x488 ], r13b
mov r13, 0x0 
dec r13
adox r9, r13
adox rbp, [ rsp + 0x108 ]
adox rbx, [ rsp + 0x428 ]
setc r9b
movzx r13, byte [ rsp + 0x3e0 ]
clc
mov byte [ rsp + 0x490 ], r15b
mov r15, -0x1 
adcx r13, r15
adcx r14, [ rsp + 0x168 ]
seto r13b
movzx r15, byte [ rsp + 0x3f0 ]
mov byte [ rsp + 0x498 ], r9b
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox r15, r9
adox r14, rdx
mov rdx, [ rax + 0x20 ]
mulx r9, r15, [ rsi + 0x28 ]
setc dl
clc
adcx r14, [ rsp - 0x30 ]
mov [ rsp + 0x4a0 ], r8
mov r8, 0x7bc65c783158aea3 
xchg rdx, r8
mov [ rsp + 0x4a8 ], rbx
mov [ rsp + 0x4b0 ], rdi
mulx rdi, rbx, r14
setc dl
clc
mov [ rsp + 0x4b8 ], rdi
mov rdi, -0x1 
movzx r8, r8b
adcx r8, rdi
adcx r12, rbp
mov bpl, dl
mov rdx, [ rsi + 0x30 ]
mulx rdi, r8, [ rax + 0x10 ]
mov rdx, [ rsp - 0x38 ]
mov [ rsp + 0x4c0 ], rbx
seto bl
mov byte [ rsp + 0x4c8 ], bpl
mov rbp, -0x2 
inc rbp
adox rdx, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
setc bpl
clc
mov [ rsp + 0x4d0 ], r8
mov r8, -0x1 
movzx r13, r13b
adcx r13, r8
adcx r15, [ rsp + 0x420 ]
adcx r11, r9
mov r13, 0x2341f27177344 
xchg rdx, r14
mulx r8, r9, r13
mov r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x4d8 ], r8
mov [ rsp + 0x4e0 ], r9
mulx r9, r8, [ rax + 0x18 ]
adox r8, rdi
mov rdx, [ rsp + 0x4b0 ]
seto dil
mov [ rsp + 0x4e8 ], r8
mov r8, 0x0 
dec r8
movzx rbp, bpl
adox rbp, r8
adox rdx, [ rsp + 0x4a8 ]
adox r15, [ rsp + 0x4a0 ]
mov rbp, [ rsp + 0x380 ]
seto r8b
mov [ rsp + 0x4f0 ], r15
movzx r15, byte [ rsp + 0x488 ]
mov [ rsp + 0x4f8 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r15, rdx
adox rbp, [ rsp + 0x478 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x500 ], r14
mulx r14, r15, [ rsi + 0x28 ]
adcx r15, [ rsp + 0x470 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x508 ], r15
mov [ rsp + 0x510 ], r11
mulx r11, r15, r13
mov rdx, 0x0 
adcx r14, rdx
movzx rdx, byte [ rsp + 0x498 ]
clc
mov [ rsp + 0x518 ], r11
mov r11, -0x1 
adcx rdx, r11
adcx rbp, [ rsp + 0x438 ]
movzx rdx, byte [ rsp + 0x448 ]
mov r11, 0x0 
adox rdx, r11
adcx rdx, [ rsp + 0x440 ]
movzx r11, byte [ rsp + 0x480 ]
mov [ rsp + 0x520 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r11, r14
adox rbp, [ rsp + 0x3c0 ]
setc r11b
movzx r14, byte [ rsp + 0x490 ]
clc
mov [ rsp + 0x528 ], rbp
mov rbp, -0x1 
adcx r14, rbp
adcx rcx, [ rsp + 0x3c8 ]
setc r14b
clc
movzx rdi, dil
adcx rdi, rbp
adcx r9, [ rsp + 0xf0 ]
mov rdi, [ rsp + 0xe8 ]
adcx rdi, [ rsp + 0x458 ]
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, r10
mov [ rsp + 0x530 ], rdi
mov [ rsp + 0x538 ], r9
mulx r9, rdi, rbp
mov rbp, 0x7bc65c783158aea3 
mov byte [ rsp + 0x540 ], r8b
mov [ rsp + 0x548 ], r9
mulx r9, r8, rbp
mov rbp, [ rsp + 0x450 ]
adcx rbp, [ rsp + 0x468 ]
mov [ rsp + 0x550 ], rbp
movzx rbp, byte [ rsp + 0x3e8 ]
mov [ rsp + 0x558 ], rdi
mov rdi, [ rsp + 0x2c8 ]
lea rbp, [ rbp + rdi ]
adox rbp, r10
movzx rdi, r11b
mov r10, 0x0 
adox rdi, r10
dec r10
movzx rbx, bl
adox rbx, r10
adox r12, rcx
mov rbx, 0xfdc1767ae2ffffff 
mulx rcx, r11, rbx
seto r10b
mov rbx, 0x0 
dec rbx
movzx r14, r14b
adox r14, rbx
adox r11, [ rsp + 0x3c8 ]
adox r8, rcx
mov r14, 0x2341f27177344 
mulx rbx, rcx, r14
adox r9, [ rsp + 0x558 ]
adox rcx, [ rsp + 0x548 ]
mov rdx, [ rsp + 0x460 ]
mov r14, 0x0 
adcx rdx, r14
mov r14, [ rsp + 0x528 ]
mov [ rsp + 0x560 ], rdx
movzx rdx, byte [ rsp + 0x540 ]
clc
mov [ rsp + 0x568 ], rbx
mov rbx, -0x1 
adcx rdx, rbx
adcx r14, [ rsp + 0x510 ]
adcx rbp, [ rsp + 0x508 ]
adcx rdi, [ rsp + 0x520 ]
setc dl
movzx rbx, byte [ rsp + 0x4c8 ]
clc
mov [ rsp + 0x570 ], rdi
mov rdi, -0x1 
adcx rbx, rdi
adcx r12, [ rsp + 0x500 ]
setc bl
clc
movzx r10, r10b
adcx r10, rdi
adcx r11, [ rsp + 0x4f8 ]
adcx r8, [ rsp + 0x4f0 ]
adcx r9, r14
setc r10b
clc
movzx rbx, bl
adcx rbx, rdi
adcx r11, [ rsp + 0x4d0 ]
adcx r8, [ rsp + 0x4e8 ]
adcx r9, [ rsp + 0x538 ]
seto r14b
inc rdi
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rbp, rcx
adcx rbp, [ rsp + 0x530 ]
mov rcx, r15
seto r10b
mov rbx, -0x3 
inc rbx
adox rcx, [ rsp + 0x518 ]
mov rdi, r15
adox rdi, [ rsp + 0x518 ]
setc bl
clc
adcx r15, r13
movzx r15, r14b
mov [ rsp + 0x578 ], rbp
mov rbp, [ rsp + 0x568 ]
lea r15, [ r15 + rbp ]
seto bpl
mov r14, 0x0 
dec r14
movzx r10, r10b
adox r10, r14
adox r15, [ rsp + 0x570 ]
adcx rcx, r12
adcx rdi, r11
mov r12, 0x6cfc5fd681c52056 
xchg rdx, r12
mulx r10, r11, r13
movzx r14, r12b
mov rdx, 0x0 
adox r14, rdx
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r15, [ rsp + 0x550 ]
mov r12, 0xfdc1767ae2ffffff 
mov rdx, r12
mulx rbx, r12, r13
setc r13b
clc
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx r12, [ rsp + 0x518 ]
adcx rbx, [ rsp + 0x4c0 ]
seto bpl
inc rdx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox r8, r12
adox rbx, r9
adcx r11, [ rsp + 0x4b8 ]
adcx r10, [ rsp + 0x4e0 ]
mov r9, [ rsp + 0x4d8 ]
mov r13, 0x0 
adcx r9, r13
adox r11, [ rsp + 0x578 ]
adox r10, r15
clc
movzx rbp, bpl
adcx rbp, rdx
adcx r14, [ rsp + 0x560 ]
setc r15b
seto bpl
mov r12, rcx
mov rdx, 0xffffffffffffffff 
sub r12, rdx
dec r13
movzx rbp, bpl
adox rbp, r13
adox r14, r9
seto r9b
mov rbp, rdi
sbb rbp, rdx
mov r13, r8
sbb r13, rdx
mov rdx, rbx
mov [ rsp + 0x580 ], rbp
mov rbp, 0xfdc1767ae2ffffff 
sbb rdx, rbp
mov rbp, r11
mov [ rsp + 0x588 ], rdx
mov rdx, 0x7bc65c783158aea3 
sbb rbp, rdx
mov rdx, r10
mov [ rsp + 0x590 ], r12
mov r12, 0x6cfc5fd681c52056 
sbb rdx, r12
mov r12, r14
mov [ rsp + 0x598 ], rdx
mov rdx, 0x2341f27177344 
sbb r12, rdx
movzx rdx, r9b
movzx r15, r15b
lea rdx, [ rdx + r15 ]
sbb rdx, 0x00000000
cmovc r13, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r13
cmovc r12, r14
cmovc rbp, r11
mov r8, [ rsp + 0x598 ]
cmovc r8, r10
mov [ rdx + 0x20 ], rbp
mov [ rdx + 0x28 ], r8
mov r11, [ rsp + 0x590 ]
cmovc r11, rcx
mov [ rdx + 0x0 ], r11
mov rcx, [ rsp + 0x580 ]
cmovc rcx, rdi
mov [ rdx + 0x8 ], rcx
mov rdi, [ rsp + 0x588 ]
cmovc rdi, rbx
mov [ rdx + 0x30 ], r12
mov [ rdx + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1568
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4900
; seed 2261948732315921 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12155747 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 197816 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.016273454852260415
; number reverted permutation / tried permutation: 50263 / 89889 =55.917%
; number reverted decision / tried decision: 42713 / 90110 =47.401%
; validated in 361.71s
