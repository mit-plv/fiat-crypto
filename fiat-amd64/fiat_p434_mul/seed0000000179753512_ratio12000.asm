SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1832
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, 0x2341f27177344 
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, r10
test al, al
adox rbp, r11
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r13
mulx r13, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r11
mulx r11, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r13
mulx r13, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r11
mulx r11, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], r13
mulx r13, r11, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], r14
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], rcx
mulx rcx, rbx, r10
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], rcx
mulx rcx, rbx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x50 ], rcx
mov [ rsp + 0x58 ], rbx
mulx rbx, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], rcx
mulx rcx, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], rbx
mulx rbx, rcx, [ rax + 0x20 ]
mov rdx, r15
adcx rdx, rdi
mov [ rsp + 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
mov rdx, r15
adcx rdx, rdi
mov [ rsp + 0x98 ], r13
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r10
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], r9
mulx r9, rcx, r13
adcx rcx, rdi
setc dil
clc
adcx r15, rdx
mov rdx, [ rax + 0x18 ]
mulx r13, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], r15
mulx r15, r13, [ rax + 0x28 ]
adcx rbx, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r15
mulx r15, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xc8 ], r13
mov [ rsp + 0xd0 ], rbp
mulx rbp, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], r13
mulx r13, rbp, [ rax + 0x10 ]
seto dl
mov [ rsp + 0xe8 ], rcx
mov rcx, -0x2 
inc rcx
adox r11, r15
seto r15b
inc rcx
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox r12, rbp
setc dl
clc
adcx r8, rbx
mov rbx, 0xffffffffffffffff 
xchg rdx, r8
mulx rcx, rbp, rbx
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0xf0 ], r11
mov byte [ rsp + 0xf8 ], r15b
mulx r15, r11, rbx
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], r11
mulx r11, r15, [ rsi + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x110 ], r11
mov [ rsp + 0x118 ], r13
mulx r13, r11, rbx
mov rdx, rbp
mov [ rsp + 0x120 ], r13
seto r13b
mov [ rsp + 0x128 ], r11
mov r11, -0x2 
inc r11
adox rdx, rbx
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x130 ], r13b
mulx r13, r11, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x138 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
movzx r8, r8b
adox r8, r9
adox r12, r10
seto r10b
inc r9
adox r11, r14
adox r15, r13
mov r14, rbp
setc r8b
clc
adcx r14, rcx
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x140 ], r15
mulx r15, r9, r13
adcx rbp, rcx
adcx r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x148 ], r9
mulx r9, r13, [ rax + 0x18 ]
mov rdx, [ rsp + 0x138 ]
mov [ rsp + 0x150 ], r9
setc r9b
clc
mov [ rsp + 0x158 ], rbp
mov rbp, -0x1 
movzx rdi, dil
adcx rdi, rbp
adcx rdx, [ rsp + 0xa8 ]
seto dil
movzx rbp, byte [ rsp + 0x130 ]
mov [ rsp + 0x160 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox rbp, rdx
adox r13, [ rsp + 0x118 ]
setc bpl
clc
movzx r10, r10b
adcx r10, rdx
adcx r13, [ rsp + 0xe8 ]
seto r10b
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r12, r11
setc r8b
clc
movzx rbx, bl
adcx rbx, rdx
adcx r12, r14
seto bl
inc rdx
mov r11, -0x1 
movzx r9, r9b
adox r9, r11
adox r15, [ rsp + 0x108 ]
mov rdx, [ rax + 0x10 ]
mulx r9, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x168 ], r15
mulx r15, r11, [ rax + 0x18 ]
setc dl
clc
adcx r12, [ rsp + 0xd0 ]
mov byte [ rsp + 0x170 ], r8b
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mov byte [ rsp + 0x178 ], dil
mov byte [ rsp + 0x180 ], bpl
mulx rbp, rdi, [ rsi + 0x10 ]
setc dl
mov [ rsp + 0x188 ], rbp
movzx rbp, byte [ rsp + 0xf8 ]
clc
mov byte [ rsp + 0x190 ], r10b
mov r10, -0x1 
adcx rbp, r10
adcx r14, [ rsp + 0x90 ]
seto bpl
inc r10
mov r10, -0x1 
movzx rbx, bl
adox rbx, r10
adox r13, [ rsp + 0x140 ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, r12
mov [ rsp + 0x198 ], r14
mulx r14, r10, rbx
adcx r11, r9
adcx rdi, r15
setc r9b
clc
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r13, [ rsp + 0x158 ]
mov r8, [ rsp + 0x150 ]
setc r15b
movzx rbx, byte [ rsp + 0x190 ]
clc
mov [ rsp + 0x1a0 ], rdi
mov rdi, -0x1 
adcx rbx, rdi
adcx r8, [ rsp + 0x28 ]
mov rbx, [ rsp + 0x38 ]
seto dil
mov [ rsp + 0x1a8 ], r14
movzx r14, byte [ rsp + 0x180 ]
mov [ rsp + 0x1b0 ], r10
mov r10, 0x0 
dec r10
adox r14, r10
adox rbx, [ rsp + 0x20 ]
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1b8 ], r11
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x10 ]
mov byte [ rsp + 0x1c0 ], bpl
mov rbp, [ rsp - 0x40 ]
mov byte [ rsp + 0x1c8 ], r15b
seto r15b
mov [ rsp + 0x1d0 ], rdx
movzx rdx, byte [ rsp + 0x178 ]
mov [ rsp + 0x1d8 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox rbp, [ rsp + 0x110 ]
mov rdx, [ rsp - 0x48 ]
adox rdx, [ rsp - 0x8 ]
mov r13, rdx
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x1e0 ], r15b
mov byte [ rsp + 0x1e8 ], r12b
mulx r12, r15, [ rsi + 0x0 ]
adcx r15, r11
mov rdx, 0x0 
adcx r12, rdx
movzx r11, byte [ rsp + 0x170 ]
clc
mov rdx, -0x1 
adcx r11, rdx
adcx r8, [ rsp + 0x160 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1f0 ], r12
mulx r12, r11, [ rax + 0x28 ]
adcx rbx, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1f8 ], r12
mulx r12, r10, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x200 ], r12
mov [ rsp + 0x208 ], r15
mulx r15, r12, [ rsi + 0x18 ]
adox r11, [ rsp - 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x210 ], r11
mov [ rsp + 0x218 ], r10
mulx r10, r11, r14
mov rdx, r11
mov byte [ rsp + 0x220 ], r9b
setc r9b
clc
adcx rdx, r10
mov byte [ rsp + 0x228 ], r9b
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x230 ], r15
mov [ rsp + 0x238 ], r12
mulx r12, r15, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x240 ], r12
mov r12, 0x0 
dec r12
movzx rdi, dil
adox rdi, r12
adox r8, rbp
mov dil, dl
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rax + 0x30 ]
adox r13, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x248 ], r12
mulx r12, rbx, [ rax + 0x0 ]
seto dl
mov [ rsp + 0x250 ], rbp
mov rbp, -0x2 
inc rbp
adox r12, [ rsp + 0x238 ]
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov byte [ rsp + 0x258 ], dil
mov [ rsp + 0x260 ], r12
mulx r12, rdi, r14
mov rdx, [ rsp + 0x230 ]
adox rdx, [ rsp + 0xa0 ]
mov [ rsp + 0x268 ], rdx
mov rdx, [ rsp + 0x188 ]
mov [ rsp + 0x270 ], r12
setc r12b
mov [ rsp + 0x278 ], rdi
movzx rdi, byte [ rsp + 0x220 ]
clc
mov [ rsp + 0x280 ], r13
mov r13, -0x1 
adcx rdi, r13
adcx rdx, [ rsp + 0x218 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rdi
mov [ rsp + 0x288 ], rdi
mulx rdi, r13, rcx
mov rcx, r11
seto dl
mov [ rsp + 0x290 ], rdi
mov rdi, -0x2 
inc rdi
adox rcx, r14
mov rcx, [ rsp + 0x1d8 ]
seto dil
mov byte [ rsp + 0x298 ], r12b
movzx r12, byte [ rsp + 0x1e8 ]
mov [ rsp + 0x2a0 ], r13
mov r13, 0x0 
dec r13
adox r12, r13
adox rcx, [ rsp + 0xf0 ]
setc r12b
clc
movzx rdi, dil
adcx rdi, r13
adcx rcx, r9
mov r9, [ rsp + 0x208 ]
seto dil
movzx r13, byte [ rsp + 0x228 ]
mov byte [ rsp + 0x2a8 ], r12b
mov r12, 0x0 
dec r12
adox r13, r12
adox r9, [ rsp + 0x1d0 ]
seto r13b
inc r12
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox r9, [ rsp + 0x210 ]
setc bpl
clc
movzx rdx, dl
adcx rdx, r12
adcx r15, [ rsp + 0x98 ]
setc dl
clc
adcx rbx, rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x2b0 ], r15
mulx r15, r12, rcx
setc cl
mov [ rsp + 0x2b8 ], r15
movzx r15, byte [ rsp + 0x1c8 ]
clc
mov byte [ rsp + 0x2c0 ], bl
mov rbx, -0x1 
adcx r15, rbx
adcx r8, [ rsp + 0x148 ]
mov r15, [ rsp + 0x168 ]
adcx r15, [ rsp + 0x280 ]
mov rbx, [ rsp + 0x100 ]
mov byte [ rsp + 0x2c8 ], r13b
setc r13b
mov [ rsp + 0x2d0 ], r12
movzx r12, byte [ rsp + 0x1c0 ]
clc
mov [ rsp + 0x2d8 ], r15
mov r15, -0x1 
adcx r12, r15
adcx rbx, [ rsp + 0x2a0 ]
mov r12, r10
setc r15b
mov byte [ rsp + 0x2e0 ], cl
movzx rcx, byte [ rsp + 0x298 ]
clc
mov byte [ rsp + 0x2e8 ], bpl
mov rbp, -0x1 
adcx rcx, rbp
adcx r12, r11
mov r11, 0xffffffffffffffff 
mulx rbp, rcx, r11
setc r11b
clc
mov byte [ rsp + 0x2f0 ], r15b
mov r15, -0x1 
movzx r13, r13b
adcx r13, r15
adcx r9, rbx
setc r13b
clc
movzx rdi, dil
adcx rdi, r15
adcx r8, [ rsp + 0x198 ]
setc dil
movzx rbx, byte [ rsp + 0x2e8 ]
clc
adcx rbx, r15
adcx r8, r12
seto bl
movzx r12, byte [ rsp + 0x2e0 ]
inc r15
mov r15, -0x1 
adox r12, r15
adox r8, [ rsp + 0x260 ]
mov r12, [ rsp + 0x1b8 ]
seto r15b
mov byte [ rsp + 0x2f8 ], r13b
mov r13, 0x0 
dec r13
movzx rdi, dil
adox rdi, r13
adox r12, [ rsp + 0x2d8 ]
setc dil
clc
movzx r11, r11b
adcx r11, r13
adcx r10, [ rsp + 0x278 ]
setc r11b
clc
movzx rdi, dil
adcx rdi, r13
adcx r12, r10
mov rdi, rcx
seto r10b
inc r13
adox rdi, rbp
mov r13, rcx
adox r13, rbp
mov [ rsp + 0x300 ], r13
setc r13b
clc
adcx rcx, rdx
adcx rdi, r8
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mov byte [ rsp + 0x308 ], r13b
mulx r13, r8, [ rsi + 0x20 ]
setc dl
clc
adcx r8, rdi
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov [ rsp + 0x310 ], r13
mov byte [ rsp + 0x318 ], r8b
mulx r8, r13, rdi
mov rdi, [ rsp + 0x1b0 ]
mov [ rsp + 0x320 ], r8
setc r8b
clc
mov [ rsp + 0x328 ], r13
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx rdi, [ rsp + 0x270 ]
mov r11, 0x2341f27177344 
xchg rdx, r11
mov byte [ rsp + 0x330 ], r8b
mulx r8, r13, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x338 ], r8
mov [ rsp + 0x340 ], r13
mulx r13, r8, r11
mov rdx, 0x2341f27177344 
mov [ rsp + 0x348 ], r13
mov [ rsp + 0x350 ], r8
mulx r8, r13, r14
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x358 ], rdi
mov [ rsp + 0x360 ], r12
mulx r12, rdi, r11
mov [ rsp + 0x368 ], r12
mov [ rsp + 0x370 ], rdi
mulx rdi, r12, r14
movzx r14, byte [ rsp + 0x1e0 ]
mov rdx, [ rsp - 0x38 ]
lea r14, [ r14 + rdx ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x378 ], r15b
mov byte [ rsp + 0x380 ], bl
mulx rbx, r15, [ rax + 0x30 ]
adcx r12, [ rsp + 0x1a8 ]
adox rbp, [ rsp + 0x2d0 ]
adcx r13, rdi
mov rdx, [ rsp + 0x48 ]
seto dil
mov [ rsp + 0x388 ], rbp
movzx rbp, byte [ rsp + 0x2a8 ]
mov [ rsp + 0x390 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
adox rbp, r13
adox rdx, [ rsp + 0x200 ]
mov rbp, 0x0 
adcx r8, rbp
mov rbp, [ rsp + 0x40 ]
mov r13, 0x0 
adox rbp, r13
mov r13, rdx
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x398 ], dil
mov [ rsp + 0x3a0 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
add r10b, 0x7F
adox r9, [ rsp + 0x1a0 ]
mov rdx, [ rsp + 0x1f8 ]
movzx r10, byte [ rsp + 0x258 ]
mov [ rsp + 0x3a8 ], rbp
mov rbp, -0x1 
adcx r10, rbp
adcx rdx, [ rsp + 0x250 ]
mov r10, [ rsp + 0x290 ]
seto bpl
mov [ rsp + 0x3b0 ], r13
movzx r13, byte [ rsp + 0x2f0 ]
mov [ rsp + 0x3b8 ], rbx
mov rbx, 0x0 
dec rbx
adox r13, rbx
adox r10, [ rsp + 0x128 ]
mov r13, [ rsp + 0x120 ]
mov rbx, 0x0 
adox r13, rbx
mov rbx, [ rsp + 0x248 ]
adc rbx, 0x0
add byte [ rsp + 0x2c8 ], 0x7F
adox r14, [ rsp + 0x1f0 ]
mov [ rsp + 0x3c0 ], r15
movzx r15, byte [ rsp + 0x380 ]
mov [ rsp + 0x3c8 ], r8
mov r8, -0x1 
adcx r15, r8
adcx r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, r15, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x3d0 ], rdi
movzx rdi, byte [ rsp + 0x2f8 ]
mov [ rsp + 0x3d8 ], r8
mov r8, 0x0 
dec r8
adox rdi, r8
adox r14, r10
seto dil
inc r8
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox r14, [ rsp + 0x288 ]
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mulx r10, r8, [ rax + 0x18 ]
mov rdx, [ rsp + 0x360 ]
mov [ rsp + 0x3e0 ], r10
seto r10b
mov [ rsp + 0x3e8 ], r8
movzx r8, byte [ rsp + 0x378 ]
mov [ rsp + 0x3f0 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
adox r8, r15
adox rdx, [ rsp + 0x268 ]
movzx r8, bpl
adcx r8, rbx
setc bl
movzx rbp, byte [ rsp + 0x318 ]
clc
adcx rbp, r15
adcx rdx, [ rsp + 0x300 ]
seto bpl
inc r15
mov r15, -0x1 
movzx rdi, dil
adox rdi, r15
adox r8, r13
seto r13b
movzx rdi, byte [ rsp + 0x308 ]
inc r15
mov r15, -0x1 
adox rdi, r15
adox r9, [ rsp + 0x358 ]
adox r12, r14
mov rdi, [ rsp + 0x240 ]
seto r14b
movzx r15, byte [ rsp + 0x2c0 ]
mov [ rsp + 0x3f8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r15, r12
adox rdi, [ rsp + 0x3f0 ]
mov r15, [ rsp + 0x3d8 ]
adox r15, [ rsp + 0x3d0 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x400 ], r15
mov [ rsp + 0x408 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x410 ], r9
mov byte [ rsp + 0x418 ], bpl
mulx rbp, r9, r11
mov rdx, r9
mov byte [ rsp + 0x420 ], bl
setc bl
clc
adcx rdx, rbp
mov byte [ rsp + 0x428 ], bl
mov rbx, r9
mov byte [ rsp + 0x430 ], r13b
seto r13b
mov byte [ rsp + 0x438 ], r14b
mov r14, -0x2 
inc r14
adox rbx, r11
mov rbx, [ rsp + 0x310 ]
seto r14b
mov [ rsp + 0x440 ], r8
mov r8, -0x2 
inc r8
adox rbx, [ rsp + 0x8 ]
adox r15, [ rsp + 0x0 ]
mov r8, [ rsp + 0x3c8 ]
mov [ rsp + 0x448 ], r15
seto r15b
mov byte [ rsp + 0x450 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
movzx r13, r13b
adox r13, r10
adox r8, [ rsp + 0x3c0 ]
adcx r9, rbp
seto r13b
movzx r10, byte [ rsp + 0x330 ]
mov [ rsp + 0x458 ], r8
mov r8, 0x0 
dec r8
adox r10, r8
adox r12, rbx
seto r10b
inc r8
mov rbx, -0x1 
movzx r15, r15b
adox r15, rbx
adox rdi, [ rsp + 0x3e8 ]
setc r15b
clc
movzx r14, r14b
adcx r14, rbx
adcx r12, rdx
setc dl
clc
adcx r12, [ rsp - 0x28 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mulx rbx, r8, r12
movzx rdx, r13b
mov [ rsp + 0x460 ], r9
mov r9, [ rsp + 0x3b8 ]
lea rdx, [ rdx + r9 ]
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r9
mov [ rsp + 0x468 ], r9
mulx r9, r13, r12
mov rdx, r8
mov [ rsp + 0x470 ], r9
seto r9b
mov byte [ rsp + 0x478 ], r14b
mov r14, -0x2 
inc r14
adox rdx, rbx
mov r14, r8
adox r14, rbx
mov [ rsp + 0x480 ], r14
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x488 ], rdi
mov byte [ rsp + 0x490 ], r10b
mulx r10, rdi, [ rsi + 0x30 ]
adox r13, rbx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x498 ], r13
mulx r13, rbx, r12
mov rdx, [ rsp + 0x3b0 ]
mov [ rsp + 0x4a0 ], r13
setc r13b
mov [ rsp + 0x4a8 ], rbx
movzx rbx, byte [ rsp + 0x450 ]
clc
mov [ rsp + 0x4b0 ], rdi
mov rdi, -0x1 
adcx rbx, rdi
adcx rdx, [ rsp + 0x440 ]
seto bl
movzx rdi, byte [ rsp + 0x438 ]
mov [ rsp + 0x4b8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rdi, r14
adox rdx, [ rsp + 0x390 ]
movzx rdi, byte [ rsp + 0x430 ]
movzx r14, byte [ rsp + 0x420 ]
lea rdi, [ rdi + r14 ]
mov r14, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov byte [ rsp + 0x4c0 ], bl
mov [ rsp + 0x4c8 ], rcx
mulx rcx, rbx, r14
adcx rdi, [ rsp + 0x3a8 ]
mov r14, rdx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x4d0 ], r13b
mov byte [ rsp + 0x4d8 ], r9b
mulx r9, r13, [ rsi + 0x30 ]
setc dl
clc
mov [ rsp + 0x4e0 ], r9
mov r9, -0x1 
movzx r15, r15b
adcx r15, r9
adcx rbp, [ rsp + 0x328 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov byte [ rsp + 0x4e8 ], r15b
mulx r15, r9, r14
adox rdi, [ rsp + 0x3a0 ]
mov r14, [ rsp + 0x350 ]
adcx r14, [ rsp + 0x320 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x4f0 ], r14
mov [ rsp + 0x4f8 ], rdi
mulx rdi, r14, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x500 ], rbp
mov rbp, -0x2 
inc rbp
adox r14, r10
seto r10b
movzx rbp, byte [ rsp + 0x398 ]
mov [ rsp + 0x508 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rbp, r14
adox r9, [ rsp + 0x2b8 ]
adox rbx, r15
adox rcx, [ rsp + 0x340 ]
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mulx r14, r15, [ rax + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x510 ], rcx
mov [ rsp + 0x518 ], rbx
mulx rbx, rcx, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x520 ], rbx
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, [ rsp + 0x338 ]
mov byte [ rsp + 0x528 ], bpl
mov rbp, 0x0 
adox rdx, rbp
dec rbp
movzx r10, r10b
adox r10, rbp
adox rdi, r13
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, [ rsp + 0x4e0 ]
adox rdx, [ rsp - 0x18 ]
mov [ rsp + 0x530 ], rdx
mov rdx, [ rsp + 0x348 ]
adcx rdx, [ rsp + 0x370 ]
mov [ rsp + 0x538 ], rdi
seto dil
mov [ rsp + 0x540 ], rdx
mov rdx, -0x2 
inc rdx
adox r15, [ rsp - 0x30 ]
adox r10, r14
adcx rcx, [ rsp + 0x368 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x548 ], rcx
mulx rcx, r14, [ rsi + 0x28 ]
adox rbp, [ rsp + 0xb8 ]
adox r14, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xc8 ]
setc dl
clc
adcx r8, r12
mov r8, [ rsp + 0xc0 ]
adox r8, [ rsp + 0x78 ]
mov [ rsp + 0x550 ], r8
mov r8, [ rsp + 0x88 ]
mov [ rsp + 0x558 ], rcx
seto cl
mov [ rsp + 0x560 ], r14
movzx r14, byte [ rsp + 0x4d8 ]
mov byte [ rsp + 0x568 ], dl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r14, rdx
adox r8, [ rsp + 0x3e0 ]
adox r11, [ rsp + 0x80 ]
mov r14, [ rsp + 0x2b0 ]
seto dl
mov byte [ rsp + 0x570 ], cl
movzx rcx, byte [ rsp + 0x418 ]
mov [ rsp + 0x578 ], rbp
mov rbp, 0x0 
dec rbp
adox rcx, rbp
adox r14, [ rsp + 0x410 ]
mov rcx, [ rsp + 0x408 ]
adox rcx, [ rsp + 0x3f8 ]
mov rbp, [ rsp + 0x68 ]
mov [ rsp + 0x580 ], r11
setc r11b
clc
mov [ rsp + 0x588 ], r13
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx rbp, [ rsp - 0x20 ]
seto dil
movzx r13, byte [ rsp + 0x428 ]
mov [ rsp + 0x590 ], rbp
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
adox r13, rbp
adox r14, [ rsp + 0x388 ]
mov r13, [ rsp + 0x60 ]
adcx r13, [ rsp + 0x58 ]
mov bpl, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x598 ], r13
mov [ rsp + 0x5a0 ], r8
mulx r8, r13, [ rsi + 0x20 ]
adox r9, rcx
seto dl
movzx rcx, byte [ rsp + 0x490 ]
mov byte [ rsp + 0x5a8 ], dil
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox rcx, rdi
adox r14, [ rsp + 0x448 ]
adox r9, [ rsp + 0x488 ]
seto cl
movzx rdi, byte [ rsp + 0x478 ]
mov byte [ rsp + 0x5b0 ], dl
mov rdx, 0x0 
dec rdx
adox rdi, rdx
adox r14, [ rsp + 0x460 ]
seto dil
movzx rdx, byte [ rsp + 0x4d0 ]
mov byte [ rsp + 0x5b8 ], cl
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
adox rdx, rcx
adox r14, r15
seto dl
inc rcx
mov r15, -0x1 
movzx r11, r11b
adox r11, r15
adox r14, [ rsp + 0x4b8 ]
setc r11b
clc
movzx rbp, bpl
adcx rbp, r15
adcx rbx, r13
adcx r8, rcx
clc
adcx r14, [ rsp + 0x4b0 ]
setc bpl
clc
movzx rdi, dil
adcx rdi, r15
adcx r9, [ rsp + 0x500 ]
setc r13b
clc
movzx rdx, dl
adcx rdx, r15
adcx r9, r10
adox r9, [ rsp + 0x480 ]
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx rdi, r10, r14
mov r15, r10
setc dl
clc
adcx r15, rdi
mov byte [ rsp + 0x5c0 ], r11b
mov r11, r10
mov [ rsp + 0x5c8 ], r15
seto r15b
mov byte [ rsp + 0x5d0 ], dl
mov rdx, -0x3 
inc rdx
adox r11, r14
movzx r11, byte [ rsp + 0x528 ]
movzx rcx, byte [ rsp + 0x4e8 ]
lea r11, [ r11 + rcx ]
seto cl
mov rdx, 0x0 
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r9, [ rsp + 0x508 ]
mov rbp, [ rsp + 0x400 ]
seto dl
mov [ rsp + 0x5d8 ], r9
movzx r9, byte [ rsp + 0x5a8 ]
mov byte [ rsp + 0x5e0 ], cl
mov rcx, 0x0 
dec rcx
adox r9, rcx
adox rbp, [ rsp + 0x4c8 ]
adcx r10, rdi
mov r9, [ rsp + 0x458 ]
adox r9, [ rsp + 0x4f8 ]
adox r11, [ rsp + 0x468 ]
setc cl
mov [ rsp + 0x5e8 ], r10
movzx r10, byte [ rsp + 0x5b0 ]
clc
mov byte [ rsp + 0x5f0 ], dl
mov rdx, -0x1 
adcx r10, rdx
adcx rbp, [ rsp + 0x518 ]
adcx r9, [ rsp + 0x510 ]
seto r10b
movzx rdx, byte [ rsp + 0x5b8 ]
mov byte [ rsp + 0x5f8 ], cl
mov rcx, 0x0 
dec rcx
adox rdx, rcx
adox rbp, [ rsp + 0x5a0 ]
adcx r11, [ rsp + 0x588 ]
adox r9, [ rsp + 0x580 ]
movzx rdx, r10b
mov rcx, 0x0 
adcx rdx, rcx
adox rbx, r11
adox r8, rdx
clc
mov r10, -0x1 
movzx r13, r13b
adcx r13, r10
adcx rbp, [ rsp + 0x4f0 ]
seto r13b
movzx r11, byte [ rsp + 0x5d0 ]
inc r10
mov rcx, -0x1 
adox r11, rcx
adox rbp, [ rsp + 0x578 ]
adcx r9, [ rsp + 0x540 ]
adcx rbx, [ rsp + 0x548 ]
movzx r11, byte [ rsp + 0x568 ]
mov rdx, [ rsp + 0x520 ]
lea r11, [ r11 + rdx ]
mov rdx, 0x7bc65c783158aea3 
mulx rcx, r10, r12
adox r9, [ rsp + 0x560 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x600 ], r9
mov byte [ rsp + 0x608 ], r13b
mulx r13, r9, r12
adox rbx, [ rsp + 0x558 ]
seto r12b
movzx rdx, byte [ rsp + 0x4c0 ]
mov [ rsp + 0x610 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox rdx, rbx
adox r10, [ rsp + 0x470 ]
adox rcx, [ rsp + 0x4a8 ]
adox r9, [ rsp + 0x4a0 ]
adcx r11, r8
mov rdx, 0x0 
adox r13, rdx
inc rbx
mov rdx, -0x1 
movzx r15, r15b
adox r15, rdx
adox rbp, [ rsp + 0x498 ]
movzx r15, byte [ rsp + 0x608 ]
adcx r15, rbx
movzx r8, byte [ rsp + 0x5f0 ]
clc
adcx r8, rdx
adcx rbp, [ rsp + 0x538 ]
mov r8, [ rsp + 0x5d8 ]
setc bl
movzx rdx, byte [ rsp + 0x5e0 ]
clc
mov [ rsp + 0x618 ], r13
mov r13, -0x1 
adcx rdx, r13
adcx r8, [ rsp + 0x5c8 ]
adox r10, [ rsp + 0x600 ]
adox rcx, [ rsp + 0x610 ]
setc dl
seto r13b
mov [ rsp + 0x620 ], rbp
mov rbp, r8
mov [ rsp + 0x628 ], rcx
mov rcx, 0xffffffffffffffff 
sub rbp, rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x630 ], rbp
mov byte [ rsp + 0x638 ], cl
mulx rcx, rbp, r14
movzx rdx, byte [ rsp + 0x570 ]
mov [ rsp + 0x640 ], rcx
mov rcx, [ rsp + 0x70 ]
lea rdx, [ rdx + rcx ]
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, r14
mov [ rsp + 0x648 ], r10
mov byte [ rsp + 0x650 ], bl
mulx rbx, r10, rcx
mov rcx, [ rsp + 0x50 ]
mov [ rsp + 0x658 ], rbx
movzx rbx, byte [ rsp + 0x5c0 ]
mov [ rsp + 0x660 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox rbx, r10
adox rcx, [ rsp + 0xe0 ]
seto bl
inc r10
mov r10, -0x1 
movzx r12, r12b
adox r12, r10
adox r11, [ rsp + 0x550 ]
adox r14, r15
setc r12b
clc
movzx r13, r13b
adcx r13, r10
adcx r11, r9
seto r9b
movzx r15, byte [ rsp + 0x5f8 ]
inc r10
mov r13, -0x1 
adox r15, r13
adox rdi, rbp
mov r15, [ rsp + 0x648 ]
setc bpl
movzx r10, byte [ rsp + 0x650 ]
clc
adcx r10, r13
adcx r15, [ rsp + 0x530 ]
mov r10, [ rsp + 0x628 ]
adcx r10, [ rsp + 0x590 ]
adcx r11, [ rsp + 0x598 ]
mov r13, [ rsp + 0x5e8 ]
mov [ rsp + 0x668 ], rcx
setc cl
mov byte [ rsp + 0x670 ], bl
movzx rbx, byte [ rsp + 0x638 ]
clc
mov byte [ rsp + 0x678 ], r12b
mov r12, -0x1 
adcx rbx, r12
adcx r13, [ rsp + 0x620 ]
adcx rdi, r15
mov rbx, 0x7bc65c783158aea3 
mulx r12, r15, rbx
adox r15, [ rsp + 0x640 ]
mov rbx, 0x2341f27177344 
mov byte [ rsp + 0x680 ], cl
mov [ rsp + 0x688 ], rdi
mulx rdi, rcx, rbx
adcx r15, r10
adox r12, [ rsp + 0x660 ]
adcx r12, r11
seto dl
mov r10, -0x1 
inc r10
mov r11, -0x1 
movzx rbp, bpl
adox rbp, r11
adox r14, [ rsp + 0x618 ]
movzx rbp, r9b
adox rbp, r10
dec r10
movzx rdx, dl
adox rdx, r10
adox rcx, [ rsp + 0x658 ]
mov r11, 0x0 
adox rdi, r11
setc r9b
movzx rdx, byte [ rsp + 0x678 ]
add rdx, -0x1
mov rdx, r13
mov r11, 0xffffffffffffffff 
sbb rdx, r11
mov r10, [ rsp + 0x688 ]
sbb r10, r11
mov rbx, r15
mov r11, 0xfdc1767ae2ffffff 
sbb rbx, r11
mov r11, r12
mov [ rsp + 0x690 ], rbx
mov rbx, 0x7bc65c783158aea3 
sbb r11, rbx
movzx rbx, byte [ rsp + 0x670 ]
mov [ rsp + 0x698 ], r10
mov r10, [ rsp + 0xd8 ]
lea rbx, [ rbx + r10 ]
movzx r10, byte [ rsp + 0x680 ]
mov [ rsp + 0x6a0 ], r11
mov r11, 0x0 
dec r11
adox r10, r11
adox r14, [ rsp + 0x668 ]
setc r10b
clc
movzx r9, r9b
adcx r9, r11
adcx r14, rcx
adox rbx, rbp
adcx rdi, rbx
seto r9b
adc r9b, 0x0
movzx r9, r9b
movzx rbp, r10b
add rbp, -0x1
mov r10, r14
mov rbp, 0x6cfc5fd681c52056 
sbb r10, rbp
mov rcx, rdi
mov rbx, 0x2341f27177344 
sbb rcx, rbx
movzx r11, r9b
sbb r11, 0x00000000
cmovc rcx, rdi
cmovc rdx, r13
mov r11, [ rsp + 0x6a0 ]
cmovc r11, r12
mov r13, [ rsp + 0x630 ]
cmovc r13, r8
cmovc r10, r14
mov r8, [ rsp + 0x698 ]
cmovc r8, [ rsp + 0x688 ]
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], r8
mov [ r12 + 0x0 ], r13
mov [ r12 + 0x30 ], rcx
mov r14, [ rsp + 0x690 ]
cmovc r14, r15
mov [ r12 + 0x18 ], r14
mov [ r12 + 0x20 ], r11
mov [ r12 + 0x8 ], rdx
mov [ r12 + 0x28 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1832
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2000
; seed 2792576969839854 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10762700 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=33, initial num_batches=31): 165207 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.015349958653497729
; number reverted permutation / tried permutation: 51130 / 89996 =56.814%
; number reverted decision / tried decision: 45889 / 90003 =50.986%
; validated in 291.499s
