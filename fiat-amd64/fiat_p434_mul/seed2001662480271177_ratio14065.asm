SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 1672
mov rax, rdx
mov rdx, [ rdx + 0x28 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r11
mulx r11, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r15
mulx r15, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r15
mulx r15, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], r12
mulx r12, r15, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r15
mulx r15, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], r12
mulx r12, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], rbp
mulx rbp, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], rbp
mov [ rsp + 0x40 ], r11
mulx r11, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], rbp
mulx rbp, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r12
mulx r12, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r12
mov [ rsp + 0x70 ], r8
mulx r8, r12, [ rax + 0x10 ]
test al, al
adox r10, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x78 ], r10
mulx r10, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r10
mov [ rsp + 0x88 ], rdi
mulx rdi, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r10
mulx r10, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xa0 ], r8
mov [ rsp + 0xa8 ], r12
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb0 ], r12
mov [ rsp + 0xb8 ], r10
mulx r10, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], r8
mulx r8, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], rbx
mulx rbx, r15, [ rax + 0x30 ]
adcx r13, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], rbx
mulx rbx, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r8
mulx r8, rbx, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rbx
mulx rbx, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], rbx
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x118 ], rbx
mov [ rsp + 0x120 ], r15
mulx r15, rbx, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x128 ], r15
mov [ rsp + 0x130 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x138 ], r8
mov [ rsp + 0x140 ], r13
mulx r13, r8, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], r13
mov [ rsp + 0x150 ], r8
mulx r8, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], r9
mulx r9, r13, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x168 ], r9
mov r9, -0x2 
inc r9
adox rcx, r8
mov r8b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x170 ], rcx
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x178 ], rcx
mov [ rsp + 0x180 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
adcx r15, r14
adcx r11, rbx
mov rdx, 0x2341f27177344 
mulx rbx, r14, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x188 ], rbx
mov [ rsp + 0x190 ], r9
mulx r9, rbx, [ rax + 0x0 ]
adcx rdi, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x198 ], rbx
mulx rbx, rbp, [ rsi + 0x30 ]
setc dl
clc
adcx rcx, r10
mov r10b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1a0 ], rbp
mov [ rsp + 0x1a8 ], rcx
mulx rcx, rbp, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b0 ], rcx
mov [ rsp + 0x1b8 ], r13
mulx r13, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x1c0 ], rbp
mov byte [ rsp + 0x1c8 ], r10b
mulx r10, rbp, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1d0 ], r14
mov [ rsp + 0x1d8 ], rdi
mulx rdi, r14, r12
setc dl
clc
adcx rbx, [ rsp + 0x160 ]
mov [ rsp + 0x1e0 ], rbx
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e8 ], r10
mov [ rsp + 0x1f0 ], rbp
mulx rbp, r10, [ rax + 0x8 ]
setc dl
clc
adcx r10, r9
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1f8 ], r10
mov byte [ rsp + 0x200 ], bl
mulx rbx, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x208 ], r9b
mov [ rsp + 0x210 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
adcx r9, rbp
mov rdx, r14
seto bpl
mov [ rsp + 0x218 ], r9
mov r9, -0x2 
inc r9
adox rdx, rdi
adcx r10, rbx
mov rbx, r14
adox rbx, rdi
setc r9b
clc
mov [ rsp + 0x220 ], r10
mov r10, -0x1 
movzx r8, r8b
adcx r8, r10
adcx rcx, [ rsp + 0xd8 ]
mov r8, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x228 ], rcx
mulx rcx, r10, [ rsi + 0x20 ]
adcx r13, [ rsp + 0xd0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x230 ], r13
mov byte [ rsp + 0x238 ], r9b
mulx r9, r13, [ rsi + 0x8 ]
adcx r10, [ rsp + 0x60 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x240 ], r10
mov [ rsp + 0x248 ], r9
mulx r9, r10, [ rsi + 0x20 ]
setc dl
clc
adcx r14, r12
adox rdi, [ rsp + 0x150 ]
adcx r8, [ rsp + 0x140 ]
adcx rbx, r15
seto r14b
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rdx, dl
adox rdx, r15
adox rcx, [ rsp + 0x138 ]
adox r10, [ rsp + 0x110 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x250 ], r10
mulx r10, r15, r12
adcx rdi, r11
seto r12b
mov r11, -0x2 
inc r11
adox r8, [ rsp + 0xc8 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x258 ], rcx
mulx rcx, r11, r8
movzx rdx, r12b
lea rdx, [ rdx + r9 ]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x260 ], rcx
mulx rcx, r12, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x1f0 ]
mov [ rsp + 0x268 ], r9
seto r9b
mov [ rsp + 0x270 ], r11
mov r11, 0x0 
dec r11
movzx rbp, bpl
adox rbp, r11
adox rdx, [ rsp + 0x58 ]
mov rbp, [ rsp + 0x210 ]
setc r11b
mov [ rsp + 0x278 ], rdx
movzx rdx, byte [ rsp + 0x238 ]
clc
mov [ rsp + 0x280 ], rcx
mov rcx, -0x1 
adcx rdx, rcx
adcx rbp, [ rsp + 0x30 ]
mov rdx, [ rsp + 0x1e8 ]
adox rdx, [ rsp + 0x28 ]
seto cl
mov [ rsp + 0x288 ], rdx
mov rdx, 0x0 
dec rdx
movzx r14, r14b
adox r14, rdx
adox r15, [ rsp + 0x148 ]
seto r14b
inc rdx
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox r15, [ rsp + 0x1d8 ]
mov r11, [ rsp + 0x0 ]
adcx r11, [ rsp + 0x120 ]
mov rdx, [ rsp + 0x118 ]
adcx rdx, [ rsp + 0x50 ]
mov [ rsp + 0x290 ], rdx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x298 ], r11
mov [ rsp + 0x2a0 ], rbp
mulx rbp, r11, r8
mov rdx, [ rsp - 0x10 ]
mov [ rsp + 0x2a8 ], rbp
setc bpl
clc
mov [ rsp + 0x2b0 ], r11
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx rdx, [ rsp + 0x40 ]
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x2b8 ], r15
mulx r15, r11, [ rax + 0x18 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2c0 ], rcx
mov [ rsp + 0x2c8 ], r15
mulx r15, rcx, r8
movzx rdx, bpl
mov [ rsp + 0x2d0 ], r15
mov r15, [ rsp + 0x48 ]
lea rdx, [ rdx + r15 ]
seto r15b
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox r10, [ rsp + 0x130 ]
mov r14, [ rsp + 0x128 ]
adox r14, [ rsp + 0x1d0 ]
mov rbp, [ rsp + 0xb8 ]
mov [ rsp + 0x2d8 ], rdx
seto dl
mov [ rsp + 0x2e0 ], rcx
movzx rcx, byte [ rsp + 0x1c8 ]
mov [ rsp + 0x2e8 ], r14
mov r14, 0x0 
dec r14
adox rcx, r14
adox rbp, [ rsp - 0x18 ]
setc cl
clc
adcx r13, [ rsp + 0xb0 ]
mov r14, [ rsp + 0x248 ]
adcx r14, [ rsp + 0xa8 ]
mov byte [ rsp + 0x2f0 ], dl
setc dl
clc
mov [ rsp + 0x2f8 ], r11
mov r11, -0x1 
movzx r15, r15b
adcx r15, r11
adcx rbp, r10
mov r15, [ rsp - 0x20 ]
adox r15, [ rsp + 0x108 ]
mov r10, [ rsp + 0x10 ]
setc r11b
clc
mov [ rsp + 0x300 ], rbp
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx r10, [ rsp + 0x38 ]
seto cl
inc rbp
mov rbp, -0x1 
movzx r9, r9b
adox r9, rbp
adox rbx, r13
setc r9b
movzx r13, byte [ rsp + 0x208 ]
clc
adcx r13, rbp
adcx r12, [ rsp - 0x8 ]
mov r13, [ rsp + 0x8 ]
setc bpl
clc
mov [ rsp + 0x308 ], r12
mov r12, -0x1 
movzx r9, r9b
adcx r9, r12
adcx r13, [ rsp + 0x1c0 ]
mov r9, [ rsp + 0x1b8 ]
setc r12b
mov [ rsp + 0x310 ], r13
movzx r13, byte [ rsp + 0x200 ]
clc
mov [ rsp + 0x318 ], r10
mov r10, -0x1 
adcx r13, r10
adcx r9, [ rsp + 0x190 ]
adox r14, rdi
mov r13, [ rsp + 0xa0 ]
setc dil
clc
movzx rdx, dl
adcx rdx, r10
adcx r13, [ rsp + 0x2f8 ]
mov rdx, [ rsp + 0x2c8 ]
adcx rdx, [ rsp + 0xf0 ]
movzx r10, cl
mov byte [ rsp + 0x320 ], r12b
mov r12, [ rsp + 0xe0 ]
lea r10, [ r10 + r12 ]
mov r12, [ rsp - 0x28 ]
adcx r12, [ rsp + 0xe8 ]
mov rcx, [ rsp + 0x88 ]
adcx rcx, [ rsp - 0x40 ]
adox r13, [ rsp + 0x2b8 ]
mov [ rsp + 0x328 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x330 ], r13
mov [ rsp + 0x338 ], r14
mulx r14, r13, [ rax + 0x30 ]
mov rdx, [ rsp + 0x80 ]
mov [ rsp + 0x340 ], r14
mov r14, 0x0 
adcx rdx, r14
movzx r14, byte [ rsp + 0x2f0 ]
mov [ rsp + 0x348 ], rbx
mov rbx, [ rsp + 0x188 ]
lea r14, [ r14 + rbx ]
mov rbx, [ rsp + 0x280 ]
clc
mov [ rsp + 0x350 ], rdx
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx rbx, [ rsp + 0x100 ]
mov rbp, [ rsp + 0xf8 ]
adcx rbp, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
adcx rdx, [ rsp + 0x180 ]
adcx r13, [ rsp + 0x168 ]
mov [ rsp + 0x358 ], r13
mov r13, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x360 ], rbp
mov [ rsp + 0x368 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x178 ]
mov [ rsp + 0x370 ], r13
setc r13b
clc
mov [ rsp + 0x378 ], rcx
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx rdx, [ rsp + 0x70 ]
seto dil
inc rcx
mov rcx, -0x1 
movzx r11, r11b
adox r11, rcx
adox r15, [ rsp + 0x2e8 ]
setc r11b
clc
movzx rdi, dil
adcx rdi, rcx
adcx r9, [ rsp + 0x300 ]
mov rdi, [ rsp + 0x68 ]
seto cl
mov byte [ rsp + 0x380 ], r13b
mov r13, 0x0 
dec r13
movzx r11, r11b
adox r11, r13
adox rdi, [ rsp + 0x98 ]
adcx r12, r15
setc r11b
clc
movzx rcx, cl
adcx rcx, r13
adcx r10, r14
mov r14, [ rsp + 0x20 ]
adox r14, [ rsp + 0x90 ]
mov r15, 0x2341f27177344 
xchg rdx, r15
mulx r13, rcx, r8
adox rbp, [ rsp + 0x18 ]
mov rdx, 0x0 
adox rbx, rdx
dec rdx
movzx r11, r11b
adox r11, rdx
adox r10, [ rsp + 0x378 ]
mov r11, r8
setc dl
clc
adcx r11, [ rsp + 0x270 ]
movzx rdx, dl
movzx r11, dl
adox r11, [ rsp + 0x350 ]
mov rdx, [ rsp + 0x260 ]
mov [ rsp + 0x388 ], rbx
mov rbx, rdx
mov [ rsp + 0x390 ], rbp
seto bpl
mov [ rsp + 0x398 ], r14
mov r14, -0x2 
inc r14
adox rbx, [ rsp + 0x270 ]
mov r14, rdx
adox r14, [ rsp + 0x270 ]
mov [ rsp + 0x3a0 ], rdi
mov rdi, 0x7bc65c783158aea3 
xchg rdx, rdi
mov [ rsp + 0x3a8 ], r15
mov byte [ rsp + 0x3b0 ], bpl
mulx rbp, r15, r8
adcx rbx, [ rsp + 0x348 ]
adcx r14, [ rsp + 0x338 ]
adox rdi, [ rsp + 0x2e0 ]
adox r15, [ rsp + 0x2d0 ]
adox rbp, [ rsp + 0x2b0 ]
adcx rdi, [ rsp + 0x330 ]
adcx r15, r9
adox rcx, [ rsp + 0x2a8 ]
adcx rbp, r12
seto r8b
mov r9, -0x2 
inc r9
adox rbx, [ rsp + 0x198 ]
adcx rcx, r10
movzx r12, r8b
lea r12, [ r12 + r13 ]
mov r13, 0xfdc1767ae2ffffff 
mov rdx, rbx
mulx r10, rbx, r13
adcx r12, r11
adox r14, [ rsp + 0x1f8 ]
mov r11, 0x6cfc5fd681c52056 
mulx r9, r8, r11
adox rdi, [ rsp + 0x218 ]
movzx r13, byte [ rsp + 0x3b0 ]
mov r11, 0x0 
adcx r13, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x3b8 ], r9
mov [ rsp + 0x3c0 ], r8
mulx r8, r9, r11
adox r15, [ rsp + 0x220 ]
adox rbp, [ rsp + 0x2a0 ]
mov r11, r9
clc
adcx r11, r8
mov [ rsp + 0x3c8 ], rbp
mov rbp, 0x2341f27177344 
mov [ rsp + 0x3d0 ], r13
mov [ rsp + 0x3d8 ], r12
mulx r12, r13, rbp
mov rbp, r9
mov [ rsp + 0x3e0 ], r12
setc r12b
clc
adcx rbp, rdx
adcx r11, r14
setc bpl
clc
adcx r11, [ rsp + 0xc0 ]
mov r14, r8
mov [ rsp + 0x3e8 ], r13
setc r13b
clc
mov [ rsp + 0x3f0 ], r10
mov r10, -0x1 
movzx r12, r12b
adcx r12, r10
adcx r14, r9
adcx rbx, r8
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r11
mulx r12, r8, r9
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3f8 ], r12
mulx r12, r9, r10
setc r10b
clc
mov [ rsp + 0x400 ], r8
mov r8, -0x1 
movzx rbp, bpl
adcx rbp, r8
adcx rdi, r14
mov rbp, 0x2341f27177344 
mulx r8, r14, rbp
adcx rbx, r15
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x408 ], r8
mulx r8, rbp, r11
adox rcx, [ rsp + 0x298 ]
mov r11, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp + 0x410 ], r14
mulx r14, r15, r11
seto r11b
mov [ rsp + 0x418 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox rdi, [ rsp + 0x1a8 ]
seto r13b
inc r12
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox rbp, [ rsp + 0x3f0 ]
mov r10, [ rsp + 0x290 ]
setc r12b
clc
mov [ rsp + 0x420 ], rdi
mov rdi, -0x1 
movzx r11, r11b
adcx r11, rdi
adcx r10, [ rsp + 0x3d8 ]
mov r11, [ rsp + 0x3d0 ]
adcx r11, [ rsp + 0x2d8 ]
seto dil
mov [ rsp + 0x428 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r12, r12b
adox r12, r11
adox rbp, [ rsp + 0x3c8 ]
mov r12, 0x7bc65c783158aea3 
mov [ rsp + 0x430 ], r10
mulx r10, r11, r12
mov r12, r15
mov [ rsp + 0x438 ], r10
setc r10b
clc
adcx r12, r14
mov byte [ rsp + 0x440 ], r10b
mov r10, r15
adcx r10, r14
adcx r9, r14
setc r14b
clc
mov [ rsp + 0x448 ], r9
mov r9, -0x1 
movzx rdi, dil
adcx rdi, r9
adcx r8, [ rsp + 0x3c0 ]
adox r8, rcx
setc cl
clc
movzx r13, r13b
adcx r13, r9
adcx rbx, [ rsp + 0x328 ]
adcx rbp, [ rsp + 0x3a8 ]
seto r13b
inc r9
mov rdi, -0x1 
movzx r14, r14b
adox r14, rdi
adox r11, [ rsp + 0x418 ]
mov r14, [ rsp + 0x438 ]
adox r14, [ rsp + 0x400 ]
setc dil
clc
adcx r15, rdx
setc r15b
clc
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx r8, [ rsp + 0x3a0 ]
mov rdi, [ rsp + 0x3b8 ]
seto r9b
inc rdx
mov rdx, -0x1 
movzx rcx, cl
adox rcx, rdx
adox rdi, [ rsp + 0x3e8 ]
mov rcx, [ rsp + 0x3f8 ]
seto dl
mov [ rsp + 0x450 ], r14
mov r14, 0x0 
dec r14
movzx r9, r9b
adox r9, r14
adox rcx, [ rsp + 0x410 ]
setc r9b
clc
movzx r15, r15b
adcx r15, r14
adcx r12, [ rsp + 0x420 ]
adcx r10, rbx
mov rbx, [ rsp + 0x408 ]
mov r15, 0x0 
adox rbx, r15
mov r14, -0x3 
inc r14
adox r12, [ rsp - 0x48 ]
adox r10, [ rsp + 0x78 ]
mov r15, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x458 ], rbx
mulx rbx, r14, r12
adcx rbp, [ rsp + 0x448 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x460 ], rcx
mov [ rsp + 0x468 ], r10
mulx r10, rcx, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x470 ], r10
mov [ rsp + 0x478 ], rcx
mulx rcx, r10, r12
adox rbp, [ rsp + 0x228 ]
mov rdx, r14
mov [ rsp + 0x480 ], rcx
seto cl
mov [ rsp + 0x488 ], r10
mov r10, -0x2 
inc r10
adox rdx, rbx
mov r10, r14
adox r10, rbx
mov byte [ rsp + 0x490 ], cl
movzx rcx, r15b
mov [ rsp + 0x498 ], r10
mov r10, [ rsp + 0x3e0 ]
lea rcx, [ rcx + r10 ]
seto r10b
mov r15, 0x0 
dec r15
movzx r13, r13b
adox r13, r15
adox rdi, [ rsp + 0x430 ]
setc r13b
clc
movzx r9, r9b
adcx r9, r15
adcx rdi, [ rsp + 0x398 ]
setc r9b
clc
movzx r13, r13b
adcx r13, r15
adcx r8, r11
adox rcx, [ rsp + 0x428 ]
setc r11b
clc
movzx r9, r9b
adcx r9, r15
adcx rcx, [ rsp + 0x390 ]
setc r13b
clc
movzx r11, r11b
adcx r11, r15
adcx rdi, [ rsp + 0x450 ]
seto r9b
inc r15
adox r14, r12
adox rdx, [ rsp + 0x468 ]
seto r14b
mov r11, -0x3 
inc r11
adox rdx, [ rsp + 0x158 ]
setc r15b
clc
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx rbp, [ rsp + 0x498 ]
mov r14, 0xffffffffffffffff 
mov byte [ rsp + 0x4a0 ], r13b
mulx r13, r11, r14
mov r14, 0xfdc1767ae2ffffff 
mov [ rsp + 0x4a8 ], rdi
mov byte [ rsp + 0x4b0 ], r9b
mulx r9, rdi, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x4b8 ], r9
mov [ rsp + 0x4c0 ], rdi
mulx rdi, r9, r14
mov r14, 0x2341f27177344 
mov [ rsp + 0x4c8 ], rdi
mov [ rsp + 0x4d0 ], r9
mulx r9, rdi, r14
adox rbp, [ rsp + 0x170 ]
setc r14b
mov [ rsp + 0x4d8 ], r9
movzx r9, byte [ rsp + 0x490 ]
clc
mov [ rsp + 0x4e0 ], rdi
mov rdi, -0x1 
adcx r9, rdi
adcx r8, [ rsp + 0x230 ]
seto r9b
inc rdi
mov rdi, -0x1 
movzx r10, r10b
adox r10, rdi
adox rbx, [ rsp + 0x478 ]
setc r10b
clc
movzx r14, r14b
adcx r14, rdi
adcx r8, rbx
setc r14b
clc
movzx r15, r15b
adcx r15, rdi
adcx rcx, [ rsp + 0x460 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r15
mulx rdi, rbx, r12
mov rdx, r11
mov [ rsp + 0x4e8 ], rdi
setc dil
clc
adcx rdx, r13
mov [ rsp + 0x4f0 ], rbx
movzx rbx, byte [ rsp + 0x4b0 ]
mov byte [ rsp + 0x4f8 ], r14b
movzx r14, byte [ rsp + 0x440 ]
lea rbx, [ rbx + r14 ]
mov r14, r11
adcx r14, r13
mov [ rsp + 0x500 ], r14
mov r14, [ rsp + 0x240 ]
mov [ rsp + 0x508 ], r8
seto r8b
mov byte [ rsp + 0x510 ], r9b
mov r9, 0x0 
dec r9
movzx r10, r10b
adox r10, r9
adox r14, [ rsp + 0x4a8 ]
setc r10b
clc
adcx r11, r15
adcx rdx, rbp
setc r11b
movzx rbp, byte [ rsp + 0x4a0 ]
clc
adcx rbp, r9
adcx rbx, [ rsp + 0x388 ]
adox rcx, [ rsp + 0x258 ]
setc bpl
clc
movzx rdi, dil
adcx rdi, r9
adcx rbx, [ rsp + 0x458 ]
mov rdi, [ rsp + 0x470 ]
setc r9b
clc
mov [ rsp + 0x518 ], rcx
mov rcx, -0x1 
movzx r8, r8b
adcx r8, rcx
adcx rdi, [ rsp + 0x488 ]
mov r8, [ rsp + 0x508 ]
seto cl
mov byte [ rsp + 0x520 ], r10b
movzx r10, byte [ rsp + 0x510 ]
mov [ rsp + 0x528 ], rbx
mov rbx, 0x0 
dec rbx
adox r10, rbx
adox r8, [ rsp + 0x278 ]
setc r10b
movzx rbx, byte [ rsp + 0x4f8 ]
clc
mov byte [ rsp + 0x530 ], cl
mov rcx, -0x1 
adcx rbx, rcx
adcx r14, rdi
seto bl
inc rcx
adox rdx, [ rsp + 0x1a0 ]
setc dil
clc
mov rcx, -0x1 
movzx r11, r11b
adcx r11, rcx
adcx r8, [ rsp + 0x500 ]
mov r11, 0x7bc65c783158aea3 
xchg rdx, r11
mov [ rsp + 0x538 ], r14
mulx r14, rcx, r15
mov r15, 0x6cfc5fd681c52056 
mov rdx, r11
mov byte [ rsp + 0x540 ], bl
mulx rbx, r11, r15
adox r8, [ rsp + 0x1e0 ]
mov r15, 0x7bc65c783158aea3 
mov [ rsp + 0x548 ], rbx
mov [ rsp + 0x550 ], r11
mulx r11, rbx, r15
mov r15, 0x2341f27177344 
mov [ rsp + 0x558 ], r11
mov [ rsp + 0x560 ], rbx
mulx rbx, r11, r15
movzx r15, r9b
movzx rbp, bpl
lea r15, [ r15 + rbp ]
mov rbp, [ rsp + 0x528 ]
seto r9b
mov [ rsp + 0x568 ], rbx
movzx rbx, byte [ rsp + 0x530 ]
mov [ rsp + 0x570 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
adox rbx, r11
adox rbp, [ rsp + 0x250 ]
setc bl
movzx r11, byte [ rsp + 0x520 ]
clc
mov byte [ rsp + 0x578 ], r9b
mov r9, -0x1 
adcx r11, r9
adcx r13, [ rsp + 0x4c0 ]
mov r11, 0x2341f27177344 
xchg rdx, r11
mov [ rsp + 0x580 ], r13
mulx r13, r9, r12
adox r15, [ rsp + 0x268 ]
adcx rcx, [ rsp + 0x4b8 ]
adcx r14, [ rsp + 0x4d0 ]
mov r12, [ rsp + 0x4e0 ]
adcx r12, [ rsp + 0x4c8 ]
mov rdx, [ rsp + 0x4f0 ]
mov [ rsp + 0x588 ], r12
seto r12b
mov [ rsp + 0x590 ], r14
mov r14, 0x0 
dec r14
movzx r10, r10b
adox r10, r14
adox rdx, [ rsp + 0x480 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r11
mov byte [ rsp + 0x598 ], r12b
mulx r12, r14, r10
setc r10b
clc
mov [ rsp + 0x5a0 ], r12
mov r12, -0x1 
movzx rdi, dil
adcx rdi, r12
adcx r11, [ rsp + 0x518 ]
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x5a8 ], rcx
mulx rcx, r12, rdi
adox r9, [ rsp + 0x4e8 ]
mov rdi, 0x0 
adox r13, rdi
mov rdi, [ rsp + 0x288 ]
mov [ rsp + 0x5b0 ], r14
movzx r14, byte [ rsp + 0x540 ]
mov byte [ rsp + 0x5b8 ], r10b
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r14, r10
adox rdi, [ rsp + 0x538 ]
adcx r9, rbp
adox r11, [ rsp + 0x2c0 ]
adcx r13, r15
mov r14, r12
setc bpl
clc
adcx r14, rdx
mov r14, r12
seto dl
inc r10
adox r14, rcx
adox r12, rcx
adcx r14, r8
setc r8b
clc
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx rdi, [ rsp + 0x580 ]
movzx rbx, byte [ rsp + 0x5b8 ]
mov r10, [ rsp + 0x4d8 ]
lea rbx, [ rbx + r10 ]
adox rcx, [ rsp + 0x5b0 ]
adcx r11, [ rsp + 0x5a8 ]
movzx r10, byte [ rsp + 0x320 ]
mov r15, [ rsp + 0x1b0 ]
lea r10, [ r10 + r15 ]
seto r15b
mov [ rsp + 0x5c0 ], rcx
mov rcx, 0x0 
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r9, [ rsp + 0x318 ]
adox r13, [ rsp + 0x310 ]
adcx r9, [ rsp + 0x590 ]
seto dl
movzx rcx, byte [ rsp + 0x578 ]
mov [ rsp + 0x5c8 ], rbx
mov rbx, 0x0 
dec rbx
adox rcx, rbx
adox rdi, [ rsp + 0x308 ]
movzx rcx, byte [ rsp + 0x380 ]
mov rbx, [ rsp + 0x340 ]
lea rcx, [ rcx + rbx ]
adox r11, [ rsp + 0x368 ]
movzx rbx, bpl
mov [ rsp + 0x5d0 ], r11
movzx r11, byte [ rsp + 0x598 ]
lea rbx, [ rbx + r11 ]
mov r11, [ rsp + 0x560 ]
seto bpl
mov [ rsp + 0x5d8 ], rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx r15, r15b
adox r15, rcx
adox r11, [ rsp + 0x5a0 ]
seto r15b
inc rcx
mov rcx, -0x1 
movzx rdx, dl
adox rdx, rcx
adox rbx, r10
seto r10b
inc rcx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox rdi, r12
mov r12, [ rsp + 0x558 ]
seto r8b
dec rcx
movzx r15, r15b
adox r15, rcx
adox r12, [ rsp + 0x550 ]
adcx r13, [ rsp + 0x588 ]
seto dl
inc rcx
mov r15, -0x1 
movzx rbp, bpl
adox rbp, r15
adox r9, [ rsp + 0x360 ]
adox r13, [ rsp + 0x370 ]
setc bpl
seto r15b
mov [ rsp + 0x5e0 ], r12
mov r12, r14
mov [ rsp + 0x5e8 ], r13
mov r13, 0xffffffffffffffff 
sub r12, r13
dec rcx
movzx rbp, bpl
adox rbp, rcx
adox rbx, [ rsp + 0x5c8 ]
seto bpl
mov rcx, rdi
sbb rcx, r13
movzx r13, bpl
movzx r10, r10b
lea r13, [ r13 + r10 ]
mov r10, -0x1 
inc r10
mov rbp, -0x1 
movzx r15, r15b
adox r15, rbp
adox rbx, [ rsp + 0x358 ]
adox r13, [ rsp + 0x5d8 ]
mov r15, [ rsp + 0x5c0 ]
seto r10b
inc rbp
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox r15, [ rsp + 0x5d0 ]
adox r11, r9
seto r8b
mov r9, r15
mov rbp, 0xffffffffffffffff 
sbb r9, rbp
mov rbp, r11
mov [ rsp + 0x5f0 ], rcx
mov rcx, 0xfdc1767ae2ffffff 
sbb rbp, rcx
mov rcx, [ rsp + 0x548 ]
mov [ rsp + 0x5f8 ], r12
mov r12, 0x0 
dec r12
movzx rdx, dl
adox rdx, r12
adox rcx, [ rsp + 0x570 ]
mov rdx, [ rsp + 0x5e8 ]
setc r12b
clc
mov [ rsp + 0x600 ], rbp
mov rbp, -0x1 
movzx r8, r8b
adcx r8, rbp
adcx rdx, [ rsp + 0x5e0 ]
mov r8, [ rsp + 0x568 ]
mov rbp, 0x0 
adox r8, rbp
adcx rcx, rbx
adcx r8, r13
setc bl
movzx r13, r12b
add r13, -0x1
mov r12, rdx
mov r13, 0x7bc65c783158aea3 
sbb r12, r13
mov rbp, rcx
mov r13, 0x6cfc5fd681c52056 
sbb rbp, r13
movzx r13, bl
movzx r10, r10b
lea r13, [ r13 + r10 ]
mov r10, r8
mov rbx, 0x2341f27177344 
sbb r10, rbx
sbb r13, 0x00000000
cmovc r12, rdx
cmovc r9, r15
cmovc r10, r8
cmovc rbp, rcx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x30 ], r10
mov r15, [ rsp + 0x600 ]
cmovc r15, r11
mov [ r13 + 0x18 ], r15
mov [ r13 + 0x20 ], r12
mov r11, [ rsp + 0x5f8 ]
cmovc r11, r14
mov [ r13 + 0x0 ], r11
mov [ r13 + 0x10 ], r9
mov r14, [ rsp + 0x5f0 ]
cmovc r14, rdi
mov [ r13 + 0x8 ], r14
mov [ r13 + 0x28 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1672
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4065
; seed 2001662480271177 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 56419 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=46, initial num_batches=31): 963 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.01706871798507595
; number reverted permutation / tried permutation: 269 / 487 =55.236%
; number reverted decision / tried decision: 265 / 512 =51.758%
; validated in 212.105s
