SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1520
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rcx
mulx rcx, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r15
mulx r15, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r10
mulx r10, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r13
mulx r13, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], r15
mulx r15, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r11
mulx r11, rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r12
mulx r12, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rbp
mov [ rsp + 0x58 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], rbx
mov [ rsp + 0x68 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x70 ], rcx
mov [ rsp + 0x78 ], r9
mulx r9, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r9
mov [ rsp + 0x88 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rcx
mov [ rsp + 0x98 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], r8
mulx r8, rcx, [ rsi + 0x20 ]
test al, al
adox rax, r9
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb0 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], rax
mov [ rsp + 0xc0 ], rcx
mulx rcx, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], r8
mulx r8, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xd8 ], r8
mov [ rsp + 0xe0 ], r9
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r9
mov [ rsp + 0xf0 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], r9
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x108 ], r8
mov [ rsp + 0x110 ], r15
mulx r15, r8, [ rsi + 0x10 ]
adox rbp, r11
adcx rax, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r11, [ rsi + 0x18 ]
adox r11, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x118 ], rax
mulx rax, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r11
mov [ rsp + 0x128 ], rbp
mulx rbp, r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x130 ], rax
mov [ rsp + 0x138 ], r15
mulx r15, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x140 ], r15
mov [ rsp + 0x148 ], rax
mulx rax, r15, [ rsi + 0x8 ]
adox r15, r9
adcx r11, rcx
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rsi + 0x8 ]
adcx r8, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r8
mulx r8, rbp, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0x158 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, r12
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x160 ], rcx
mulx rcx, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r11
mov [ rsp + 0x170 ], r15
mulx r15, r11, [ rsi + 0x28 ]
setc dl
clc
adcx r14, r8
mov r8b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x178 ], r14
mov [ rsp + 0x180 ], rcx
mulx rcx, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x188 ], rbp
mov [ rsp + 0x190 ], r15
mulx r15, rbp, rdx
adcx r14, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x198 ], r14
mulx r14, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x1a0 ], r8b
mov [ rsp + 0x1a8 ], rax
mulx rax, r8, [ rsi + 0x0 ]
adcx r10, rcx
adcx rbx, r14
adox r13, r9
mov rdx, [ rsp + 0x110 ]
adox rdx, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0x78 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, rcx, [ rsi + 0x30 ]
adcx r11, r15
seto dl
mov r15, -0x2 
inc r15
adox r14, [ rsp + 0x70 ]
mov r15, [ rsp + 0x60 ]
adox r15, [ rsp + 0x68 ]
mov [ rsp + 0x1b0 ], r11
mov r11, [ rsp + 0x48 ]
adox r11, [ rsp + 0x58 ]
mov [ rsp + 0x1b8 ], rbp
seto bpl
mov [ rsp + 0x1c0 ], r11
mov r11, -0x2 
inc r11
adox rdi, [ rsp + 0xd0 ]
mov r11b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c8 ], r15
mov [ rsp + 0x1d0 ], r14
mulx r14, r15, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1d8 ], rbx
mov [ rsp + 0x1e0 ], r10
mulx r10, rbx, r15
mov rdx, [ rsp + 0x40 ]
mov [ rsp + 0x1e8 ], rcx
setc cl
clc
mov [ rsp + 0x1f0 ], rdi
mov rdi, -0x1 
movzx r12, r12b
adcx r12, rdi
adcx rdx, [ rsp + 0x1a8 ]
mov r12, [ rsp + 0x148 ]
adcx r12, [ rsp + 0x38 ]
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1f8 ], r9
mov [ rsp + 0x200 ], r13
mulx r13, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x208 ], r12
mov [ rsp + 0x210 ], rdi
mulx rdi, r12, [ rsi + 0x28 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x218 ], r10
mov [ rsp + 0x220 ], rbx
mulx rbx, r10, r15
mov rdx, [ rsp + 0x140 ]
mov [ rsp + 0x228 ], rbx
mov rbx, 0x0 
adcx rdx, rbx
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x230 ], rbx
mov [ rsp + 0x238 ], r10
mulx r10, rbx, r15
mov rdx, [ rsp + 0x138 ]
mov [ rsp + 0x240 ], r10
movzx r10, byte [ rsp + 0x1a0 ]
clc
mov [ rsp + 0x248 ], rbx
mov rbx, -0x1 
adcx r10, rbx
adcx rdx, [ rsp + 0x28 ]
mov r10, [ rsp + 0x20 ]
setc bl
clc
mov [ rsp + 0x250 ], rdx
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx r10, [ rsp + 0x18 ]
mov r11, [ rsp + 0x130 ]
adox r11, [ rsp + 0x10 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x258 ], r11
mov [ rsp + 0x260 ], r10
mulx r10, r11, r15
mov rdx, [ rsp - 0x8 ]
mov [ rsp + 0x268 ], r10
setc r10b
clc
mov [ rsp + 0x270 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx rdx, [ rsp + 0x98 ]
mov rbx, [ rsp + 0x88 ]
setc r11b
clc
mov [ rsp + 0x278 ], rdx
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx rbx, [ rsp + 0x50 ]
seto bpl
inc rdx
mov rdx, -0x1 
movzx r10, r10b
adox r10, rdx
adox r12, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x280 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
mov rdx, [ rsp + 0xe0 ]
adcx rdx, [ rsp + 0x80 ]
mov [ rsp + 0x288 ], rdx
movzx rdx, cl
mov [ rsp + 0x290 ], r12
mov r12, [ rsp + 0x190 ]
lea rdx, [ rdx + r12 ]
setc r12b
clc
mov rcx, -0x1 
movzx rbp, bpl
adcx rbp, rcx
adcx r10, [ rsp - 0x18 ]
adcx r9, rbx
adox rdi, [ rsp + 0xf0 ]
adcx r13, [ rsp + 0xc8 ]
setc bpl
clc
adcx r8, r14
adcx rax, [ rsp + 0x100 ]
mov r14, [ rsp + 0xf8 ]
adcx r14, [ rsp - 0x20 ]
mov rbx, [ rsp - 0x28 ]
adcx rbx, [ rsp - 0x30 ]
mov rcx, [ rsp + 0x90 ]
mov [ rsp + 0x298 ], rdx
seto dl
mov [ rsp + 0x2a0 ], r13
mov r13, -0x1 
inc r13
mov r13, -0x1 
movzx r11, r11b
adox r11, r13
adox rcx, [ rsp + 0x8 ]
mov r11, [ rsp + 0x188 ]
adcx r11, [ rsp - 0x38 ]
movzx r13, dl
mov [ rsp + 0x2a8 ], r9
mov r9, [ rsp + 0xe8 ]
lea r13, [ r13 + r9 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x2b0 ], r13
mulx r13, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x2b8 ], r10
mov [ rsp + 0x2c0 ], rdi
mulx rdi, r10, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x2c8 ], rcx
mov rcx, 0x0 
adox rdx, rcx
mov rcx, [ rsp + 0xd8 ]
mov [ rsp + 0x2d0 ], rdx
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox rcx, [ rsp - 0x40 ]
seto r12b
inc rdx
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox r9, [ rsp + 0xc0 ]
mov rbp, r15
seto dl
mov [ rsp + 0x2d8 ], rcx
mov rcx, -0x2 
inc rcx
adox rbp, [ rsp + 0x220 ]
movzx rbp, dl
lea rbp, [ rbp + r13 ]
adcx r10, [ rsp + 0x180 ]
mov r13, 0x0 
adcx rdi, r13
movzx rdx, r12b
mov r13, [ rsp - 0x48 ]
lea rdx, [ rdx + r13 ]
mov r13, [ rsp + 0x218 ]
mov r12, r13
clc
adcx r12, [ rsp + 0x220 ]
mov rcx, r13
adcx rcx, [ rsp + 0x220 ]
adcx r13, [ rsp + 0x248 ]
mov [ rsp + 0x2e0 ], rdx
mov rdx, [ rsp + 0x270 ]
adcx rdx, [ rsp + 0x240 ]
adox r12, r8
adox rcx, rax
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x2e8 ], rbp
mulx rbp, rax, r15
setc r15b
clc
adcx r12, [ rsp + 0xa0 ]
adox r13, r14
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x2f0 ], r9
mulx r9, r14, r12
mov rdx, r14
mov [ rsp + 0x2f8 ], rdi
seto dil
mov [ rsp + 0x300 ], r10
mov r10, -0x2 
inc r10
adox rdx, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x308 ], rbp
mulx rbp, r10, r12
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x310 ], rbp
mov [ rsp + 0x318 ], r11
mulx r11, rbp, r12
adcx rcx, [ rsp + 0xb8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x320 ], r11
mov [ rsp + 0x328 ], rbp
mulx rbp, r11, r12
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x330 ], rbp
mov [ rsp + 0x338 ], r11
mulx r11, rbp, r12
mov r12, r14
setc dl
clc
adcx r12, r9
adcx r14, r9
adcx rbp, r9
adcx r10, r11
setc r9b
clc
mov r11, -0x1 
movzx r15, r15b
adcx r15, r11
adcx rax, [ rsp + 0x268 ]
setc r15b
clc
movzx rdx, dl
adcx rdx, r11
adcx r13, [ rsp + 0x128 ]
setc dl
clc
movzx rdi, dil
adcx rdi, r11
adcx rbx, r8
adcx rax, [ rsp + 0x318 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, r11
adcx rbx, [ rsp + 0x120 ]
adox r12, rcx
adox r14, r13
seto dil
inc r11
adox r12, [ rsp + 0x108 ]
mov rcx, 0xffffffffffffffff 
mov rdx, r12
mulx r13, r12, rcx
adcx rax, [ rsp + 0x170 ]
seto r11b
mov rcx, 0x0 
dec rcx
movzx rdi, dil
adox rdi, rcx
adox rbx, rbp
setc bpl
clc
movzx r11, r11b
adcx r11, rcx
adcx r14, [ rsp + 0x118 ]
adox r10, rax
mov rdi, 0x6cfc5fd681c52056 
mulx rax, r11, rdi
mov rcx, [ rsp + 0x238 ]
setc dil
clc
mov [ rsp + 0x340 ], rax
mov rax, -0x1 
movzx r15, r15b
adcx r15, rax
adcx rcx, [ rsp + 0x308 ]
mov r15, 0x2341f27177344 
mov [ rsp + 0x348 ], r11
mulx r11, rax, r15
mov r15, [ rsp + 0x228 ]
mov [ rsp + 0x350 ], r11
mov r11, 0x0 
adcx r15, r11
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x358 ], rax
mov [ rsp + 0x360 ], r14
mulx r14, rax, r11
mov r11, [ rsp + 0x328 ]
clc
mov [ rsp + 0x368 ], r14
mov r14, -0x1 
movzx r9, r9b
adcx r9, r14
adcx r11, [ rsp + 0x310 ]
seto r9b
inc r14
mov r14, -0x1 
movzx r8, r8b
adox r8, r14
adox rcx, [ rsp + 0x300 ]
mov r8, [ rsp + 0x320 ]
adcx r8, [ rsp + 0x338 ]
adox r15, [ rsp + 0x2f8 ]
setc r14b
clc
mov [ rsp + 0x370 ], r8
mov r8, -0x1 
movzx rdi, dil
adcx rdi, r8
adcx rbx, [ rsp + 0x168 ]
seto dil
inc r8
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox rcx, [ rsp + 0x210 ]
adcx r10, [ rsp + 0x150 ]
mov rbp, r12
setc r8b
clc
adcx rbp, r13
mov byte [ rsp + 0x378 ], r8b
mov r8, r12
adcx r8, r13
mov byte [ rsp + 0x380 ], dil
mov rdi, 0x7bc65c783158aea3 
mov [ rsp + 0x388 ], r10
mov [ rsp + 0x390 ], r8
mulx r8, r10, rdi
seto dil
mov [ rsp + 0x398 ], r8
mov r8, -0x2 
inc r8
adox r12, rdx
movzx r12, r14b
mov rdx, [ rsp + 0x330 ]
lea r12, [ r12 + rdx ]
seto dl
inc r8
mov r14, -0x1 
movzx rdi, dil
adox rdi, r14
adox r15, [ rsp + 0x208 ]
seto dil
dec r8
movzx r9, r9b
adox r9, r8
adox rcx, r11
seto r14b
inc r8
mov r9, -0x1 
movzx rdx, dl
adox rdx, r9
adox rbp, [ rsp + 0x360 ]
adcx rax, r13
adcx r10, [ rsp + 0x368 ]
adox rbx, [ rsp + 0x390 ]
setc r13b
clc
adcx rbp, [ rsp + 0x30 ]
mov r11, 0xfdc1767ae2ffffff 
mov rdx, rbp
mulx r8, rbp, r11
adox rax, [ rsp + 0x388 ]
setc r9b
clc
mov r11, -0x1 
movzx r14, r14b
adcx r14, r11
adcx r15, [ rsp + 0x370 ]
movzx r14, byte [ rsp + 0x380 ]
setc r11b
clc
mov [ rsp + 0x3a0 ], rax
mov rax, -0x1 
movzx rdi, dil
adcx rdi, rax
adcx r14, [ rsp + 0x230 ]
setc dil
clc
movzx r11, r11b
adcx r11, rax
adcx r14, r12
mov r12, [ rsp + 0x348 ]
seto r11b
inc rax
mov rax, -0x1 
movzx r13, r13b
adox r13, rax
adox r12, [ rsp + 0x398 ]
mov r13, [ rsp + 0x358 ]
adox r13, [ rsp + 0x340 ]
mov rax, 0x6cfc5fd681c52056 
mov [ rsp + 0x3a8 ], r13
mov [ rsp + 0x3b0 ], r12
mulx r12, r13, rax
mov rax, 0x7bc65c783158aea3 
mov [ rsp + 0x3b8 ], r12
mov [ rsp + 0x3c0 ], r13
mulx r13, r12, rax
mov rax, [ rsp + 0x350 ]
mov [ rsp + 0x3c8 ], r13
mov r13, 0x0 
adox rax, r13
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x3d0 ], rax
mov [ rsp + 0x3d8 ], r12
mulx r12, rax, r13
mov r13, rax
mov [ rsp + 0x3e0 ], r8
mov r8, -0x2 
inc r8
adox r13, rdx
mov r13, rax
setc r8b
clc
adcx r13, r12
adcx rax, r12
adcx rbp, r12
setc r12b
clc
mov [ rsp + 0x3e8 ], rbp
mov rbp, -0x1 
movzx r9, r9b
adcx r9, rbp
adcx rbx, [ rsp + 0x160 ]
seto r9b
movzx rbp, byte [ rsp + 0x378 ]
mov [ rsp + 0x3f0 ], rax
mov rax, 0x0 
dec rax
adox rbp, rax
adox rcx, [ rsp + 0x250 ]
seto bpl
inc rax
mov rax, -0x1 
movzx r9, r9b
adox r9, rax
adox rbx, r13
movzx r9, r8b
movzx rdi, dil
lea r9, [ r9 + rdi ]
setc dil
clc
movzx rbp, bpl
adcx rbp, rax
adcx r15, [ rsp + 0x278 ]
adcx r14, [ rsp + 0x2c8 ]
adcx r9, [ rsp + 0x2d0 ]
setc r8b
clc
movzx r11, r11b
adcx r11, rax
adcx rcx, r10
mov r10, [ rsp + 0x3e0 ]
seto r11b
inc rax
mov r13, -0x1 
movzx r12, r12b
adox r12, r13
adox r10, [ rsp + 0x3d8 ]
mov r12, [ rsp + 0x3c8 ]
adox r12, [ rsp + 0x3c0 ]
mov rbp, [ rsp + 0x200 ]
seto al
inc r13
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox rbp, [ rsp + 0x3a0 ]
mov rdi, 0x2341f27177344 
mov [ rsp + 0x3f8 ], r12
mulx r12, r13, rdi
adcx r15, [ rsp + 0x3b0 ]
adox rcx, [ rsp + 0x1f8 ]
seto dl
mov rdi, -0x2 
inc rdi
adox rbx, [ rsp + 0xb0 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov byte [ rsp + 0x400 ], r8b
mov [ rsp + 0x408 ], r12
mulx r12, r8, rbx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x410 ], r12
mov [ rsp + 0x418 ], r8
mulx r8, r12, rbx
seto dl
mov [ rsp + 0x420 ], r8
mov r8, 0x0 
dec r8
movzx rax, al
adox rax, r8
adox r13, [ rsp + 0x3b8 ]
setc al
clc
movzx r11, r11b
adcx r11, r8
adcx rbp, [ rsp + 0x3f0 ]
adcx rcx, [ rsp + 0x3e8 ]
seto r11b
inc r8
mov r8, -0x1 
movzx rdi, dil
adox rdi, r8
adox r15, [ rsp + 0x260 ]
mov rdi, 0x6cfc5fd681c52056 
xchg rdx, rbx
mov [ rsp + 0x428 ], r12
mulx r12, r8, rdi
adcx r10, r15
setc r15b
clc
mov rdi, -0x1 
movzx rax, al
adcx rax, rdi
adcx r14, [ rsp + 0x3a8 ]
adcx r9, [ rsp + 0x3d0 ]
movzx rax, r11b
mov rdi, [ rsp + 0x408 ]
lea rax, [ rax + rdi ]
movzx rdi, byte [ rsp + 0x400 ]
mov r11, 0x0 
adcx rdi, r11
adox r14, [ rsp + 0x290 ]
adox r9, [ rsp + 0x2c0 ]
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x430 ], rax
mov [ rsp + 0x438 ], rdi
mulx rdi, rax, r11
mov r11, rax
clc
adcx r11, rdi
mov [ rsp + 0x440 ], r12
mov r12, rax
adcx r12, rdi
mov [ rsp + 0x448 ], r8
seto r8b
mov [ rsp + 0x450 ], r12
mov r12, 0x0 
dec r12
movzx r15, r15b
adox r15, r12
adox r14, [ rsp + 0x3f8 ]
setc r15b
clc
movzx rbx, bl
adcx rbx, r12
adcx rbp, [ rsp + 0x1f0 ]
adcx rcx, [ rsp + 0x258 ]
adcx r10, [ rsp + 0x2b8 ]
setc bl
clc
movzx r15, r15b
adcx r15, r12
adcx rdi, [ rsp + 0x418 ]
adox r13, r9
seto r9b
inc r12
adox rax, rdx
adox r11, rbp
adox rcx, [ rsp + 0x450 ]
setc al
clc
mov r15, -0x1 
movzx rbx, bl
adcx rbx, r15
adcx r14, [ rsp + 0x2a8 ]
seto bpl
mov rbx, -0x3 
inc rbx
adox r11, [ rsp + 0x158 ]
adcx r13, [ rsp + 0x2a0 ]
setc r12b
clc
movzx rbp, bpl
adcx rbp, r15
adcx r10, rdi
mov rdi, [ rsp + 0x428 ]
seto bpl
inc r15
mov r15, -0x1 
movzx rax, al
adox rax, r15
adox rdi, [ rsp + 0x410 ]
mov rax, [ rsp + 0x420 ]
adox rax, [ rsp + 0x448 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r15
mov [ rsp + 0x458 ], rax
mulx rax, rbx, r11
mov rdx, 0x2341f27177344 
mov [ rsp + 0x460 ], rax
mov [ rsp + 0x468 ], r13
mulx r13, rax, r15
mov r15, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x470 ], rbx
mulx rbx, r11, r15
mov r15, r11
mov byte [ rsp + 0x478 ], r12b
seto r12b
mov [ rsp + 0x480 ], r10
mov r10, -0x2 
inc r10
adox r15, rbx
seto r10b
mov [ rsp + 0x488 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r12, r12b
adox r12, r15
adox rax, [ rsp + 0x440 ]
mov r12, 0x2341f27177344 
mov [ rsp + 0x490 ], rax
mulx rax, r15, r12
mov r12, [ rsp + 0x2b0 ]
mov [ rsp + 0x498 ], rax
setc al
clc
mov [ rsp + 0x4a0 ], r15
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r12, [ rsp + 0x438 ]
mov r8, 0x0 
adox r13, r8
inc r15
mov r8, -0x1 
movzx rax, al
adox rax, r8
adox r14, rdi
mov rax, 0xfdc1767ae2ffffff 
mulx r15, rdi, rax
seto r8b
mov rax, 0x0 
dec rax
movzx r9, r9b
adox r9, rax
adox r12, [ rsp + 0x430 ]
mov r9, r11
seto al
mov [ rsp + 0x4a8 ], r13
mov r13, -0x2 
inc r13
adox r9, rdx
mov r9, rbx
seto r13b
mov byte [ rsp + 0x4b0 ], r8b
mov r8, 0x0 
dec r8
movzx r10, r10b
adox r10, r8
adox r9, r11
seto r11b
inc r8
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rcx, [ rsp + 0x178 ]
seto bpl
dec r8
movzx r13, r13b
adox r13, r8
adox rcx, [ rsp + 0x488 ]
seto r10b
inc r8
mov r13, -0x1 
movzx r11, r11b
adox r11, r13
adox rbx, rdi
setc dil
clc
adcx rcx, [ rsp + 0x1e8 ]
mov r11, [ rsp + 0x480 ]
setc r8b
clc
movzx rbp, bpl
adcx rbp, r13
adcx r11, [ rsp + 0x198 ]
mov rbp, 0x7bc65c783158aea3 
mov [ rsp + 0x4b8 ], rbx
mulx rbx, r13, rbp
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x4c0 ], r8b
mulx r8, rbp, rcx
adox r13, r15
mov r15, 0x7bc65c783158aea3 
mov rdx, r15
mov [ rsp + 0x4c8 ], r13
mulx r13, r15, rcx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x4d0 ], r13
mov [ rsp + 0x4d8 ], r15
mulx r15, r13, rcx
adcx r14, [ rsp + 0x1e0 ]
setc dl
mov [ rsp + 0x4e0 ], r15
movzx r15, byte [ rsp + 0x478 ]
clc
mov [ rsp + 0x4e8 ], r13
mov r13, -0x1 
adcx r15, r13
adcx r12, [ rsp + 0x2f0 ]
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, r15
mov [ rsp + 0x4f0 ], r14
mulx r14, r13, rcx
mov rdx, rbp
mov [ rsp + 0x4f8 ], r14
setc r14b
clc
adcx rdx, r8
mov [ rsp + 0x500 ], rdx
mov rdx, rbp
adcx rdx, r8
mov [ rsp + 0x508 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0x510 ], r9
mov [ rsp + 0x518 ], r11
mulx r11, r9, rcx
movzx rdx, al
movzx rdi, dil
lea rdx, [ rdx + rdi ]
adox rbx, [ rsp + 0x470 ]
adcx r13, r8
mov rdi, [ rsp + 0x458 ]
seto al
movzx r8, byte [ rsp + 0x4b0 ]
mov [ rsp + 0x520 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r8, rbx
adox rdi, [ rsp + 0x468 ]
adox r12, [ rsp + 0x490 ]
setc r8b
clc
movzx r14, r14b
adcx r14, rbx
adcx rdx, [ rsp + 0x2e8 ]
adox rdx, [ rsp + 0x4a8 ]
seto r14b
inc rbx
mov rbx, -0x1 
movzx r15, r15b
adox r15, rbx
adox rdi, [ rsp + 0x1d8 ]
mov r15, [ rsp + 0x518 ]
seto bl
mov byte [ rsp + 0x528 ], r14b
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx r10, r10b
adox r10, r14
adox r15, [ rsp + 0x510 ]
seto r10b
movzx r14, byte [ rsp + 0x4c0 ]
mov [ rsp + 0x530 ], rdx
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
adox r14, rdx
adox r15, [ rsp + 0x1d0 ]
mov r14, [ rsp + 0x4f0 ]
setc dl
clc
mov [ rsp + 0x538 ], r12
mov r12, -0x1 
movzx r10, r10b
adcx r10, r12
adcx r14, [ rsp + 0x4b8 ]
adcx rdi, [ rsp + 0x4c8 ]
adox r14, [ rsp + 0x1c8 ]
setc r10b
clc
adcx rbp, rcx
mov rbp, [ rsp + 0x460 ]
setc cl
clc
movzx rax, al
adcx rax, r12
adcx rbp, [ rsp + 0x4a0 ]
adox rdi, [ rsp + 0x1c0 ]
mov rax, [ rsp + 0x4d8 ]
seto r12b
mov byte [ rsp + 0x540 ], dl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox rax, [ rsp + 0x4f8 ]
mov r8, [ rsp + 0x498 ]
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsp + 0x4d0 ]
adox rdx, [ rsp + 0x4e8 ]
clc
mov [ rsp + 0x548 ], r8
mov r8, -0x1 
movzx rcx, cl
adcx rcx, r8
adcx r15, [ rsp + 0x500 ]
adox r9, [ rsp + 0x4e0 ]
adcx r14, [ rsp + 0x508 ]
adcx r13, rdi
mov rcx, 0x0 
adox r11, rcx
setc dil
mov r8, r15
mov [ rsp + 0x550 ], r11
mov r11, 0xffffffffffffffff 
sub r8, r11
mov rcx, [ rsp + 0x538 ]
mov r11, 0x0 
dec r11
movzx rbx, bl
adox rbx, r11
adox rcx, [ rsp + 0x1b8 ]
seto bl
mov r11, r14
mov [ rsp + 0x558 ], r8
mov r8, 0xffffffffffffffff 
sbb r11, r8
mov r8, [ rsp + 0x1b0 ]
mov [ rsp + 0x560 ], r11
mov r11, 0x0 
dec r11
movzx rbx, bl
adox rbx, r11
adox r8, [ rsp + 0x530 ]
seto bl
inc r11
mov r11, -0x1 
movzx r10, r10b
adox r10, r11
adox rcx, [ rsp + 0x520 ]
setc r10b
clc
movzx r12, r12b
adcx r12, r11
adcx rcx, [ rsp + 0x280 ]
adox rbp, r8
adcx rbp, [ rsp + 0x288 ]
movzx r12, byte [ rsp + 0x528 ]
movzx r8, byte [ rsp + 0x540 ]
lea r12, [ r12 + r8 ]
seto r8b
inc r11
mov r11, -0x1 
movzx rbx, bl
adox rbx, r11
adox r12, [ rsp + 0x298 ]
seto bl
inc r11
mov r11, -0x1 
movzx rdi, dil
adox rdi, r11
adox rcx, rax
setc al
seto dil
movzx r11, r10b
add r11, -0x1
mov r10, r13
mov r11, 0xffffffffffffffff 
sbb r10, r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx rdi, dil
adox rdi, r11
adox rbp, rdx
seto dl
mov rdi, rcx
mov r11, 0xfdc1767ae2ffffff 
sbb rdi, r11
mov r11, rbp
mov [ rsp + 0x568 ], rdi
mov rdi, 0x7bc65c783158aea3 
sbb r11, rdi
mov rdi, 0x0 
dec rdi
movzx r8, r8b
adox r8, rdi
adox r12, [ rsp + 0x548 ]
movzx r8, bl
mov rdi, 0x0 
adox r8, rdi
dec rdi
movzx rax, al
adox rax, rdi
adox r12, [ rsp + 0x2d8 ]
setc al
clc
movzx rdx, dl
adcx rdx, rdi
adcx r12, r9
adox r8, [ rsp + 0x2e0 ]
adcx r8, [ rsp + 0x550 ]
seto r9b
adc r9b, 0x0
movzx r9, r9b
movzx rbx, al
add rbx, -0x1
mov rax, r12
mov rbx, 0x6cfc5fd681c52056 
sbb rax, rbx
mov rdx, r8
mov rdi, 0x2341f27177344 
sbb rdx, rdi
movzx rbx, r9b
sbb rbx, 0x00000000
cmovc r11, rbp
cmovc rax, r12
cmovc r10, r13
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], r10
mov r13, [ rsp + 0x558 ]
cmovc r13, r15
mov [ rbx + 0x20 ], r11
mov [ rbx + 0x28 ], rax
mov r15, [ rsp + 0x560 ]
cmovc r15, r14
cmovc rdx, r8
mov [ rbx + 0x8 ], r15
mov r14, [ rsp + 0x568 ]
cmovc r14, rcx
mov [ rbx + 0x30 ], rdx
mov [ rbx + 0x0 ], r13
mov [ rbx + 0x18 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1520
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4072
; seed 3371548711473103 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 51997 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=47, initial num_batches=31): 922 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.017731792218781853
; number reverted permutation / tried permutation: 330 / 532 =62.030%
; number reverted decision / tried decision: 276 / 467 =59.101%
; validated in 191.046s
