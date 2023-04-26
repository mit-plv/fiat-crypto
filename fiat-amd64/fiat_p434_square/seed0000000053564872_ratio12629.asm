SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1248
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], rbx
mulx rbx, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], rcx
mov [ rsp - 0x8 ], r11
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], rcx
mulx rcx, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r13
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r12
mov [ rsp + 0x28 ], r11
mulx r11, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r12
mov [ rsp + 0x38 ], r11
mulx r11, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r11
mov [ rsp + 0x48 ], r12
mulx r12, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r12
mov [ rsp + 0x58 ], r11
mulx r11, r12, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x60 ], r13
mov [ rsp + 0x68 ], rcx
mulx rcx, r13, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x70 ], r9
mov [ rsp + 0x78 ], rbx
mulx rbx, r9, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r14
mov [ rsp + 0x88 ], r10
mulx r10, r14, rdx
mov rdx, r13
test al, al
adox rdx, rcx
mov [ rsp + 0x90 ], r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x98 ], r14
mov [ rsp + 0xa0 ], rax
mulx rax, r14, [ rsi + 0x10 ]
adcx rbp, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], rax
mulx rax, r11, [ rsi + 0x28 ]
adcx r14, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], rax
mulx rax, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], rax
mulx rax, rdi, [ rsi + 0x30 ]
mov rdx, r13
mov [ rsp + 0xc8 ], rax
setc al
clc
adcx rdx, r12
adox r13, rcx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xd0 ], rdi
mov [ rsp + 0xd8 ], r11
mulx r11, rdi, r12
adox rdi, rcx
adcx r10, rbp
adox r9, r11
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ rsi + 0x0 ]
setc dl
clc
adcx r8, rbp
seto r11b
mov rbp, -0x2 
inc rbp
adox rcx, r10
seto r10b
inc rbp
mov rbp, -0x1 
movzx rdx, dl
adox rdx, rbp
adox r14, r13
mov r13, 0x6cfc5fd681c52056 
mov rdx, r13
mulx rbp, r13, r12
mov rdx, 0x2341f27177344 
mov [ rsp + 0xe0 ], r9
mov [ rsp + 0xe8 ], rdi
mulx rdi, r9, r12
mov r12, 0xffffffffffffffff 
mov rdx, r12
mov [ rsp + 0xf0 ], rdi
mulx rdi, r12, rcx
mov rdx, r12
mov byte [ rsp + 0xf8 ], al
seto al
mov [ rsp + 0x100 ], rdi
mov rdi, -0x2 
inc rdi
adox rdx, rcx
seto dl
inc rdi
mov rdi, -0x1 
movzx r11, r11b
adox r11, rdi
adox rbx, r13
mov r11b, dl
mov rdx, [ rsi + 0x18 ]
mulx rdi, r13, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x108 ], rbx
mov rbx, -0x2 
inc rbx
adox r15, [ rsp + 0xa0 ]
mov rbx, [ rsp + 0x88 ]
adox rbx, [ rsp + 0x80 ]
mov [ rsp + 0x110 ], rbx
setc bl
clc
mov [ rsp + 0x118 ], r15
mov r15, -0x1 
movzx r10, r10b
adcx r10, r15
adcx r14, r8
adox r13, [ rsp + 0x78 ]
setc r8b
clc
movzx rdx, dl
adcx rdx, r15
adcx rbp, r9
mov r10, r12
seto r9b
inc r15
adox r10, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x120 ], r13
mulx r13, r15, [ rsi + 0x0 ]
setc dl
clc
mov byte [ rsp + 0x128 ], r8b
mov r8, -0x1 
movzx r11, r11b
adcx r11, r8
adcx r14, r10
mov r11b, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, r10, [ rsi + 0x8 ]
seto dl
mov byte [ rsp + 0x130 ], r11b
mov r11, -0x2 
inc r11
adox r15, r14
mov r14b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], rbp
mulx rbp, r11, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x140 ], rbp
mov byte [ rsp + 0x148 ], al
mulx rax, rbp, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x150 ], rax
mov [ rsp + 0x158 ], rbp
mulx rbp, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x160 ], r14b
mov [ rsp + 0x168 ], r8
mulx r8, r14, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp + 0x170 ], r8
mov r8, -0x1 
movzx r9, r9b
adcx r9, r8
adcx rdi, r11
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mulx r8, r11, r15
seto dl
mov [ rsp + 0x178 ], rdi
mov rdi, 0x0 
dec rdi
movzx rbx, bl
adox rbx, rdi
adox rax, [ rsp + 0x70 ]
setc bl
clc
adcx r13, [ rsp + 0x68 ]
adox r10, rbp
adox r14, [ rsp + 0x168 ]
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x180 ], bl
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x188 ], rbx
mov [ rsp + 0x190 ], r13
mulx r13, rbx, rdx
adcx rbx, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x198 ], rbx
mov byte [ rsp + 0x1a0 ], bpl
mulx rbp, rbx, [ rsi + 0x10 ]
adcx rbx, r13
seto dl
movzx r13, byte [ rsp + 0x160 ]
mov [ rsp + 0x1a8 ], rbx
mov rbx, 0x0 
dec rbx
adox r13, rbx
adox r12, [ rsp + 0x100 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r13
mov [ rsp + 0x1b0 ], r12
mulx r12, rbx, rcx
adox rbx, [ rsp + 0x100 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b8 ], rbx
mov byte [ rsp + 0x1c0 ], r9b
mulx r9, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x1c8 ], r13b
mov [ rsp + 0x1d0 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1d8 ], r10
mov [ rsp + 0x1e0 ], rax
mulx rax, r10, rcx
adcx rdi, rbp
adox r10, r12
mov rbp, 0x2341f27177344 
mov rdx, r15
mulx r12, r15, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1e8 ], r12
mov [ rsp + 0x1f0 ], r15
mulx r15, r12, [ rsi + 0x20 ]
setc dl
clc
adcx rbx, [ rsp + 0x38 ]
mov [ rsp + 0x1f8 ], rbx
mov bl, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x200 ], rdi
mov [ rsp + 0x208 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
adcx rdi, r9
seto dl
movzx r9, byte [ rsp + 0xf8 ]
mov [ rsp + 0x210 ], rdi
mov rdi, 0x0 
dec rdi
adox r9, rdi
adox r13, [ rsp + 0xa8 ]
setc r9b
movzx rdi, byte [ rsp + 0x148 ]
clc
mov byte [ rsp + 0x218 ], bl
mov rbx, -0x1 
adcx rdi, rbx
adcx r13, [ rsp + 0xe8 ]
setc dil
clc
movzx r9, r9b
adcx r9, rbx
adcx rax, [ rsp + 0x98 ]
mov r9b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x220 ], rax
mulx rax, rbx, [ rsi + 0x28 ]
adox r12, r14
adox rbx, r15
adox rax, [ rsp + 0x28 ]
seto dl
mov r14, -0x1 
inc r14
mov r15, -0x1 
movzx rdi, dil
adox rdi, r15
adox r12, [ rsp + 0xe0 ]
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mulx r15, r14, [ rsi + 0x18 ]
adox rbx, [ rsp + 0x108 ]
adox rax, [ rsp + 0x138 ]
adcx r14, [ rsp + 0x90 ]
adcx r15, [ rsp + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x228 ], r15
mov [ rsp + 0x230 ], r14
mulx r14, r15, rbp
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x238 ], r9b
mov [ rsp + 0x240 ], r10
mulx r10, r9, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x248 ], r10
mov [ rsp + 0x250 ], rax
mulx rax, r10, [ rsi + 0x30 ]
adcx r10, [ rsp + 0x18 ]
mov rdx, r11
mov [ rsp + 0x258 ], r10
setc r10b
clc
adcx rdx, r8
mov [ rsp + 0x260 ], rdx
mov rdx, r11
adcx rdx, r8
adcx r15, r8
movzx r8, byte [ rsp + 0x130 ]
mov [ rsp + 0x268 ], r15
mov r15, [ rsp + 0xf0 ]
lea r8, [ r8 + r15 ]
setc r15b
mov [ rsp + 0x270 ], rdx
movzx rdx, byte [ rsp + 0x128 ]
clc
mov [ rsp + 0x278 ], r8
mov r8, -0x1 
adcx rdx, r8
adcx r13, [ rsp + 0x1e0 ]
adcx r12, [ rsp + 0x1d8 ]
adcx rbx, [ rsp + 0x1d0 ]
movzx rdx, r10b
lea rdx, [ rdx + rax ]
setc al
clc
movzx r15, r15b
adcx r15, r8
adcx r14, [ rsp + 0x158 ]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, [ rsi + 0x28 ]
adcx r9, [ rsp + 0x150 ]
movzx rdx, dil
mov [ rsp + 0x280 ], r10
mov r10, [ rsp + 0x10 ]
lea rdx, [ rdx + r10 ]
adox rdx, [ rsp + 0x278 ]
mov r10, [ rsp - 0x8 ]
setc dil
mov [ rsp + 0x288 ], r9
movzx r9, byte [ rsp + 0x1c8 ]
clc
mov [ rsp + 0x290 ], r14
mov r14, -0x1 
adcx r9, r14
adcx r10, [ rsp + 0x170 ]
seto r9b
inc r14
adox r11, rbp
setc r11b
clc
mov rbp, -0x1 
movzx rax, al
adcx rax, rbp
adcx r10, [ rsp + 0x250 ]
seto al
movzx r14, byte [ rsp + 0x1c0 ]
inc rbp
mov rbp, -0x1 
adox r14, rbp
adox r13, [ rsp + 0x1b0 ]
adox r12, [ rsp + 0x1b8 ]
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x298 ], dil
mulx rdi, rbp, [ rsi + 0x8 ]
adox rbx, [ rsp + 0x240 ]
seto dl
mov byte [ rsp + 0x2a0 ], r9b
movzx r9, byte [ rsp + 0x1a0 ]
mov [ rsp + 0x2a8 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox r9, rdi
adox r13, [ rsp + 0x190 ]
seto r9b
inc rdi
mov rdi, -0x1 
movzx rax, al
adox rax, rdi
adox r13, [ rsp + 0x260 ]
mov rax, 0x6cfc5fd681c52056 
xchg rdx, rcx
mov [ rsp + 0x2b0 ], r13
mulx r13, rdi, rax
setc al
mov [ rsp + 0x2b8 ], rbp
movzx rbp, byte [ rsp + 0x238 ]
clc
mov [ rsp + 0x2c0 ], r14
mov r14, -0x1 
adcx rbp, r14
adcx rdi, [ rsp + 0x208 ]
mov rbp, 0x2341f27177344 
mov byte [ rsp + 0x2c8 ], al
mulx rax, r14, rbp
adcx r14, r13
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x2d0 ], rbp
mov rbp, 0x0 
dec rbp
movzx r9, r9b
adox r9, rbp
adox r12, [ rsp + 0x198 ]
adox rbx, [ rsp + 0x1a8 ]
setc r9b
clc
movzx rcx, cl
adcx rcx, rbp
adcx r10, rdi
setc cl
clc
movzx rdx, dl
adcx rdx, rbp
adcx r12, [ rsp + 0x270 ]
adox r10, [ rsp + 0x200 ]
setc dl
movzx rdi, byte [ rsp + 0x218 ]
clc
adcx rdi, rbp
adcx r15, [ rsp + 0x188 ]
mov rdi, [ rsp - 0x10 ]
seto bpl
mov [ rsp + 0x2d8 ], r12
mov r12, 0x0 
dec r12
movzx r11, r11b
adox r11, r12
adox rdi, [ rsp - 0x18 ]
adcx r13, r8
setc r8b
movzx r11, byte [ rsp + 0x2c8 ]
clc
adcx r11, r12
adcx rdi, [ rsp + 0x2c0 ]
movzx r11, r9b
lea r11, [ r11 + rax ]
mov rax, [ rsp - 0x20 ]
seto r9b
inc r12
adox rax, [ rsp + 0x2b8 ]
mov r12, [ rsp + 0x2a8 ]
adox r12, [ rsp + 0x8 ]
mov [ rsp + 0x2e0 ], r12
movzx r12, r9b
mov [ rsp + 0x2e8 ], rax
mov rax, [ rsp - 0x28 ]
lea r12, [ r12 + rax ]
mov rax, [ rsp + 0x0 ]
adox rax, [ rsp + 0x58 ]
movzx r9, byte [ rsp + 0x2a0 ]
adcx r9, r12
seto r12b
mov [ rsp + 0x2f0 ], rax
mov rax, 0x0 
dec rax
movzx rcx, cl
adox rcx, rax
adox rdi, r14
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mulx rax, rcx, rdx
adox r11, r9
seto dl
adc dl, 0x0
movzx rdx, dl
add r14b, 0xFF
adcx rbx, [ rsp + 0x268 ]
mov r14, [ rsp + 0x30 ]
adox r14, [ rsp + 0x2b0 ]
mov r9, 0x7bc65c783158aea3 
xchg rdx, r9
mov [ rsp + 0x2f8 ], rax
mov [ rsp + 0x300 ], rcx
mulx rcx, rax, r14
seto dl
mov byte [ rsp + 0x308 ], r12b
mov r12, 0x0 
dec r12
movzx rbp, bpl
adox rbp, r12
adox rdi, r15
adox r13, r11
mov rbp, 0xffffffffffffffff 
xchg rdx, r14
mulx r11, r15, rbp
adcx r10, [ rsp + 0x290 ]
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x310 ], rcx
mulx rcx, rbp, r12
movzx r12, r8b
mov [ rsp + 0x318 ], rax
mov rax, [ rsp + 0x2d0 ]
lea r12, [ r12 + rax ]
mov rax, r15
setc r8b
clc
adcx rax, r11
mov [ rsp + 0x320 ], rcx
mov rcx, r15
adcx rcx, r11
adcx rbp, r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x328 ], r13
mov [ rsp + 0x330 ], rbp
mulx rbp, r13, [ rsi + 0x20 ]
movzx rdx, r9b
adox rdx, r12
setc r9b
clc
adcx r15, r11
mov r15, [ rsp + 0x2d8 ]
seto r12b
mov [ rsp + 0x338 ], rbp
mov rbp, 0x0 
dec rbp
movzx r14, r14b
adox r14, rbp
adox r15, [ rsp + 0x1f8 ]
adcx rax, r15
setc r14b
clc
adcx rax, [ rsp - 0x30 ]
adox rbx, [ rsp + 0x210 ]
seto r15b
inc rbp
mov rbp, -0x1 
movzx r8, r8b
adox r8, rbp
adox rdi, [ rsp + 0x288 ]
seto r8b
inc rbp
mov rbp, -0x1 
movzx r14, r14b
adox r14, rbp
adox rbx, rcx
adcx rbx, [ rsp + 0x118 ]
setc cl
clc
movzx r15, r15b
adcx r15, rbp
adcx r10, [ rsp + 0x220 ]
adox r10, [ rsp + 0x330 ]
mov r14, 0x6cfc5fd681c52056 
xchg rdx, r14
mulx rbp, r15, rax
mov rdx, [ rsp + 0x248 ]
mov [ rsp + 0x340 ], rbp
seto bpl
mov [ rsp + 0x348 ], r15
movzx r15, byte [ rsp + 0x298 ]
mov [ rsp + 0x350 ], rbx
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
adox r15, rbx
adox rdx, [ rsp + 0x1f0 ]
mov r15, [ rsp + 0x1e8 ]
mov rbx, 0x0 
adox r15, rbx
adcx rdi, [ rsp + 0x230 ]
dec rbx
movzx r8, r8b
adox r8, rbx
adox rdx, [ rsp + 0x328 ]
adox r15, r14
adcx rdx, [ rsp + 0x228 ]
movzx r14, r12b
mov r8, 0x0 
adox r14, r8
inc rbx
mov r8, -0x1 
movzx rcx, cl
adox rcx, r8
adox r10, [ rsp + 0x110 ]
mov r12, [ rsp + 0x140 ]
seto cl
movzx rbx, byte [ rsp + 0x180 ]
inc r8
mov r8, -0x1 
adox rbx, r8
adox r12, [ rsp + 0xd8 ]
mov rbx, [ rsp - 0x38 ]
adox rbx, [ rsp + 0xb0 ]
mov r8, [ rsp + 0x318 ]
mov [ rsp + 0x358 ], rbx
seto bl
mov [ rsp + 0x360 ], r12
mov r12, 0x0 
dec r12
movzx r9, r9b
adox r9, r12
adox r8, [ rsp + 0x320 ]
movzx r9, bl
mov r12, [ rsp - 0x48 ]
lea r9, [ r9 + r12 ]
adcx r15, [ rsp + 0x258 ]
mov r12, 0xffffffffffffffff 
xchg rdx, rax
mov [ rsp + 0x368 ], r9
mulx r9, rbx, r12
setc r12b
clc
mov [ rsp + 0x370 ], r15
mov r15, -0x1 
movzx rbp, bpl
adcx rbp, r15
adcx rdi, r8
setc bpl
clc
movzx rcx, cl
adcx rcx, r15
adcx rdi, [ rsp + 0x120 ]
mov rcx, rbx
setc r8b
clc
adcx rcx, r9
mov r15, rbx
adcx r15, r9
mov byte [ rsp + 0x378 ], r8b
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r11
mov [ rsp + 0x380 ], rdi
mov [ rsp + 0x388 ], rax
mulx rax, rdi, r8
adox rdi, [ rsp + 0x310 ]
setc r8b
clc
adcx rbx, r11
seto bl
mov byte [ rsp + 0x390 ], r8b
movzx r8, byte [ rsp + 0x308 ]
mov [ rsp + 0x398 ], rdi
mov rdi, 0x0 
dec rdi
adox r8, rdi
adox r13, [ rsp + 0x50 ]
mov r8, [ rsp + 0x338 ]
adox r8, [ rsp + 0x300 ]
mov rdi, [ rsp + 0x2f8 ]
adox rdi, [ rsp + 0xd0 ]
adcx rcx, [ rsp + 0x350 ]
mov [ rsp + 0x3a0 ], rdi
mov rdi, 0x2341f27177344 
mov [ rsp + 0x3a8 ], r8
mov [ rsp + 0x3b0 ], r13
mulx r13, r8, rdi
adcx r15, r10
setc dl
clc
mov r10, -0x1 
movzx r12, r12b
adcx r12, r10
adcx r14, [ rsp + 0x280 ]
setc r12b
clc
movzx rbx, bl
adcx rbx, r10
adcx rax, r8
mov rbx, [ rsp + 0x398 ]
seto r8b
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox rbx, [ rsp + 0x388 ]
adox rax, [ rsp + 0x370 ]
mov rbp, 0x0 
adcx r13, rbp
adox r13, r14
mov r14, 0x7bc65c783158aea3 
xchg rdx, r11
mulx r10, rbp, r14
movzx r14, r12b
mov rdi, 0x0 
adox r14, rdi
mov r12, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x3b8 ], r8b
mulx r8, rdi, r12
add byte [ rsp + 0x390 ], 0x7F
adox r9, rdi
adox rbp, r8
mov rdi, -0x1 
movzx r11, r11b
adcx r11, rdi
adcx r9, [ rsp + 0x380 ]
mov r11, 0x2341f27177344 
mulx rdi, r8, r11
adox r10, [ rsp + 0x348 ]
adox r8, [ rsp + 0x340 ]
seto dl
mov r12, -0x2 
inc r12
adox rcx, [ rsp - 0x40 ]
adox r15, [ rsp + 0x2e8 ]
movzx r12, dl
lea r12, [ r12 + rdi ]
mov rdi, 0x6cfc5fd681c52056 
mov rdx, rdi
mulx r11, rdi, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x3c0 ], r11
mov [ rsp + 0x3c8 ], rdi
mulx rdi, r11, rcx
adox r9, [ rsp + 0x2e0 ]
seto dl
mov [ rsp + 0x3d0 ], rdi
movzx rdi, byte [ rsp + 0x378 ]
mov [ rsp + 0x3d8 ], r9
mov r9, -0x1 
inc r9
mov r9, -0x1 
adox rdi, r9
adox rbx, [ rsp + 0x178 ]
adox rax, [ rsp + 0x360 ]
adox r13, [ rsp + 0x358 ]
adcx rbp, rbx
adcx r10, rax
adox r14, [ rsp + 0x368 ]
adcx r8, r13
adcx r12, r14
mov dil, dl
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mulx r14, r13, [ rsi + 0x30 ]
seto dl
adc dl, 0x0
movzx rdx, dl
add dil, 0x7F
adox rbp, [ rsp + 0x2f0 ]
mov rdi, 0xffffffffffffffff 
xchg rdx, rdi
mov [ rsp + 0x3e0 ], r14
mulx r14, r9, rcx
mov rdx, r9
adcx rdx, r14
mov [ rsp + 0x3e8 ], r13
mov r13, r9
adcx r13, r14
mov [ rsp + 0x3f0 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x3f8 ], rbx
mov byte [ rsp + 0x400 ], dil
mulx rdi, rbx, [ rsi + 0x8 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x408 ], rdi
mov [ rsp + 0x410 ], rbx
mulx rbx, rdi, rcx
adcx rdi, r14
adcx r11, rbx
seto r14b
mov rbx, -0x2 
inc rbx
adox r9, rcx
adox rax, r15
adox r13, [ rsp + 0x3d8 ]
mov r9, [ rsp + 0x3d0 ]
adcx r9, [ rsp + 0x3c8 ]
mov rdx, [ rsi + 0x28 ]
mulx rbx, r15, [ rsi + 0x30 ]
setc dl
clc
mov [ rsp + 0x418 ], rbx
mov rbx, -0x1 
movzx r14, r14b
adcx r14, rbx
adcx r10, [ rsp + 0x3b0 ]
adox rdi, rbp
adox r11, r10
adcx r8, [ rsp + 0x3a8 ]
adcx r12, [ rsp + 0x3a0 ]
mov rbp, 0x2341f27177344 
xchg rdx, rcx
mulx r10, r14, rbp
movzx rdx, byte [ rsp + 0x3b8 ]
mov rbx, [ rsp + 0xc8 ]
lea rdx, [ rdx + rbx ]
movzx rbx, byte [ rsp + 0x400 ]
adcx rbx, rdx
setc dl
clc
mov rbp, -0x1 
movzx rcx, cl
adcx rcx, rbp
adcx r14, [ rsp + 0x3c0 ]
adox r9, r8
adox r14, r12
mov rcx, 0x0 
adcx r10, rcx
adox r10, rbx
mov r8, [ rsp + 0xc0 ]
clc
adcx r8, [ rsp + 0x410 ]
seto r12b
mov rbx, -0x3 
inc rbx
adox rax, [ rsp + 0xb8 ]
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, [ rsi + 0x30 ]
movzx rdx, r12b
movzx rcx, cl
lea rdx, [ rdx + rcx ]
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x420 ], rcx
mulx rcx, r12, rax
mov rdx, [ rsp + 0x408 ]
adcx rdx, [ rsp + 0x3f8 ]
mov [ rsp + 0x428 ], rcx
mov rcx, [ rsp + 0x3e8 ]
adcx rcx, [ rsp + 0x3f0 ]
adox r8, r13
adox rdx, rdi
adcx rbx, [ rsp + 0x3e0 ]
adcx r15, rbp
adox rcx, r11
adox rbx, r9
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx r11, rdi, rax
mov r9, [ rsp + 0x418 ]
adcx r9, [ rsp + 0x48 ]
mov rbp, rdi
setc dl
clc
adcx rbp, r11
mov [ rsp + 0x430 ], rbx
mov rbx, rdi
adcx rbx, r11
mov [ rsp + 0x438 ], rcx
movzx rcx, dl
mov [ rsp + 0x440 ], rbx
mov rbx, [ rsp + 0x40 ]
lea rcx, [ rcx + rbx ]
adox r15, r14
mov rbx, 0x6cfc5fd681c52056 
mov rdx, rbx
mulx r14, rbx, rax
adcx r12, r11
adox r9, r10
mov r10, 0x7bc65c783158aea3 
mov rdx, rax
mulx r11, rax, r10
adox rcx, [ rsp + 0x420 ]
seto r10b
mov [ rsp + 0x448 ], rcx
mov rcx, -0x2 
inc rcx
adox rdi, rdx
adox rbp, r8
adcx rax, [ rsp + 0x428 ]
adcx rbx, r11
adox r13, [ rsp + 0x440 ]
mov rdi, 0x2341f27177344 
mulx r11, r8, rdi
adox r12, [ rsp + 0x438 ]
adox rax, [ rsp + 0x430 ]
adcx r8, r14
adox rbx, r15
adox r8, r9
setc dl
seto r15b
mov r14, rbp
mov r9, 0xffffffffffffffff 
sub r14, r9
movzx rcx, dl
lea rcx, [ rcx + r11 ]
mov r11, r13
sbb r11, r9
mov rdx, r12
sbb rdx, r9
mov rdi, rax
mov r9, 0xfdc1767ae2ffffff 
sbb rdi, r9
mov r9, rbx
mov [ rsp + 0x450 ], rdx
mov rdx, 0x7bc65c783158aea3 
sbb r9, rdx
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox rcx, [ rsp + 0x448 ]
seto r15b
mov rdx, r8
mov [ rsp + 0x458 ], r14
mov r14, 0x6cfc5fd681c52056 
sbb rdx, r14
movzx r14, r15b
movzx r10, r10b
lea r14, [ r14 + r10 ]
mov r10, rcx
mov r15, 0x2341f27177344 
sbb r10, r15
sbb r14, 0x00000000
cmovc r9, rbx
cmovc rdi, rax
cmovc r10, rcx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x30 ], r10
mov [ r14 + 0x20 ], r9
cmovc rdx, r8
mov [ r14 + 0x18 ], rdi
cmovc r11, r13
mov r13, [ rsp + 0x458 ]
cmovc r13, rbp
mov [ r14 + 0x8 ], r11
mov [ r14 + 0x28 ], rdx
mov rbp, [ rsp + 0x450 ]
cmovc rbp, r12
mov [ r14 + 0x0 ], r13
mov [ r14 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1248
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.2629
; seed 4031532714329030 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 16885940 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=22, initial num_batches=31): 301455 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01785242633812509
; number reverted permutation / tried permutation: 66717 / 90342 =73.849%
; number reverted decision / tried decision: 53255 / 89657 =59.399%
; validated in 378.612s
