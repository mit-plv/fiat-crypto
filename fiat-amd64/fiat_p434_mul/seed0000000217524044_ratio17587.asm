SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 968
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r10
mulx r10, r15, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], r15
mulx r15, r10, [ rsi + 0x20 ]
test al, al
adox rbx, r15
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r10
mov [ rsp + 0x48 ], r11
mulx r11, r10, [ rax + 0x30 ]
adox r15, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r15
mulx r15, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x58 ], r11
mov [ rsp + 0x60 ], r10
mulx r10, r11, [ rsi + 0x8 ]
adox rcx, rbx
adox r13, r8
mov rdx, [ rax + 0x0 ]
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], r13
mov [ rsp + 0x70 ], rcx
mulx rcx, r13, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r9
mulx r9, r15, [ rsi + 0x0 ]
adox r13, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r13
mulx r13, r14, [ rax + 0x10 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], rcx
mulx rcx, r8, r15
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xa0 ], rcx
mov [ rsp + 0xa8 ], r8
mulx r8, rcx, r15
adcx rbp, rbx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb0 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
adcx r14, r12
adcx r11, r13
adcx rbx, r10
mov rdx, 0x2341f27177344 
mulx r10, r12, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r13, [ rsi + 0x0 ]
setc dl
clc
adcx r13, r9
adcx rdi, rbx
mov r9, [ rsp + 0x30 ]
adcx r9, [ rsp + 0x48 ]
mov rbx, [ rsp + 0x0 ]
adcx rbx, [ rsp + 0x28 ]
mov [ rsp + 0xc0 ], r11
mov r11b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xc8 ], r14
mov [ rsp + 0xd0 ], rbx
mulx rbx, r14, [ rsi + 0x0 ]
adcx r14, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r9
mulx r9, r14, [ rax + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xe8 ], r10
mov [ rsp + 0xf0 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xf8 ], r8
mov [ rsp + 0x100 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
adcx r14, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], r14
mulx r14, rbx, [ rax + 0x28 ]
mov rdx, 0x0 
adcx r9, rdx
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rbp, rbx
adox r8, [ rsp + 0x98 ]
mov rdx, [ rax + 0x18 ]
mulx rbx, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x110 ], r8
mov [ rsp + 0x118 ], rbp
mulx rbp, r8, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x120 ], r9
mov r9, -0x2 
inc r9
adox r10, [ rsp - 0x10 ]
mov r9b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x128 ], r10
mov [ rsp + 0x130 ], rdi
mulx rdi, r10, [ rsi + 0x8 ]
adox r8, r12
adcx r10, r14
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, r12, [ rsi + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x138 ], r8
mov [ rsp + 0x140 ], rdi
mulx rdi, r8, r15
mov rdx, r8
clc
adcx rdx, r15
adox r11, rbp
movzx rdx, r9b
lea rdx, [ rdx + rcx ]
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mulx rbp, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x148 ], rcx
mov [ rsp + 0x150 ], rbp
mulx rbp, rcx, [ rsi + 0x30 ]
adox r9, rbx
mov rdx, r8
seto bl
mov [ rsp + 0x158 ], r9
mov r9, -0x2 
inc r9
adox rdx, rdi
adcx rdx, r13
adox r8, rdi
adcx r8, [ rsp + 0x130 ]
mov r13, 0xfdc1767ae2ffffff 
xchg rdx, r15
mov byte [ rsp + 0x160 ], bl
mulx rbx, r9, r13
adox r9, rdi
adox rbx, [ rsp + 0x100 ]
mov rdx, [ rsp + 0xf8 ]
adox rdx, [ rsp + 0xa8 ]
mov rdi, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x168 ], r11
mulx r11, r13, [ rsi + 0x30 ]
setc dl
clc
adcx r12, [ rsp - 0x18 ]
adcx r14, [ rsp - 0x30 ]
mov [ rsp + 0x170 ], r14
mov r14b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x178 ], r12
mov [ rsp + 0x180 ], r10
mulx r10, r12, [ rax + 0x18 ]
adcx r12, [ rsp - 0x38 ]
adcx rcx, r10
mov rdx, [ rsp + 0xa0 ]
adox rdx, [ rsp + 0xf0 ]
mov r10, [ rsp + 0xe8 ]
mov [ rsp + 0x188 ], rcx
mov rcx, 0x0 
adox r10, rcx
dec rcx
movzx r14, r14b
adox r14, rcx
adox r9, [ rsp + 0xe0 ]
adox rbx, [ rsp + 0xd0 ]
adox rdi, [ rsp + 0xd8 ]
adox rdx, [ rsp + 0x108 ]
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r12
mulx r12, rcx, [ rax + 0x28 ]
adcx rcx, rbp
adox r10, [ rsp + 0x120 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x198 ], rcx
mulx rcx, rbp, [ rax + 0x0 ]
seto dl
mov [ rsp + 0x1a0 ], rbp
mov rbp, -0x2 
inc rbp
adox rcx, [ rsp + 0x10 ]
mov rbp, [ rsp + 0x8 ]
adox rbp, [ rsp - 0x20 ]
mov [ rsp + 0x1a8 ], rbp
seto bpl
mov [ rsp + 0x1b0 ], rcx
mov rcx, -0x2 
inc rcx
adox r15, [ rsp + 0x90 ]
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r15
mov byte [ rsp + 0x1b8 ], r15b
mov [ rsp + 0x1c0 ], r10
mulx r10, r15, rcx
mov rcx, 0x2341f27177344 
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], r10
mulx r10, r14, rcx
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1d8 ], r10
mov [ rsp + 0x1e0 ], r14
mulx r14, r10, rcx
adox r8, [ rsp + 0xb0 ]
adox r9, [ rsp + 0xc8 ]
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1e8 ], r14
mov [ rsp + 0x1f0 ], r9
mulx r9, r14, rcx
adcx r13, r12
mov r12, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1f8 ], r13
mulx r13, rcx, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x200 ], r10
mov [ rsp + 0x208 ], r15
mulx r15, r10, r12
setc dl
clc
mov [ rsp + 0x210 ], r9
mov r9, -0x1 
movzx rbp, bpl
adcx rbp, r9
adcx rcx, [ rsp - 0x28 ]
mov rbp, r10
setc r9b
clc
adcx rbp, r12
adox rbx, [ rsp + 0xc0 ]
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x218 ], rcx
mulx rcx, r12, [ rax + 0x20 ]
setc dl
clc
mov [ rsp + 0x220 ], rcx
mov rcx, -0x1 
movzx r9, r9b
adcx r9, rcx
adcx r13, r12
mov r9, r10
setc r12b
clc
adcx r9, r15
adox rdi, [ rsp + 0xb8 ]
seto cl
mov [ rsp + 0x228 ], r13
mov r13, 0x0 
dec r13
movzx rdx, dl
adox rdx, r13
adox r8, r9
movzx rdx, bpl
lea rdx, [ rdx + r11 ]
adcx r10, r15
adcx r14, r15
mov r11, [ rsp + 0x208 ]
adcx r11, [ rsp + 0x210 ]
mov rbp, [ rsp + 0x200 ]
adcx rbp, [ rsp + 0x1d0 ]
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r9, [ rax + 0x0 ]
adox r10, [ rsp + 0x1f0 ]
adox r14, rbx
mov rdx, [ rsp + 0x1e8 ]
adcx rdx, [ rsp + 0x1e0 ]
mov rbx, [ rsp + 0x1d8 ]
mov [ rsp + 0x230 ], r15
mov r15, 0x0 
adcx rbx, r15
adox r11, rdi
mov rdi, [ rsp + 0x1c8 ]
clc
mov r15, -0x1 
movzx rcx, cl
adcx rcx, r15
adcx rdi, [ rsp + 0x118 ]
mov rcx, [ rsp + 0x1c0 ]
adcx rcx, [ rsp + 0x180 ]
adox rbp, rdi
mov rdi, [ rsp + 0x140 ]
movzx r15, byte [ rsp + 0x1b8 ]
adcx r15, rdi
adox rdx, rcx
adox rbx, r15
seto dil
adc dil, 0x0
movzx rdi, dil
adox r9, r8
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, rcx, [ rsi + 0x10 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x238 ], r12b
mov byte [ rsp + 0x240 ], dil
mulx rdi, r12, r9
adcx rcx, r13
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x248 ], rbx
mulx rbx, r13, [ rsi + 0x10 ]
adcx r13, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x250 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
adcx r15, rbx
adox rcx, r10
adox r13, r14
adcx rdi, [ rsp + 0x80 ]
mov rdx, [ rax + 0x28 ]
mulx r14, r10, [ rsi + 0x10 ]
adcx r10, [ rsp + 0x78 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x258 ], r13
mulx r13, rbx, r9
adox r15, r11
mov r11, rbx
seto dl
mov [ rsp + 0x260 ], r15
mov r15, -0x2 
inc r15
adox r11, r13
adcx r14, [ rsp + 0x60 ]
setc r15b
clc
mov [ rsp + 0x268 ], r14
mov r14, -0x1 
movzx rdx, dl
adcx rdx, r14
adcx rbp, rdi
adcx r10, r8
mov r8, 0x7bc65c783158aea3 
mov rdx, r8
mulx rdi, r8, r9
mov r14, rbx
adox r14, r13
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x270 ], r15b
mov [ rsp + 0x278 ], r10
mulx r10, r15, r9
adox r12, r13
adox r8, [ rsp + 0x250 ]
seto r13b
mov rdx, -0x2 
inc rdx
adox rbx, r9
adox r11, rcx
adox r14, [ rsp + 0x258 ]
adox r12, [ rsp + 0x260 ]
seto bl
inc rdx
mov rcx, -0x1 
movzx r13, r13b
adox r13, rcx
adox rdi, r15
setc r15b
clc
movzx rbx, bl
adcx rbx, rcx
adcx rbp, r8
adcx rdi, [ rsp + 0x278 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbx, [ rax + 0x30 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x280 ], rcx
mov [ rsp + 0x288 ], rbx
mulx rbx, rcx, r9
adox rcx, r10
mov r9, 0x0 
adox rbx, r9
movzx r10, byte [ rsp + 0x270 ]
mov r9, [ rsp + 0x58 ]
lea r10, [ r10 + r9 ]
mov r9, [ rsp + 0x248 ]
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox r9, [ rsp + 0x268 ]
adcx rcx, r9
movzx r15, byte [ rsp + 0x240 ]
adox r15, r10
adcx rbx, r15
seto r10b
adc r10b, 0x0
movzx r10, r10b
adox r11, [ rsp - 0x40 ]
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r15, r9, r11
adox r14, [ rsp + 0x128 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x290 ], r10b
mov [ rsp + 0x298 ], r14
mulx r14, r10, r11
adox r12, [ rsp + 0x138 ]
adox rbp, [ rsp + 0x168 ]
movzx rdx, byte [ rsp + 0x160 ]
mov [ rsp + 0x2a0 ], rbp
mov rbp, -0x1 
adcx rdx, rbp
adcx r13, [ rsp + 0x150 ]
adox rdi, [ rsp + 0x158 ]
adox r13, rcx
adcx r8, [ rsp + 0x288 ]
adox r8, rbx
mov rdx, r9
seto cl
inc rbp
adox rdx, r15
mov rbx, r9
adox rbx, r15
mov rbp, 0x7bc65c783158aea3 
xchg rdx, r11
mov [ rsp + 0x2a8 ], r8
mov [ rsp + 0x2b0 ], r13
mulx r13, r8, rbp
adox r10, r15
setc r15b
clc
adcx r9, rdx
mov r9, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x2b8 ], cl
mulx rcx, rbp, r9
adox r8, r14
adcx r11, [ rsp + 0x298 ]
adox rbp, r13
adcx rbx, r12
adcx r10, [ rsp + 0x2a0 ]
adcx r8, rdi
movzx r14, r15b
mov r12, [ rsp + 0x280 ]
lea r14, [ r14 + r12 ]
mov r12, 0x2341f27177344 
mulx r15, rdi, r12
adox rdi, rcx
seto dl
movzx r13, byte [ rsp + 0x2b8 ]
mov rcx, 0x0 
dec rcx
movzx r9, byte [ rsp + 0x290 ]
adox r13, rcx
adox r14, r9
movzx r9, dl
lea r9, [ r9 + r15 ]
seto r13b
inc rcx
adox r11, [ rsp + 0x40 ]
mov r15, 0xffffffffffffffff 
mov rdx, r11
mulx rcx, r11, r15
adox rbx, [ rsp + 0x38 ]
adox r10, [ rsp + 0x50 ]
adox r8, [ rsp + 0x70 ]
adcx rbp, [ rsp + 0x2b0 ]
adox rbp, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x2a8 ]
adcx r9, r14
movzx r14, r13b
mov r15, 0x0 
adcx r14, r15
adox rdi, [ rsp + 0x88 ]
adox r9, [ rsp + 0x110 ]
mov r13, r11
clc
adcx r13, rdx
adox r14, [ rsp + 0x148 ]
mov r13, r11
setc r12b
clc
adcx r13, rcx
seto r15b
mov [ rsp + 0x2c0 ], r14
mov r14, 0x0 
dec r14
movzx r12, r12b
adox r12, r14
adox rbx, r13
adcx r11, rcx
adox r11, r10
mov r10, 0xfdc1767ae2ffffff 
mulx r13, r12, r10
adcx r12, rcx
mov rcx, 0x7bc65c783158aea3 
mulx r10, r14, rcx
adcx r14, r13
mov r13, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x2c8 ], r15b
mulx r15, rcx, r13
mov r13, 0x2341f27177344 
mov [ rsp + 0x2d0 ], r9
mov [ rsp + 0x2d8 ], rdi
mulx rdi, r9, r13
adcx rcx, r10
adcx r9, r15
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx rbx, [ rsp + 0x1a0 ]
adcx r11, [ rsp + 0x1b0 ]
mov r10, 0xffffffffffffffff 
mov rdx, rbx
mulx r15, rbx, r10
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2e0 ], r11
mulx r11, r13, r10
mov r10, 0x6cfc5fd681c52056 
mov [ rsp + 0x2e8 ], r11
mov [ rsp + 0x2f0 ], r13
mulx r13, r11, r10
adox r12, r8
mov r8, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x2f8 ], r13
mulx r13, r10, [ rsi + 0x28 ]
adox r14, rbp
adox rcx, [ rsp + 0x2d8 ]
adox r9, [ rsp + 0x2d0 ]
adox rdi, [ rsp + 0x2c0 ]
adcx r12, [ rsp + 0x1a8 ]
adcx r14, [ rsp + 0x218 ]
mov rdx, [ rsp + 0x20 ]
seto bpl
mov [ rsp + 0x300 ], r14
movzx r14, byte [ rsp + 0x238 ]
mov [ rsp + 0x308 ], r12
mov r12, 0x0 
dec r12
adox r14, r12
adox rdx, [ rsp + 0x220 ]
adox r10, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x228 ]
adcx rdx, r9
movzx r14, bpl
movzx r9, byte [ rsp + 0x2c8 ]
lea r14, [ r14 + r9 ]
adcx r10, rdi
mov r9, 0x0 
adox r13, r9
mov rbp, 0x7bc65c783158aea3 
xchg rdx, rbp
mulx r9, rdi, r8
mov r12, rbx
mov rdx, -0x2 
inc rdx
adox r12, r15
mov rdx, rbx
adox rdx, r15
adox r15, [ rsp + 0x2f0 ]
adox rdi, [ rsp + 0x2e8 ]
adox r11, r9
setc r9b
clc
adcx rbx, r8
adcx r12, [ rsp + 0x2e0 ]
adcx rdx, [ rsp + 0x308 ]
adcx r15, [ rsp + 0x300 ]
adcx rdi, rcx
adcx r11, rbp
mov rbx, 0x2341f27177344 
xchg rdx, r8
mulx rbp, rcx, rbx
adox rcx, [ rsp + 0x2f8 ]
seto dl
mov rbx, -0x2 
inc rbx
adox r12, [ rsp - 0x48 ]
adox r8, [ rsp + 0x178 ]
adox r15, [ rsp + 0x170 ]
adox rdi, [ rsp + 0x190 ]
adox r11, [ rsp + 0x188 ]
adcx rcx, r10
movzx r10, dl
lea r10, [ r10 + rbp ]
setc bpl
clc
movzx r9, r9b
adcx r9, rbx
adcx r14, r13
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r13, r9, r12
mov rbx, r9
setc dl
clc
adcx rbx, r13
mov byte [ rsp + 0x310 ], dl
mov rdx, r9
adcx rdx, r13
mov [ rsp + 0x318 ], r10
seto r10b
mov [ rsp + 0x320 ], r14
mov r14, -0x2 
inc r14
adox r9, r12
mov r9, 0xfdc1767ae2ffffff 
xchg rdx, r12
mov byte [ rsp + 0x328 ], bpl
mulx rbp, r14, r9
adox rbx, r8
adox r12, r15
adcx r14, r13
mov r8, 0x6cfc5fd681c52056 
mulx r13, r15, r8
mov r8, 0x7bc65c783158aea3 
mov [ rsp + 0x330 ], r12
mulx r12, r9, r8
adox r14, rdi
adcx r9, rbp
mov rdi, 0x2341f27177344 
mulx r8, rbp, rdi
adox r9, r11
adcx r15, r12
adcx rbp, r13
mov rdx, 0x0 
adcx r8, rdx
clc
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rcx, [ rsp + 0x198 ]
mov r10, [ rsp + 0x318 ]
seto r13b
movzx r12, byte [ rsp + 0x328 ]
dec rdx
adox r12, rdx
adox r10, [ rsp + 0x320 ]
seto r11b
inc rdx
mov r12, -0x1 
movzx r13, r13b
adox r13, r12
adox rcx, r15
adcx r10, [ rsp + 0x1f8 ]
adox rbp, r10
movzx r13, r11b
movzx r15, byte [ rsp + 0x310 ]
lea r13, [ r13 + r15 ]
adcx r13, [ rsp + 0x230 ]
adox r8, r13
setc r15b
seto r11b
mov r10, rbx
mov r13, 0xffffffffffffffff 
sub r10, r13
mov rdx, [ rsp + 0x330 ]
sbb rdx, r13
movzx r12, r11b
movzx r15, r15b
lea r12, [ r12 + r15 ]
mov r15, r14
sbb r15, r13
mov r11, r9
mov rdi, 0xfdc1767ae2ffffff 
sbb r11, rdi
mov rdi, rcx
mov r13, 0x7bc65c783158aea3 
sbb rdi, r13
mov r13, rbp
mov [ rsp + 0x338 ], r15
mov r15, 0x6cfc5fd681c52056 
sbb r13, r15
mov r15, r8
mov [ rsp + 0x340 ], rdx
mov rdx, 0x2341f27177344 
sbb r15, rdx
sbb r12, 0x00000000
cmovc r11, r9
cmovc r10, rbx
cmovc rdi, rcx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], r10
cmovc r13, rbp
mov rbx, [ rsp + 0x340 ]
cmovc rbx, [ rsp + 0x330 ]
mov [ r12 + 0x28 ], r13
cmovc r15, r8
mov r9, [ rsp + 0x338 ]
cmovc r9, r14
mov [ r12 + 0x30 ], r15
mov [ r12 + 0x10 ], r9
mov [ r12 + 0x20 ], rdi
mov [ r12 + 0x8 ], rbx
mov [ r12 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 968
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7587
; seed 2344211671174711 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7809524 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=28, initial num_batches=31): 144533 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018507273938846977
; number reverted permutation / tried permutation: 60694 / 90105 =67.359%
; number reverted decision / tried decision: 56874 / 89894 =63.268%
; validated in 378s
