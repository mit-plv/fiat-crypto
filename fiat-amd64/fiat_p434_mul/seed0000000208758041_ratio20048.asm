SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 776
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rbx
mulx rbx, r15, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r13
mulx r13, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r12
mulx r12, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r14
mulx r14, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], r14
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
test al, al
adox r10, r14
adox rcx, r11
mov rdx, [ rsi + 0x8 ]
mulx r14, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
adox rcx, r8
adox r11, r10
adox r12, r14
mov rdx, [ rax + 0x18 ]
mulx r14, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x28 ], r14
mulx r14, r10, [ rsi + 0x8 ]
adox r10, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], r8
mulx r8, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x38 ], r10
mov [ rsp + 0x40 ], r12
mulx r12, r10, [ rsi + 0x30 ]
adcx r10, rdi
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
adcx rbp, r12
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x50 ], rbp
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r12
mov [ rsp + 0x60 ], r14
mulx r14, r12, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r12, rbp
adox rdi, r14
mov rdx, [ rax + 0x10 ]
mulx r14, rbp, [ rsi + 0x0 ]
adox r9, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r9
mulx r9, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r12
mulx r12, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x80 ], r11
mov [ rsp + 0x88 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r8
mulx r8, rdi, [ rax + 0x28 ]
seto dl
mov [ rsp + 0xa0 ], r13
mov r13, -0x2 
inc r13
adox r11, r12
adox rbp, rcx
adox r15, r14
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mulx rcx, r12, [ rax + 0x30 ]
adox r10, rbx
adox rdi, r9
adox r12, r8
mov rdx, [ rax + 0x8 ]
mulx r9, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mulx r13, r8, [ rax + 0x18 ]
mov rdx, 0x0 
adox rcx, rdx
mov [ rsp + 0xa8 ], rcx
mov rcx, -0x3 
inc rcx
adox rbx, [ rsp + 0xa0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb0 ], rbx
mulx rbx, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rbx
mov [ rsp + 0xc0 ], r12
mulx r12, rbx, [ rax + 0x28 ]
adox r9, [ rsp + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], rdi
mulx rdi, r9, [ rsi + 0x28 ]
adox r8, [ rsp - 0x20 ]
adox r13, [ rsp - 0x30 ]
adcx rcx, [ rsp + 0x98 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xd8 ], rcx
mov [ rsp + 0xe0 ], r13
mulx r13, rcx, [ rsp + 0x90 ]
adox rbx, [ rsp - 0x38 ]
mov rdx, rcx
mov [ rsp + 0xe8 ], rbx
setc bl
clc
adcx rdx, [ rsp + 0x90 ]
adox r9, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xf0 ], r9
mulx r9, r12, [ rsp + 0x90 ]
mov rdx, rcx
mov [ rsp + 0xf8 ], r8
seto r8b
mov byte [ rsp + 0x100 ], bl
mov rbx, -0x2 
inc rbx
adox rdx, r13
adox rcx, r13
adcx rdx, r11
adcx rcx, rbp
mov r11, 0xfdc1767ae2ffffff 
mov rbp, rdx
mov rdx, [ rsp + 0x90 ]
mov [ rsp + 0x108 ], r10
mulx r10, rbx, r11
adox rbx, r13
adox r12, r10
adcx rbx, r15
mov r15, rdx
mov rdx, [ rax + 0x28 ]
mulx r10, r13, [ rsi + 0x20 ]
movzx rdx, r8b
lea rdx, [ rdx + rdi ]
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mulx r11, r8, [ rsi + 0x20 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], r12
mulx r12, rdi, r15
adox rdi, r9
setc r9b
clc
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx r8, [ rsp - 0x40 ]
adcx r13, r11
seto r14b
inc rdx
adox rbp, [ rsp + 0x8 ]
mov r11, 0xfdc1767ae2ffffff 
mov rdx, rbp
mov [ rsp + 0x120 ], r13
mulx r13, rbp, r11
mov r11, 0x2341f27177344 
mov [ rsp + 0x128 ], r8
mov [ rsp + 0x130 ], r13
mulx r13, r8, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r8
mulx r8, r13, r11
adox rcx, [ rsp + 0x20 ]
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x148 ], r8
mov [ rsp + 0x150 ], r13
mulx r13, r8, [ rax + 0x30 ]
adcx r8, r10
adox rbx, [ rsp + 0x18 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x158 ], r8
mulx r8, r10, r15
mov r15, 0x0 
adcx r13, r15
clc
mov r15, -0x1 
movzx r14, r14b
adcx r14, r15
adcx r12, r10
mov r14, [ rsp + 0x108 ]
seto r10b
inc r15
mov r15, -0x1 
movzx r9, r9b
adox r9, r15
adox r14, [ rsp + 0x118 ]
adox rdi, [ rsp + 0xd0 ]
mov r9, 0x0 
adcx r8, r9
clc
movzx r10, r10b
adcx r10, r15
adcx r14, [ rsp + 0x88 ]
adox r12, [ rsp + 0xc0 ]
adox r8, [ rsp + 0xa8 ]
adcx rdi, [ rsp + 0x80 ]
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, r11
adcx r12, [ rsp + 0x40 ]
adcx r8, [ rsp + 0x38 ]
mov r15, r10
seto dl
mov [ rsp + 0x160 ], r13
mov r13, -0x2 
inc r13
adox r15, r9
mov r13, r10
adox r13, r9
mov [ rsp + 0x168 ], r8
mov r8b, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], rdi
mulx rdi, r12, [ rsi + 0x10 ]
movzx r8, r8b
movzx rdx, r8b
adcx rdx, [ rsp + 0x60 ]
setc r8b
clc
adcx rdi, [ rsp - 0x10 ]
mov byte [ rsp + 0x180 ], r8b
setc r8b
clc
adcx r10, r11
adcx r15, rcx
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r11
mov [ rsp + 0x188 ], rdi
mulx rdi, rcx, r10
adcx r13, rbx
adox rbp, r9
mov rdx, [ rsp + 0x150 ]
adox rdx, [ rsp + 0x130 ]
adox rcx, [ rsp + 0x148 ]
adcx rbp, r14
adcx rdx, [ rsp + 0x178 ]
adox rdi, [ rsp + 0x140 ]
mov rbx, [ rsp + 0x138 ]
mov r14, 0x0 
adox rbx, r14
adcx rcx, [ rsp + 0x170 ]
adcx rdi, [ rsp + 0x168 ]
mov r9, rdx
mov rdx, [ rax + 0x30 ]
mulx r10, r14, [ rsi + 0x18 ]
adcx rbx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x190 ], r10
mulx r10, r11, [ rax + 0x10 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox r11, [ rsp - 0x18 ]
adox r10, [ rsp + 0x30 ]
setc r8b
clc
adcx r12, r15
mov r15, 0x7bc65c783158aea3 
mov rdx, r15
mov [ rsp + 0x198 ], r14
mulx r14, r15, r12
adcx r13, [ rsp + 0x188 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1a0 ], r14
mov [ rsp + 0x1a8 ], r15
mulx r15, r14, [ rax + 0x28 ]
adcx r11, rbp
adcx r10, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, [ rax + 0x20 ]
adox rbp, [ rsp + 0x28 ]
adox r14, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1b0 ], r10
mulx r10, r9, [ rax + 0x30 ]
adox r9, r15
adcx rbp, rcx
mov rdx, 0x0 
adox r10, rdx
adcx r14, rdi
movzx rcx, r8b
movzx rdi, byte [ rsp + 0x180 ]
lea rcx, [ rcx + rdi ]
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r8, rdi, r12
adcx r9, rbx
mov rbx, rdi
mov r15, -0x2 
inc r15
adox rbx, r12
adcx r10, rcx
mov rbx, rdi
setc cl
clc
adcx rbx, r8
adcx rdi, r8
adox rbx, r13
mov r13, 0xfdc1767ae2ffffff 
mov rdx, r12
mulx r15, r12, r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x1b8 ], cl
mov [ rsp + 0x1c0 ], rbx
mulx rbx, rcx, [ rax + 0x8 ]
adox rdi, r11
adcx r12, r8
adox r12, [ rsp + 0x1b0 ]
adcx r15, [ rsp + 0x1a8 ]
mov rdx, 0x2341f27177344 
mulx r8, r11, r13
adox r15, rbp
mov rbp, 0x6cfc5fd681c52056 
mov rdx, r13
mov [ rsp + 0x1c8 ], r15
mulx r15, r13, rbp
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1d0 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
adcx r13, [ rsp + 0x1a0 ]
adox r13, r14
adcx r11, r15
mov rdx, 0x0 
adcx r8, rdx
adox r11, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r14, [ rax + 0x18 ]
clc
adcx rcx, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1d8 ], r11
mulx r11, r15, [ rax + 0x10 ]
adcx r15, rbx
adcx r14, r11
adcx rbp, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, rbx, [ rax + 0x28 ]
adcx rbx, r12
adcx r9, [ rsp + 0x198 ]
adox r8, r10
mov rdx, [ rsp + 0x1c0 ]
seto r10b
mov r12, -0x2 
inc r12
adox rdx, [ rsp - 0x8 ]
adox rcx, rdi
adox r15, [ rsp + 0x1d0 ]
adox r14, [ rsp + 0x1c8 ]
mov rdi, 0xffffffffffffffff 
mulx r12, r11, rdi
adox rbp, r13
adox rbx, [ rsp + 0x1d8 ]
mov r13, [ rsp + 0x190 ]
mov rdi, 0x0 
adcx r13, rdi
mov [ rsp + 0x1e0 ], rbx
mov rbx, r11
clc
adcx rbx, r12
movzx rdi, r10b
mov [ rsp + 0x1e8 ], rbp
movzx rbp, byte [ rsp + 0x1b8 ]
lea rdi, [ rdi + rbp ]
mov rbp, r11
adcx rbp, r12
adox r9, r8
adox r13, rdi
seto r10b
mov r8, -0x2 
inc r8
adox r11, rdx
mov r11, 0x6cfc5fd681c52056 
mulx r8, rdi, r11
mov r11, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x1f0 ], r10b
mov [ rsp + 0x1f8 ], r13
mulx r13, r10, r11
adox rbx, rcx
adcx r10, r12
adox rbp, r15
adox r10, r14
mov rcx, 0x7bc65c783158aea3 
mulx r14, r15, rcx
adcx r15, r13
adcx rdi, r14
adox r15, [ rsp + 0x1e8 ]
mov r12, 0x2341f27177344 
mulx r14, r13, r12
adcx r13, r8
mov rdx, 0x0 
adcx r14, rdx
clc
adcx rbx, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x78 ]
mov rdx, r11
mulx r8, r11, rbx
mov r12, 0xffffffffffffffff 
mov rdx, rbx
mulx rcx, rbx, r12
adcx r10, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x1e0 ]
adox r13, r9
adox r14, [ rsp + 0x1f8 ]
movzx r9, byte [ rsp + 0x1f0 ]
mov r12, 0x0 
adox r9, r12
mov [ rsp + 0x200 ], r8
mov r8, rbx
mov [ rsp + 0x208 ], r10
mov r10, -0x3 
inc r10
adox r8, rcx
adcx r15, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x128 ]
mov r12, rbx
adox r12, rcx
adcx r13, [ rsp + 0x120 ]
adcx r14, [ rsp + 0x158 ]
adcx r9, [ rsp + 0x160 ]
setc r10b
clc
adcx rbx, rdx
adcx r8, rbp
adox r11, rcx
adcx r12, [ rsp + 0x208 ]
adcx r11, r15
mov rbx, 0x7bc65c783158aea3 
mulx rcx, rbp, rbx
adox rbp, [ rsp + 0x200 ]
mov r15, 0x6cfc5fd681c52056 
mov [ rsp + 0x210 ], r11
mulx r11, rbx, r15
adox rbx, rcx
adcx rbp, rdi
adcx rbx, r13
mov rdi, 0x2341f27177344 
mulx rcx, r13, rdi
adox r13, r11
mov rdx, 0x0 
adox rcx, rdx
adcx r13, r14
adcx rcx, r9
movzx r14, r10b
adc r14, 0x0
mov rdx, [ rsi + 0x30 ]
mulx r9, r10, [ rax + 0x20 ]
xor rdx, rdx
adox r8, [ rsp - 0x28 ]
movzx r11, byte [ rsp + 0x100 ]
mov rdx, -0x1 
adcx r11, rdx
adcx r10, [ rsp + 0xb8 ]
adox r12, [ rsp + 0xb0 ]
mov r11, [ rsp + 0x210 ]
adox r11, [ rsp + 0xc8 ]
mov rdx, r8
mulx rdi, r8, r15
adox rbp, [ rsp + 0xf8 ]
adox rbx, [ rsp + 0xe0 ]
adox r13, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0xf0 ]
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x218 ], r10
mov [ rsp + 0x220 ], r9
mulx r9, r10, r15
adox r14, [ rsp + 0x110 ]
mov r15, r10
mov [ rsp + 0x228 ], r14
seto r14b
mov [ rsp + 0x230 ], rcx
mov rcx, -0x2 
inc rcx
adox r15, rdx
mov r15, r10
setc cl
clc
adcx r15, r9
adcx r10, r9
adox r15, r12
mov r12, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x238 ], r14b
mov byte [ rsp + 0x240 ], cl
mulx rcx, r14, r12
adcx r14, r9
mov r9, 0x7bc65c783158aea3 
mov [ rsp + 0x248 ], r15
mulx r15, r12, r9
adcx r12, rcx
mov rcx, 0x2341f27177344 
mov [ rsp + 0x250 ], r13
mulx r13, r9, rcx
adox r10, r11
adcx r8, r15
adcx r9, rdi
adox r14, rbp
mov rdx, 0x0 
adcx r13, rdx
adox r12, rbx
adox r8, [ rsp + 0x250 ]
adox r9, [ rsp + 0x230 ]
mov rdx, [ rax + 0x30 ]
mulx rdi, r11, [ rsi + 0x30 ]
mov rdx, [ rsp + 0x248 ]
clc
adcx rdx, [ rsp - 0x48 ]
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, rbx, [ rax + 0x28 ]
setc dl
movzx rcx, byte [ rsp + 0x240 ]
clc
mov [ rsp + 0x258 ], rbp
mov rbp, -0x1 
adcx rcx, rbp
adcx rbx, [ rsp + 0x220 ]
adox r13, [ rsp + 0x228 ]
adcx r11, r15
mov rcx, 0x0 
adcx rdi, rcx
clc
movzx rdx, dl
adcx rdx, rbp
adcx r10, [ rsp + 0x48 ]
adcx r14, [ rsp + 0x50 ]
adcx r12, [ rsp + 0xd8 ]
adcx r8, [ rsp + 0x218 ]
adcx rbx, r9
mov r9, 0xffffffffffffffff 
mov rdx, [ rsp + 0x258 ]
mulx rcx, r15, r9
movzx rbp, byte [ rsp + 0x238 ]
mov r9, 0x0 
adox rbp, r9
adcx r11, r13
adcx rdi, rbp
mov r13, r15
mov rbp, -0x3 
inc rbp
adox r13, rdx
mov r13, r15
setc bpl
clc
adcx r13, rcx
mov r9, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x260 ], bpl
mov [ rsp + 0x268 ], rdi
mulx rdi, rbp, r9
adox r13, r10
adcx r15, rcx
adcx rbp, rcx
adox r15, r14
mov r10, 0x6cfc5fd681c52056 
mulx rcx, r14, r10
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x270 ], r15
mulx r15, r9, r10
adcx r9, rdi
adcx r14, r15
adox rbp, r12
adox r9, r8
adox r14, rbx
mov r12, 0x2341f27177344 
mulx rbx, r8, r12
adcx r8, rcx
adox r8, r11
mov rdx, 0x0 
adcx rbx, rdx
adox rbx, [ rsp + 0x268 ]
movzx r11, byte [ rsp + 0x260 ]
adox r11, rdx
mov rdi, r13
mov rcx, 0xffffffffffffffff 
sub rdi, rcx
mov r15, [ rsp + 0x270 ]
sbb r15, rcx
mov rdx, rbp
sbb rdx, rcx
mov r12, r9
mov r10, 0xfdc1767ae2ffffff 
sbb r12, r10
mov r10, r14
mov rcx, 0x7bc65c783158aea3 
sbb r10, rcx
mov rcx, r8
mov [ rsp + 0x278 ], rdx
mov rdx, 0x6cfc5fd681c52056 
sbb rcx, rdx
mov rdx, rbx
mov [ rsp + 0x280 ], r10
mov r10, 0x2341f27177344 
sbb rdx, r10
sbb r11, 0x00000000
cmovc rdi, r13
cmovc rdx, rbx
cmovc r12, r9
cmovc r15, [ rsp + 0x270 ]
cmovc rcx, r8
mov r11, [ rsp + 0x280 ]
cmovc r11, r14
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x28 ], rcx
mov [ r13 + 0x20 ], r11
mov [ r13 + 0x30 ], rdx
mov [ r13 + 0x18 ], r12
mov r9, [ rsp + 0x278 ]
cmovc r9, rbp
mov [ r13 + 0x10 ], r9
mov [ r13 + 0x8 ], r15
mov [ r13 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 776
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 2.0048
; seed 1007670797487783 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7672406 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=28, initial num_batches=31): 143980 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018765951645416053
; number reverted permutation / tried permutation: 60916 / 90328 =67.439%
; number reverted decision / tried decision: 56312 / 89671 =62.798%
; validated in 364.193s
