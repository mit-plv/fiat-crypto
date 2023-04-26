SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 832
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r13
mulx r13, r11, rdx
mov rdx, 0x2341f27177344 
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], r15
mulx r15, r12, r11
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rdi
mulx rdi, r15, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r9
mulx r9, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r14
mulx r14, r9, [ rsi + 0x28 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r9
mulx r9, r14, r11
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r10
mulx r10, r8, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x30 ], rax
mov [ rsp + 0x38 ], rbp
mulx rbp, rax, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], rax
mulx rax, rbp, r11
mov rdx, rbp
mov [ rsp + 0x50 ], rbx
xor rbx, rbx
adox rdx, r11
mov rdx, [ rsi + 0x28 ]
mulx rbx, r11, [ rsi + 0x8 ]
mov rdx, rbp
adcx rdx, rax
adcx rbp, rax
adcx r8, rax
adcx r14, r10
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r14
mulx r14, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
setc dl
clc
adcx rax, r13
adox r10, rax
seto r13b
mov rax, 0x0 
dec rax
movzx rdx, dl
adox rdx, rax
adox r9, r15
adox r12, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r15, [ rsi + 0x10 ]
seto dl
inc rax
adox r8, rcx
mov cl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r8
mulx r8, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], rax
mov [ rsp + 0x80 ], r12
mulx r12, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r9
mov byte [ rsp + 0x90 ], cl
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x98 ], r13b
mov [ rsp + 0xa0 ], r14
mulx r14, r13, rdx
adox r15, rbp
adox r13, rdi
setc dl
clc
adcx r8, [ rsp + 0x50 ]
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r13
mulx r13, rdi, rdx
adcx rdi, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r15
mov [ rsp + 0xb8 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r8
mov byte [ rsp + 0xc8 ], bpl
mulx rbp, r8, [ rsi + 0x28 ]
adcx rax, r13
adcx r9, r12
adcx r8, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r12, [ rsi + 0x18 ]
adox r12, r14
mov rdx, [ rsi + 0x30 ]
mulx r13, r14, [ rsi + 0x10 ]
adox r15, rcx
adcx r14, rbp
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], r15
mov [ rsp + 0xd8 ], r12
mulx r12, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], r14
mov [ rsp + 0xe8 ], r8
mulx r8, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xf0 ], r9
mov [ rsp + 0xf8 ], rax
mulx rax, r9, [ rsi + 0x28 ]
setc dl
clc
adcx r15, rax
adox r14, rdi
movzx rdi, dl
lea rdi, [ rdi + r13 ]
mov rdx, [ rsi + 0x10 ]
mulx rax, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r15
mov [ rsp + 0x108 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r8, rdx
mov [ rsp + 0x110 ], r15
mov r15, -0x3 
inc r15
adox r9, [ rsp + 0x30 ]
adox rbp, [ rsp + 0x28 ]
adcx r13, r12
mov rdx, [ rsi + 0x30 ]
mulx r15, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], r13
mov [ rsp + 0x120 ], rbp
mulx rbp, r13, [ rsi + 0x28 ]
adcx r13, rax
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r13
mulx r13, rax, [ rsi + 0x20 ]
adcx rax, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], rax
mulx rax, rbp, rdx
adcx rbp, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x138 ], rbp
mulx rbp, r13, rdx
adcx r12, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r12
mulx r12, rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x148 ], r9
mov [ rsp + 0x150 ], r8
mulx r8, r9, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r14
mov [ rsp + 0x160 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
adox rcx, [ rsp + 0x20 ]
adox r13, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], r13
mov [ rsp + 0x170 ], rcx
mulx rcx, r13, [ rsi + 0x30 ]
setc dl
clc
adcx r9, rcx
adox rbp, [ rsp - 0x10 ]
seto cl
mov [ rsp + 0x178 ], r9
mov r9, -0x2 
inc r9
adox r10, [ rsp - 0x18 ]
mov r9, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x180 ], r13
mov byte [ rsp + 0x188 ], cl
mulx rcx, r13, r10
adcx r8, [ rsp + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x190 ], r8
mov [ rsp + 0x198 ], rbp
mulx rbp, r8, r10
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1a0 ], rcx
mov [ rsp + 0x1a8 ], r13
mulx r13, rcx, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1b0 ], rbp
mov [ rsp + 0x1b8 ], r8
mulx r8, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c0 ], r13
mov [ rsp + 0x1c8 ], rcx
mulx rcx, r13, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x1d0 ], r8
mov r8, -0x2 
inc r8
adox rax, [ rsp - 0x28 ]
mov r8b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1d8 ], rax
mov [ rsp + 0x1e0 ], rbp
mulx rbp, rax, [ rsi + 0x30 ]
adox r13, r12
adox r14, rcx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r12, [ rsi + 0x20 ]
adox r12, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1e8 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
movzx rdx, r9b
lea rdx, [ rdx + r15 ]
adox r11, rcx
adox rax, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, 0x0 
adox rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1f0 ], rbx
mulx rbx, rcx, [ rsi + 0x28 ]
adcx rdi, [ rsp + 0x0 ]
adcx r12, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
movzx rdx, byte [ rsp + 0xc8 ]
mov [ rsp + 0x1f8 ], rcx
mov rcx, 0x0 
dec rcx
adox rdx, rcx
adox r15, [ rsp + 0xa0 ]
adox r9, [ rsp + 0x1e0 ]
adcx rbx, [ rsp + 0x48 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x200 ], rbx
mulx rbx, rcx, [ rsi + 0x0 ]
adox rcx, [ rsp + 0x1d0 ]
adox rbx, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x208 ], r12
mov [ rsp + 0x210 ], rdi
mulx rdi, r12, [ rsi + 0x0 ]
adox r12, [ rsp + 0x10 ]
seto dl
mov [ rsp + 0x218 ], rbp
movzx rbp, byte [ rsp + 0x98 ]
mov [ rsp + 0x220 ], rax
mov rax, 0x0 
dec rax
adox rbp, rax
adox r15, [ rsp + 0x68 ]
mov rbp, [ rsp + 0x40 ]
mov rax, 0x0 
adcx rbp, rax
adox r9, [ rsp + 0x60 ]
clc
mov rax, -0x1 
movzx r8, r8b
adcx r8, rax
adcx r15, [ rsp + 0x1d8 ]
adcx r13, r9
adox rcx, [ rsp + 0x58 ]
movzx r8, byte [ rsp + 0x90 ]
mov r9, [ rsp - 0x20 ]
lea r8, [ r8 + r9 ]
adox rbx, [ rsp + 0x88 ]
adcx r14, rcx
adcx rbx, [ rsp + 0x1e8 ]
adox r12, [ rsp + 0x80 ]
adcx r11, r12
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mulx r12, rcx, r10
movzx rax, r9b
lea rax, [ rax + rdi ]
adox r8, rax
adcx r8, [ rsp + 0x220 ]
setc dil
movzx rdi, dil
adox rdi, [ rsp + 0x218 ]
mov r9, rcx
clc
adcx r9, r12
mov rax, rcx
adcx rax, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x228 ], rbp
mov [ rsp + 0x230 ], rdi
mulx rdi, rbp, r10
seto dl
mov [ rsp + 0x238 ], r8
mov r8, -0x2 
inc r8
adox rcx, r10
adcx r12, [ rsp + 0x1c8 ]
adcx rbp, [ rsp + 0x1c0 ]
adox r9, r15
adox rax, r13
adox r12, r14
adcx rdi, [ rsp + 0x1b8 ]
adox rbp, rbx
adox rdi, r11
seto cl
inc r8
adox r9, [ rsp + 0x78 ]
adox rax, [ rsp + 0xc0 ]
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, r9
mulx r13, r15, r10
mov r14, 0xffffffffffffffff 
mulx r11, rbx, r14
mov r8, [ rsp + 0x1a8 ]
adcx r8, [ rsp + 0x1b0 ]
adox r12, [ rsp + 0xb8 ]
adox rbp, [ rsp + 0xf8 ]
mov r14, [ rsp + 0x1a0 ]
mov r10, 0x0 
adcx r14, r10
adox rdi, [ rsp + 0xf0 ]
clc
mov r10, -0x1 
movzx rcx, cl
adcx rcx, r10
adcx r8, [ rsp + 0x238 ]
adox r8, [ rsp + 0xe8 ]
adcx r14, [ rsp + 0x230 ]
mov rcx, rbx
setc r10b
clc
adcx rcx, r11
mov [ rsp + 0x240 ], r8
mov r8, rbx
adcx r8, r11
mov [ rsp + 0x248 ], rdi
movzx rdi, r10b
movzx r9, r9b
lea rdi, [ rdi + r9 ]
adox r14, [ rsp + 0xe0 ]
adcx r15, r11
adox rdi, [ rsp + 0x160 ]
seto r9b
mov r11, -0x2 
inc r11
adox rbx, rdx
adox rcx, rax
mov rbx, 0x7bc65c783158aea3 
mulx r10, rax, rbx
adcx rax, r13
adox r8, r12
adox r15, rbp
mov r13, 0x6cfc5fd681c52056 
mulx rbp, r12, r13
adcx r12, r10
adox rax, [ rsp + 0x248 ]
adox r12, [ rsp + 0x240 ]
mov r10, 0x2341f27177344 
mulx rbx, r11, r10
adcx r11, rbp
setc dl
clc
adcx rcx, [ rsp - 0x40 ]
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mulx r10, r13, rcx
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x250 ], r10
mov [ rsp + 0x258 ], r13
mulx r13, r10, rcx
adox r11, r14
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x260 ], r13
mulx r13, r14, rcx
adcx r8, [ rsp + 0x70 ]
movzx rdx, bpl
lea rdx, [ rdx + rbx ]
adcx r15, [ rsp + 0xb0 ]
adcx rax, [ rsp + 0xa8 ]
adcx r12, [ rsp + 0xd8 ]
adox rdx, rdi
adcx r11, [ rsp + 0xd0 ]
movzx rdi, r9b
mov rbx, 0x0 
adox rdi, rbx
mov r9, r14
mov rbp, -0x3 
inc rbp
adox r9, rcx
mov r9, r14
setc bpl
clc
adcx r9, r13
adcx r14, r13
adcx r13, [ rsp + 0x258 ]
adox r9, r8
adox r14, r15
mov r8, 0x7bc65c783158aea3 
xchg rdx, r8
mulx rbx, r15, rcx
adox r13, rax
adcx r15, [ rsp + 0x250 ]
adcx r10, rbx
adox r15, r12
mov rax, 0x2341f27177344 
mov rdx, rax
mulx r12, rax, rcx
adcx rax, [ rsp + 0x260 ]
mov rcx, 0x0 
adcx r12, rcx
adox r10, r11
clc
mov r11, -0x1 
movzx rbp, bpl
adcx rbp, r11
adcx r8, [ rsp + 0x158 ]
adox rax, r8
mov rdx, [ rsi + 0x20 ]
mulx rbx, rbp, [ rsi + 0x30 ]
adcx rdi, [ rsp + 0x150 ]
adox r12, rdi
seto dl
adc dl, 0x0
movzx rdx, dl
adox r9, [ rsp + 0x110 ]
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mulx rcx, rdi, r9
adox r14, [ rsp + 0x148 ]
mov r11, rdi
adcx r11, rcx
adox r13, [ rsp + 0x120 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x268 ], r8b
mov [ rsp + 0x270 ], r12
mulx r12, r8, r9
adox r15, [ rsp + 0x170 ]
adox r10, [ rsp + 0x168 ]
adox rax, [ rsp + 0x198 ]
mov rdx, rdi
mov [ rsp + 0x278 ], rax
seto al
mov [ rsp + 0x280 ], r10
mov r10, -0x2 
inc r10
adox rdx, r9
adox r11, r14
adcx rdi, rcx
adox rdi, r13
adcx r8, rcx
adox r8, r15
mov rdx, 0x7bc65c783158aea3 
mulx r14, rcx, r9
seto r13b
inc r10
adox r11, [ rsp + 0x108 ]
adcx rcx, r12
adox rdi, [ rsp + 0x100 ]
mulx r15, r12, r11
adox r8, [ rsp + 0x118 ]
mov r10, 0x6cfc5fd681c52056 
mov rdx, r10
mov [ rsp + 0x288 ], r15
mulx r15, r10, r9
setc dl
mov [ rsp + 0x290 ], r8
movzx r8, byte [ rsp + 0x188 ]
clc
mov [ rsp + 0x298 ], r12
mov r12, -0x1 
adcx r8, r12
adcx rbp, [ rsp - 0x48 ]
mov r8, 0x0 
adcx rbx, r8
mov r8, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x2a0 ], rdi
mulx rdi, r12, r8
clc
mov rdx, -0x1 
movzx rax, al
adcx rax, rdx
adcx rbp, [ rsp + 0x270 ]
movzx rax, byte [ rsp + 0x268 ]
adcx rax, rbx
setc bl
clc
movzx r9, r9b
adcx r9, rdx
adcx r14, r10
adcx r12, r15
mov r9, 0x0 
adcx rdi, r9
clc
movzx r13, r13b
adcx r13, rdx
adcx rcx, [ rsp + 0x280 ]
adox rcx, [ rsp + 0x128 ]
adcx r14, [ rsp + 0x278 ]
adcx r12, rbp
adcx rdi, rax
movzx r13, bl
adcx r13, r9
adox r14, [ rsp + 0x130 ]
adox r12, [ rsp + 0x138 ]
mov r10, 0xffffffffffffffff 
mov rdx, r11
mulx r15, r11, r10
mov rbp, r11
clc
adcx rbp, rdx
adox rdi, [ rsp + 0x140 ]
mov rbp, r11
setc bl
clc
adcx rbp, r15
adox r13, [ rsp + 0x1f0 ]
seto al
dec r9
movzx rbx, bl
adox rbx, r9
adox rbp, [ rsp + 0x2a0 ]
adcx r11, r15
mov rbx, 0xfdc1767ae2ffffff 
mulx r10, r9, rbx
adcx r9, r15
adcx r10, [ rsp + 0x298 ]
adox r11, [ rsp + 0x290 ]
adox r9, rcx
adox r10, r14
mov rcx, 0x6cfc5fd681c52056 
mulx r15, r14, rcx
mulx rcx, rbx, r8
adcx r14, [ rsp + 0x288 ]
adcx rbx, r15
adox r14, r12
setc dl
clc
adcx rbp, [ rsp + 0x180 ]
adcx r11, [ rsp + 0x178 ]
adox rbx, rdi
mov r12, 0xffffffffffffffff 
xchg rdx, rbp
mulx r15, rdi, r12
adcx r9, [ rsp + 0x190 ]
movzx r12, bpl
lea r12, [ r12 + rcx ]
mulx rbp, rcx, r8
adox r12, r13
adcx r10, [ rsp + 0x210 ]
adcx r14, [ rsp + 0x208 ]
adcx rbx, [ rsp + 0x1f8 ]
adcx r12, [ rsp + 0x200 ]
movzx r13, al
mov r8, 0x0 
adox r13, r8
mov rax, rdi
mov [ rsp + 0x2a8 ], rbp
mov rbp, -0x3 
inc rbp
adox rax, rdx
adcx r13, [ rsp + 0x228 ]
mov rax, rdi
setc bpl
clc
adcx rax, r15
adox rax, r11
adcx rdi, r15
adox rdi, r9
mov r11, 0x7bc65c783158aea3 
mulx r8, r9, r11
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2b0 ], rdi
mov [ rsp + 0x2b8 ], rax
mulx rax, rdi, r11
adcx rdi, r15
adcx r9, rax
adox rdi, r10
mov r15, 0x6cfc5fd681c52056 
mulx rax, r10, r15
adcx r10, r8
adcx rcx, rax
adox r9, r14
adox r10, rbx
adox rcx, r12
mov rdx, [ rsp + 0x2a8 ]
mov r14, 0x0 
adcx rdx, r14
adox rdx, r13
movzx rbx, bpl
adox rbx, r14
mov r12, [ rsp + 0x2b8 ]
mov rbp, 0xffffffffffffffff 
sub r12, rbp
mov r13, [ rsp + 0x2b0 ]
sbb r13, rbp
mov r8, rdi
sbb r8, rbp
mov rax, r9
sbb rax, r11
mov r14, r10
mov rbp, 0x7bc65c783158aea3 
sbb r14, rbp
mov rbp, rcx
sbb rbp, r15
mov r11, rdx
mov r15, 0x2341f27177344 
sbb r11, r15
sbb rbx, 0x00000000
cmovc r11, rdx
cmovc r14, r10
cmovc r8, rdi
cmovc rax, r9
cmovc r12, [ rsp + 0x2b8 ]
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], rax
mov [ rbx + 0x0 ], r12
mov [ rbx + 0x20 ], r14
cmovc r13, [ rsp + 0x2b0 ]
mov [ rbx + 0x8 ], r13
cmovc rbp, rcx
mov [ rbx + 0x28 ], rbp
mov [ rbx + 0x30 ], r11
mov [ rbx + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 832
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.8934
; seed 3642856512495627 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7268836 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 136990 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018846208663945645
; number reverted permutation / tried permutation: 60925 / 89840 =67.815%
; number reverted decision / tried decision: 56984 / 90159 =63.204%
; validated in 332.947s
