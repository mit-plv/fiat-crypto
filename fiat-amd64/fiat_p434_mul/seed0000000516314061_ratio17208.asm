SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 784
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r14
mulx r14, r9, [ rax + 0x8 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r14
mulx r14, r11, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r15
mulx r15, r10, [ rsi + 0x18 ]
test al, al
adox r9, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r9
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], r15
mulx r15, rbx, rcx
adcx r13, r9
mov r9, rbx
setc dl
clc
adcx r9, r15
mov [ rsp + 0x10 ], r13
seto r13b
mov byte [ rsp + 0x18 ], dl
mov rdx, -0x2 
inc rdx
adox rbp, rdi
mov rdi, rbx
adcx rdi, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r10
mulx r10, rbp, [ rsi + 0x10 ]
adox rbp, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x30 ], rbp
mulx rbp, r12, rcx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x38 ], r10
mov byte [ rsp + 0x40 ], r13b
mulx r13, r10, rcx
adcx r10, r15
adcx r12, r13
adcx r11, rbp
mov rdx, [ rsi + 0x28 ]
mulx rbp, r15, [ rax + 0x10 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x48 ], r11
mulx r11, r13, rcx
adcx r13, r14
seto r14b
mov rdx, -0x2 
inc rdx
adox r8, [ rsp - 0x10 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x50 ], r14b
mov [ rsp + 0x58 ], r11
mulx r11, r14, [ rsi + 0x0 ]
adox r14, [ rsp - 0x20 ]
adox r11, [ rsp - 0x28 ]
clc
adcx rbx, rcx
mov rdx, [ rax + 0x18 ]
mulx rcx, rbx, [ rsi + 0x28 ]
adcx r9, r8
adcx rdi, r14
adcx r10, r11
mov rdx, [ rax + 0x8 ]
mulx r14, r8, [ rsi + 0x8 ]
seto dl
movzx r11, byte [ rsp + 0x40 ]
mov [ rsp + 0x60 ], rcx
mov rcx, 0x0 
dec rcx
adox r11, rcx
adox r15, [ rsp - 0x30 ]
adox rbx, rbp
mov r11b, dl
mov rdx, [ rsi + 0x30 ]
mulx rcx, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rbx
mulx rbx, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r10
mulx r10, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], rdi
mov [ rsp + 0x90 ], r9
mulx r9, rdi, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r12
mulx r12, r13, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0xa8 ], r13
mov r13, -0x2 
inc r13
adox r15, rcx
adox rdi, r10
mov cl, dl
mov rdx, [ rsi + 0x30 ]
mulx r13, r10, [ rax + 0x18 ]
setc dl
clc
adcx r8, r12
adox r10, r9
mov r9b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r10
mulx r10, r12, [ rax + 0x10 ]
adcx r12, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb8 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
adox rbp, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], rbp
mulx rbp, r13, [ rax + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc8 ], r15
mov byte [ rsp + 0xd0 ], cl
mulx rcx, r15, [ rax + 0x18 ]
adcx r15, r10
adcx r14, rcx
mov rdx, [ rax + 0x30 ]
mulx rcx, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], r15
mulx r15, r14, [ rax + 0x28 ]
adcx r14, rdi
adox r13, rbx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rax + 0x30 ]
adox r10, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xe8 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
adcx rbx, r15
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf0 ], rcx
mulx rcx, r15, [ rax + 0x0 ]
adc rdi, 0x0
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r13
mov [ rsp + 0x100 ], r15
mulx r15, r13, [ rax + 0x10 ]
add rbp, rcx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x108 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x110 ], rdi
mov [ rsp + 0x118 ], rbx
mulx rbx, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x120 ], r14
mov [ rsp + 0x128 ], r12
mulx r12, r14, [ rsi + 0x18 ]
adcx r13, r10
adcx rdi, r15
mov rdx, [ rsi + 0x0 ]
mulx r15, r10, [ rax + 0x20 ]
mov rdx, 0x0 
dec rdx
movzx r11, r11b
adox r11, rdx
adox r10, [ rsp - 0x38 ]
adcx rcx, rbx
mov rdx, [ rax + 0x30 ]
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x130 ], rcx
mov [ rsp + 0x138 ], rdi
mulx rdi, rcx, [ rsi + 0x0 ]
adox rcx, r15
adox r11, rdi
seto dl
mov r15, 0x0 
dec r15
movzx r9, r9b
adox r9, r15
adox r10, [ rsp + 0xa0 ]
adox rcx, [ rsp + 0x48 ]
adox r11, [ rsp + 0x98 ]
mov r9b, dl
mov rdx, [ rax + 0x18 ]
mulx r15, rdi, [ rsi + 0x10 ]
movzx rdx, r9b
lea rdx, [ rdx + rbx ]
adcx r14, rbp
adox rdx, [ rsp + 0x58 ]
adcx r12, [ rsp + 0x28 ]
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rbx, [ rax + 0x20 ]
mov rdx, [ rsp + 0xa8 ]
mov [ rsp + 0x140 ], r12
setc r12b
clc
adcx rdx, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x88 ]
mov [ rsp + 0x148 ], r14
seto r14b
mov byte [ rsp + 0x150 ], r12b
movzx r12, byte [ rsp + 0x50 ]
mov [ rsp + 0x158 ], r13
mov r13, 0x0 
dec r13
adox r12, r13
adox rdi, [ rsp + 0x38 ]
adox rbx, r15
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rax + 0x28 ]
adox r15, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x160 ], r15
mulx r15, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], rdi
mulx rdi, rbx, [ rsi + 0x10 ]
adox rbx, r13
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], rbx
mulx rbx, r13, [ rax + 0x18 ]
mov rdx, 0x0 
adox rdi, rdx
movzx rdx, byte [ rsp + 0x18 ]
mov [ rsp + 0x180 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
adox rdx, rdi
adox r9, [ rsp - 0x40 ]
adox r13, r15
mov rdx, [ rsp + 0x80 ]
adcx rdx, [ rsp + 0x128 ]
adcx r10, [ rsp + 0xe0 ]
adcx rcx, [ rsp + 0xd8 ]
adcx r11, [ rsp + 0x120 ]
adcx rbp, [ rsp + 0x118 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x188 ], r13
mulx r13, rdi, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x190 ], r9
mov [ rsp + 0x198 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1a0 ], r11
mov [ rsp + 0x1a8 ], rcx
mulx rcx, r11, [ rax + 0x28 ]
movzx r14, r14b
movzx rdx, r14b
adcx rdx, [ rsp + 0x110 ]
adox r9, rbx
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1b0 ], r9
mulx r9, rbx, [ rsi + 0x28 ]
adox r11, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1b8 ], r11
mulx r11, rbp, r12
adox rdi, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1c0 ], rdi
mulx rdi, rcx, [ rax + 0x20 ]
mov rdx, 0x0 
adox r13, rdx
movzx rdx, byte [ rsp + 0xd0 ]
mov [ rsp + 0x1c8 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox rcx, [ rsp + 0x60 ]
adox rbx, rdi
mov rdx, [ rsi + 0x28 ]
mulx r13, rdi, [ rax + 0x30 ]
adox rdi, r9
mov rdx, rbp
setc r9b
clc
adcx rdx, r11
mov [ rsp + 0x1d0 ], rdi
mov rdi, rbp
mov [ rsp + 0x1d8 ], rbx
seto bl
mov [ rsp + 0x1e0 ], rcx
mov rcx, -0x2 
inc rcx
adox rdi, r12
adox rdx, r8
adcx rbp, r11
adox rbp, r15
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx r15, r8, r12
adcx r8, r11
movzx r11, bl
lea r11, [ r11 + r13 ]
adox r8, r10
mov r10, 0x6cfc5fd681c52056 
mov rdx, r10
mulx r13, r10, r12
mov rbx, 0x7bc65c783158aea3 
mov rdx, r12
mulx rcx, r12, rbx
adcx r12, r15
adcx r10, rcx
adox r12, [ rsp + 0x1a8 ]
adox r10, [ rsp + 0x1a0 ]
mov r15, 0x2341f27177344 
mulx rbx, rcx, r15
adcx rcx, r13
adox rcx, [ rsp + 0x198 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rbx, r14
clc
adcx rdi, [ rsp - 0x18 ]
movzx r14, r9b
adox r14, rdx
mov r9, 0xffffffffffffffff 
mov rdx, rdi
mulx r13, rdi, r9
mov r9, rdi
mov r15, -0x2 
inc r15
adox r9, rdx
adcx rbp, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x30 ]
adcx r12, [ rsp + 0x170 ]
adcx r10, [ rsp + 0x168 ]
adcx rcx, [ rsp + 0x160 ]
adcx rbx, [ rsp + 0x178 ]
adcx r14, [ rsp + 0x180 ]
mov r9, rdi
setc r15b
clc
adcx r9, r13
adcx rdi, r13
adox r9, rbp
adox rdi, r8
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1e8 ], r11
mulx r11, r8, rbp
adcx r8, r13
adox r8, r12
mov r13, 0x7bc65c783158aea3 
mulx rbp, r12, r13
mov r13, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x1f0 ], r15b
mov [ rsp + 0x1f8 ], r14
mulx r14, r15, r13
adcx r12, r11
adcx r15, rbp
adox r12, r10
mov r10, 0x2341f27177344 
mulx rbp, r11, r10
adcx r11, r14
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx r9, [ rsp + 0x100 ]
adcx rdi, [ rsp + 0x108 ]
adcx r8, [ rsp + 0x158 ]
adcx r12, [ rsp + 0x138 ]
adox r15, rcx
adcx r15, [ rsp + 0x130 ]
movzx rcx, byte [ rsp + 0x150 ]
mov r14, [ rsp + 0x8 ]
lea rcx, [ rcx + r14 ]
adox r11, rbx
adox rbp, [ rsp + 0x1f8 ]
movzx r14, byte [ rsp + 0x1f0 ]
adox r14, rdx
adcx r11, [ rsp + 0x148 ]
adcx rbp, [ rsp + 0x140 ]
adcx rcx, r14
mov rbx, 0xffffffffffffffff 
mov rdx, r9
mulx r14, r9, rbx
mov r10, r9
mov r13, -0x2 
inc r13
adox r10, r14
mov r13, r9
adox r13, r14
setc bl
clc
adcx r9, rdx
adcx r10, rdi
adcx r13, r8
mov r9, 0xfdc1767ae2ffffff 
mulx r8, rdi, r9
adox rdi, r14
adcx rdi, r12
mov r12, 0x7bc65c783158aea3 
mulx r9, r14, r12
adox r14, r8
adcx r14, r15
mov r15, 0x6cfc5fd681c52056 
mulx r12, r8, r15
adox r8, r9
adcx r8, r11
mov r11, 0x2341f27177344 
mulx r15, r9, r11
adox r9, r12
adcx r9, rbp
mov rdx, 0x0 
adox r15, rdx
mov rbp, -0x3 
inc rbp
adox r10, [ rsp + 0x0 ]
adox r13, [ rsp + 0x10 ]
adcx r15, rcx
movzx rcx, bl
adcx rcx, rdx
adox rdi, [ rsp + 0x190 ]
adox r14, [ rsp + 0x188 ]
adox r8, [ rsp + 0x1b0 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r12, rbx, r10
mov rbp, rbx
clc
adcx rbp, r10
adox r9, [ rsp + 0x1b8 ]
adox r15, [ rsp + 0x1c0 ]
adox rcx, [ rsp + 0x1c8 ]
mov rbp, rbx
setc r11b
clc
adcx rbp, r12
seto dl
mov [ rsp + 0x200 ], rcx
mov rcx, 0x0 
dec rcx
movzx r11, r11b
adox r11, rcx
adox r13, rbp
setc r11b
clc
adcx r13, [ rsp - 0x48 ]
mov rbp, r12
setc cl
clc
mov byte [ rsp + 0x208 ], dl
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rbp, rbx
adox rbp, rdi
mov rdi, 0xfdc1767ae2ffffff 
mov rdx, rdi
mulx rbx, rdi, r10
adcx rdi, r12
adox rdi, r14
mulx r12, r14, r13
mov r11, 0x7bc65c783158aea3 
mov rdx, r11
mov [ rsp + 0x210 ], r12
mulx r12, r11, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x218 ], rdi
mov [ rsp + 0x220 ], rbp
mulx rbp, rdi, r13
mov rdx, rdi
mov byte [ rsp + 0x228 ], cl
seto cl
mov [ rsp + 0x230 ], r15
mov r15, -0x2 
inc r15
adox rdx, rbp
mov r15, rdi
adox r15, rbp
adox r14, rbp
adcx r11, rbx
seto bl
mov rbp, 0x0 
dec rbp
movzx rcx, cl
adox rcx, rbp
adox r8, r11
mov rcx, 0x6cfc5fd681c52056 
xchg rdx, r10
mulx rbp, r11, rcx
adcx r11, r12
adox r11, r9
mov r9, 0x2341f27177344 
mulx rcx, r12, r9
adcx r12, rbp
mov rdx, 0x0 
adcx rcx, rdx
adox r12, [ rsp + 0x230 ]
adox rcx, [ rsp + 0x200 ]
movzx rbp, byte [ rsp + 0x208 ]
adox rbp, rdx
mov rdx, [ rsp - 0x8 ]
add byte [ rsp + 0x228 ], 0xFF
adcx rdx, [ rsp + 0x220 ]
mov r9, [ rsp + 0x218 ]
adcx r9, [ rsp + 0x78 ]
adcx r8, [ rsp + 0x70 ]
adcx r11, [ rsp + 0x1e0 ]
adcx r12, [ rsp + 0x1d8 ]
adcx rcx, [ rsp + 0x1d0 ]
adox rdi, r13
adox r10, rdx
adox r15, r9
adox r14, r8
seto dil
mov rdx, -0x2 
inc rdx
adox r10, [ rsp + 0x68 ]
adox r15, [ rsp + 0xc8 ]
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r10
mulx r8, r10, r9
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x238 ], rcx
mov [ rsp + 0x240 ], r12
mulx r12, rcx, r9
adcx rbp, [ rsp + 0x1e8 ]
mov r9, rcx
mov [ rsp + 0x248 ], rbp
setc bpl
clc
adcx r9, r12
adox r14, [ rsp + 0xb8 ]
mov byte [ rsp + 0x250 ], bpl
mov rbp, rcx
mov [ rsp + 0x258 ], r11
seto r11b
mov byte [ rsp + 0x260 ], dil
mov rdi, -0x2 
inc rdi
adox rbp, rdx
adcx rcx, r12
mov rbp, 0x7bc65c783158aea3 
mov byte [ rsp + 0x268 ], r11b
mulx r11, rdi, rbp
adcx r10, r12
adox r9, r15
xchg rdx, r13
mulx r12, r15, rbp
adcx rdi, r8
adox rcx, r14
seto r8b
mov r14, 0x0 
dec r14
movzx rbx, bl
adox rbx, r14
adox r15, [ rsp + 0x210 ]
mov rbx, 0x6cfc5fd681c52056 
xchg rdx, r13
mulx rbp, r14, rbx
xchg rdx, rbx
mov [ rsp + 0x270 ], rcx
mov [ rsp + 0x278 ], r9
mulx r9, rcx, r13
adox rcx, r12
mov r12, 0x2341f27177344 
mov rdx, r12
mov [ rsp + 0x280 ], rdi
mulx rdi, r12, r13
adox r12, r9
mov r13, 0x0 
adox rdi, r13
movzx r9, byte [ rsp + 0x260 ]
dec r13
adox r9, r13
adox r15, [ rsp + 0x258 ]
adox rcx, [ rsp + 0x240 ]
adox r12, [ rsp + 0x238 ]
adox rdi, [ rsp + 0x248 ]
adcx r14, r11
mulx r11, r9, rbx
adcx r9, rbp
mov rbx, 0x0 
adcx r11, rbx
movzx rbp, byte [ rsp + 0x250 ]
adox rbp, rbx
add byte [ rsp + 0x268 ], 0x7F
adox r15, [ rsp + 0xb0 ]
movzx r8, r8b
adcx r8, r13
adcx r15, r10
adox rcx, [ rsp + 0xc0 ]
adcx rcx, [ rsp + 0x280 ]
adox r12, [ rsp + 0xf8 ]
adox rdi, [ rsp + 0xe8 ]
adox rbp, [ rsp + 0xf0 ]
adcx r14, r12
adcx r9, rdi
adcx r11, rbp
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov r8, [ rsp + 0x278 ]
mov r12, 0xffffffffffffffff 
sub r8, r12
mov rdi, [ rsp + 0x270 ]
sbb rdi, r12
mov rbp, r15
sbb rbp, r12
mov rbx, rcx
mov r13, 0xfdc1767ae2ffffff 
sbb rbx, r13
mov rdx, r14
mov r13, 0x7bc65c783158aea3 
sbb rdx, r13
mov r13, r9
mov r12, 0x6cfc5fd681c52056 
sbb r13, r12
mov r12, r11
mov [ rsp + 0x288 ], rbx
mov rbx, 0x2341f27177344 
sbb r12, rbx
movzx rbx, r10b
sbb rbx, 0x00000000
cmovc r13, r9
cmovc r12, r11
cmovc rbp, r15
cmovc r8, [ rsp + 0x278 ]
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], rbp
mov [ rbx + 0x28 ], r13
cmovc rdi, [ rsp + 0x270 ]
mov [ rbx + 0x8 ], rdi
cmovc rdx, r14
mov [ rbx + 0x20 ], rdx
mov r15, [ rsp + 0x288 ]
cmovc r15, rcx
mov [ rbx + 0x18 ], r15
mov [ rbx + 0x30 ], r12
mov [ rbx + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 784
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7208
; seed 2527649816573419 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13280333 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=24, initial num_batches=31): 238723 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01797567877251271
; number reverted permutation / tried permutation: 75857 / 90075 =84.215%
; number reverted decision / tried decision: 70901 / 89924 =78.845%
; validated in 475.832s
