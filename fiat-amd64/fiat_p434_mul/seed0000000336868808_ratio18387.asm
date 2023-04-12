SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 744
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r10
mulx r10, r9, [ rax + 0x8 ]
test al, al
adox r9, r11
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x38 ], r9
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r9
mulx r9, r13, [ rax + 0x10 ]
adox r13, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r13
mulx r13, r10, [ rsi + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rbx
mulx rbx, r11, [ rsi + 0x28 ]
adox r10, r9
adox r11, r13
mov rdx, [ rax + 0x8 ]
mulx r13, r9, [ rsi + 0x10 ]
adox rcx, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rcx
mulx rcx, rbx, [ rsi + 0x0 ]
adcx r9, r14
adox r15, r8
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], r11
mulx r11, r15, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r9
mulx r9, r10, r15
adcx r8, r13
setc r13b
clc
adcx rbx, r11
mov r11, 0x0 
adox rdi, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rdi
mulx rdi, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], r14
mulx r14, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x38 ], r13b
mov [ rsp + 0x40 ], r11
mulx r11, r13, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r13, rdi
adox r8, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, rdi, [ rax + 0x10 ]
adcx rdi, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x48 ], r8
mulx r8, rcx, [ rax + 0x18 ]
adcx rcx, r11
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x50 ], r8
mulx r8, r11, [ rsi + 0x8 ]
adox rbp, r14
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x58 ], rbp
mulx rbp, r14, [ rsi + 0x18 ]
adox r11, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], r11
mulx r11, r12, [ rax + 0x0 ]
setc dl
clc
adcx r14, r11
mov r11b, dl
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x68 ], r14
mov [ rsp + 0x70 ], r12
mulx r12, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x78 ], r11b
mov [ rsp + 0x80 ], r13
mulx r13, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], rdi
mulx rdi, rcx, [ rax + 0x10 ]
adcx rcx, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], rcx
mulx rcx, rbp, [ rax + 0x28 ]
adox rbp, r8
adox r14, rcx
adcx r11, rdi
mov rdx, [ rax + 0x20 ]
mulx rdi, r8, [ rsi + 0x18 ]
adcx r8, r13
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, [ rax + 0x30 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xa0 ], r8
mov [ rsp + 0xa8 ], r11
mulx r11, r8, [ rsi + 0x18 ]
adcx r8, rdi
adcx r13, r11
mov rdx, 0x7bc65c783158aea3 
mulx r11, rdi, r15
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0xb0 ], r13
mov [ rsp + 0xb8 ], r8
mulx r8, r13, r15
mov rdx, 0x0 
adox r12, rdx
mov [ rsp + 0xc0 ], r12
mov r12, r10
mov [ rsp + 0xc8 ], r14
mov r14, -0x3 
inc r14
adox r12, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xd0 ], rbp
mulx rbp, r14, r15
mov rdx, r10
adox rdx, r9
adox r14, r9
setc r9b
clc
adcx r10, r15
adcx r12, rbx
adcx rdx, [ rsp + 0x90 ]
adox rdi, rbp
adcx r14, [ rsp + 0x88 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0xd8 ], rbx
mov [ rsp + 0xe0 ], rdi
mulx rdi, rbx, r15
movzx r15, r9b
lea r15, [ r15 + rcx ]
setc cl
clc
adcx r12, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe8 ], r15
mulx r15, r9, [ rax + 0x20 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xf0 ], r15
mov byte [ rsp + 0xf8 ], cl
mulx rcx, r15, r12
adox r13, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], rcx
mulx rcx, r11, [ rax + 0x10 ]
adcx r10, [ rsp + 0x80 ]
adox rbx, r8
adcx r14, [ rsp + 0x48 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x108 ], r15
mulx r15, r8, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x110 ], r15
mov [ rsp + 0x118 ], r14
mulx r14, r15, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], rbx
mulx rbx, r10, [ rax + 0x8 ]
setc dl
clc
adcx r10, rbp
adcx r11, rbx
seto bpl
mov rbx, -0x2 
inc rbx
adox r15, [ rsp - 0x10 ]
mov bl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x130 ], r15
mov [ rsp + 0x138 ], r11
mulx r11, r15, [ rsi + 0x20 ]
adcx r15, rcx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x140 ], r15
mulx r15, rcx, [ rax + 0x10 ]
adox rcx, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x148 ], rcx
mulx rcx, r14, [ rsi + 0x20 ]
adcx r14, r11
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x150 ], r14
mulx r14, r11, [ rsi + 0x20 ]
adcx r11, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x158 ], r11
mulx r11, rcx, [ rax + 0x18 ]
movzx rdx, bpl
lea rdx, [ rdx + rdi ]
mov rdi, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x160 ], r10
mulx r10, rbp, [ rax + 0x18 ]
adox rbp, r15
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x168 ], rbp
mulx rbp, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x170 ], rdi
mov [ rsp + 0x178 ], r13
mulx r13, rdi, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x180 ], bl
mov [ rsp + 0x188 ], rbp
mulx rbp, rbx, [ rax + 0x30 ]
adcx rbx, r14
adox r9, r10
mov rdx, 0xffffffffffffffff 
mulx r10, r14, r12
setc dl
mov [ rsp + 0x190 ], r9
movzx r9, byte [ rsp + 0x38 ]
clc
mov [ rsp + 0x198 ], rbx
mov rbx, -0x1 
adcx r9, rbx
adcx rcx, [ rsp + 0x30 ]
adcx rdi, r11
mov r9, r14
seto r11b
inc rbx
adox r9, r10
movzx rbx, dl
lea rbx, [ rbx + rbp ]
mov rbp, r14
adox rbp, r10
mov rdx, [ rsi + 0x10 ]
mov byte [ rsp + 0x1a0 ], r11b
mov [ rsp + 0x1a8 ], rbx
mulx rbx, r11, [ rax + 0x28 ]
adcx r11, r13
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1b0 ], r11
mulx r11, r13, [ rsi + 0x10 ]
adcx r13, rbx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1b8 ], r13
mulx r13, rbx, [ rsi + 0x0 ]
adox r8, r10
seto dl
movzx r10, byte [ rsp + 0x78 ]
mov [ rsp + 0x1c0 ], rdi
mov rdi, 0x0 
dec rdi
adox r10, rdi
adox rbx, [ rsp + 0x50 ]
adox r13, [ rsp - 0x18 ]
adox r15, [ rsp - 0x28 ]
mov r10, [ rsp + 0x188 ]
mov rdi, 0x0 
adox r10, rdi
adc r11, 0x0
add byte [ rsp + 0xf8 ], 0x7F
adox rbx, [ rsp + 0xe0 ]
movzx rdi, byte [ rsp + 0x180 ]
mov [ rsp + 0x1c8 ], r11
mov r11, -0x1 
adcx rdi, r11
adcx rbx, [ rsp + 0x58 ]
adox r13, [ rsp + 0x178 ]
adcx r13, [ rsp + 0x60 ]
adox r15, [ rsp + 0x128 ]
adcx r15, [ rsp + 0xd0 ]
adox r10, [ rsp + 0x170 ]
adcx r10, [ rsp + 0xc8 ]
setc dil
clc
adcx r14, r12
adcx r9, [ rsp + 0x120 ]
movzx rdi, dil
movzx r14, dil
adox r14, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0x118 ]
adcx r8, rbx
seto bl
inc r11
adox r9, [ rsp - 0x30 ]
adox rbp, [ rsp + 0x18 ]
adox r8, [ rsp + 0x28 ]
mov rdi, [ rsp + 0x108 ]
seto r11b
mov byte [ rsp + 0x1d0 ], bl
mov rbx, 0x0 
dec rbx
movzx rdx, dl
adox rdx, rbx
adox rdi, [ rsp + 0x110 ]
adcx rdi, r13
mov rdx, 0x6cfc5fd681c52056 
mulx rbx, r13, r12
adox r13, [ rsp + 0x100 ]
adcx r13, r15
mov r15, 0x2341f27177344 
mov rdx, r12
mov [ rsp + 0x1d8 ], r8
mulx r8, r12, r15
adox r12, rbx
adcx r12, r10
mov rdx, 0x0 
adox r8, rdx
mov r10, 0xffffffffffffffff 
mov rdx, r9
mulx rbx, r9, r10
adcx r8, r14
mov r14, r9
mov r15, -0x2 
inc r15
adox r14, rdx
setc r14b
clc
movzx r11, r11b
adcx r11, r15
adcx rdi, rcx
adcx r13, [ rsp + 0x1c0 ]
mov rcx, r9
setc r11b
clc
adcx rcx, rbx
adcx r9, rbx
adox rcx, rbp
mov rbp, 0xfdc1767ae2ffffff 
mulx r10, r15, rbp
adcx r15, rbx
adox r9, [ rsp + 0x1d8 ]
adox r15, rdi
mov rbx, 0x7bc65c783158aea3 
mulx rbp, rdi, rbx
adcx rdi, r10
adox rdi, r13
seto r13b
mov r10, -0x2 
inc r10
adox rcx, [ rsp + 0x70 ]
adox r9, [ rsp + 0x68 ]
adox r15, [ rsp + 0x98 ]
mov r10, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x1e0 ], r13b
mulx r13, rbx, r10
adox rdi, [ rsp + 0xa8 ]
adcx rbx, rbp
mov rbp, 0x2341f27177344 
mov [ rsp + 0x1e8 ], rbx
mulx rbx, r10, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1f0 ], r8
mulx r8, rbp, rcx
adcx r10, r13
mov r13, rbp
seto dl
mov [ rsp + 0x1f8 ], r10
mov r10, -0x2 
inc r10
adox r13, r8
mov r10, rbp
mov byte [ rsp + 0x200 ], dl
setc dl
clc
adcx r10, rcx
adcx r13, r9
adox rbp, r8
adcx rbp, r15
movzx r10, dl
lea r10, [ r10 + rbx ]
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r9
mulx r15, r9, rcx
adox r9, r8
mov rbx, 0x7bc65c783158aea3 
mov rdx, rcx
mulx r8, rcx, rbx
adox rcx, r15
adcx r9, rdi
mov rdi, 0x6cfc5fd681c52056 
mulx rbx, r15, rdi
adox r15, r8
mov r8, 0x2341f27177344 
mov [ rsp + 0x208 ], r15
mulx r15, rdi, r8
adox rdi, rbx
setc dl
clc
adcx r13, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x160 ]
adcx r9, [ rsp + 0x138 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x210 ], rdi
mulx rdi, r8, rbx
mov rbx, r8
mov [ rsp + 0x218 ], rcx
setc cl
clc
adcx rbx, rdi
mov byte [ rsp + 0x220 ], cl
mov rcx, 0x0 
adox r15, rcx
movzx rcx, r14b
mov [ rsp + 0x228 ], r15
movzx r15, byte [ rsp + 0x1d0 ]
lea rcx, [ rcx + r15 ]
mov r15, r8
mov r14, -0x2 
inc r14
adox r15, rdx
adox rbx, rbp
seto r15b
inc r14
mov rbp, -0x1 
movzx r11, r11b
adox r11, rbp
adox r12, [ rsp + 0x1b0 ]
mov r11, [ rsp + 0x1f0 ]
adox r11, [ rsp + 0x1b8 ]
adcx r8, rdi
adox rcx, [ rsp + 0x1c8 ]
setc r14b
clc
movzx r15, r15b
adcx r15, rbp
adcx r9, r8
setc r15b
movzx r8, byte [ rsp + 0x1e0 ]
clc
adcx r8, rbp
adcx r12, [ rsp + 0x1e8 ]
adcx r11, [ rsp + 0x1f8 ]
adcx r10, rcx
seto r8b
adc r8b, 0x0
movzx r8, r8b
add byte [ rsp + 0x200 ], 0x7F
adox r12, [ rsp + 0xa0 ]
movzx r13, r13b
adcx r13, rbp
adcx r12, [ rsp + 0x218 ]
adox r11, [ rsp + 0xb8 ]
adox r10, [ rsp + 0xb0 ]
adcx r11, [ rsp + 0x208 ]
adcx r10, [ rsp + 0x210 ]
mov r13, 0x7bc65c783158aea3 
mulx rbp, rcx, r13
movzx r8, r8b
movzx r13, r8b
adox r13, [ rsp + 0xe8 ]
adcx r13, [ rsp + 0x228 ]
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov [ rsp + 0x230 ], r9
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x238 ], rbx
mov byte [ rsp + 0x240 ], r15b
mulx r15, rbx, r9
add r14b, 0x7F
adox rdi, rbx
adox rcx, r15
movzx r14, byte [ rsp + 0x220 ]
mov rbx, -0x1 
adcx r14, rbx
adcx r12, [ rsp + 0x140 ]
adcx r11, [ rsp + 0x150 ]
mov r14, 0x6cfc5fd681c52056 
mulx rbx, r15, r14
adox r15, rbp
adcx r10, [ rsp + 0x158 ]
adcx r13, [ rsp + 0x198 ]
movzx r8, r8b
movzx rbp, r8b
adcx rbp, [ rsp + 0x1a8 ]
mov r8, 0x2341f27177344 
mulx r14, r9, r8
adox r9, rbx
setc dl
movzx rbx, byte [ rsp + 0x240 ]
clc
mov r8, -0x1 
adcx rbx, r8
adcx r12, rdi
mov rbx, 0x0 
adox r14, rbx
adcx rcx, r11
mov rdi, [ rsp + 0x238 ]
mov r11, -0x3 
inc r11
adox rdi, [ rsp - 0x40 ]
adcx r15, r10
adcx r9, r13
mov r10, [ rsp + 0x230 ]
adox r10, [ rsp - 0x38 ]
adox r12, [ rsp - 0x20 ]
adox rcx, [ rsp + 0x10 ]
adox r15, [ rsp + 0x8 ]
adox r9, [ rsp - 0x8 ]
adcx r14, rbp
adox r14, [ rsp + 0x0 ]
movzx r13, dl
adcx r13, rbx
mov rdx, 0xffffffffffffffff 
mulx rbx, rbp, rdi
mov r11, rbp
clc
adcx r11, rbx
adox r13, [ rsp + 0x20 ]
mov r8, rbp
seto dl
mov [ rsp + 0x248 ], r13
mov r13, -0x2 
inc r13
adox r8, rdi
adox r11, r10
adcx rbp, rbx
mov r8, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx r13, r10, r8
adox rbp, r12
adcx r10, rbx
adox r10, rcx
mov r12, 0x7bc65c783158aea3 
mulx rbx, rcx, r12
adcx rcx, r13
adox rcx, r15
mov r15, 0x6cfc5fd681c52056 
mulx r8, r13, r15
adcx r13, rbx
mov rbx, 0x2341f27177344 
mulx r12, r15, rbx
adcx r15, r8
adox r13, r9
adox r15, r14
mov rdx, 0x0 
adcx r12, rdx
adox r12, [ rsp + 0x248 ]
movzx r9, dil
adox r9, rdx
mov rdx, [ rax + 0x30 ]
mulx rdi, r14, [ rsi + 0x30 ]
mov rdx, [ rax + 0x28 ]
mulx rbx, r8, [ rsi + 0x30 ]
add byte [ rsp + 0x1a0 ], 0x7F
adox r8, [ rsp + 0xf0 ]
adox r14, rbx
mov rdx, 0x0 
adox rdi, rdx
adcx r11, [ rsp - 0x48 ]
adcx rbp, [ rsp + 0x130 ]
adcx r10, [ rsp + 0x148 ]
adcx rcx, [ rsp + 0x168 ]
adcx r13, [ rsp + 0x190 ]
adcx r8, r15
adcx r14, r12
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r12, r15, r11
adcx rdi, r9
mov r9, r15
mov rbx, -0x2 
inc rbx
adox r9, r12
mov rbx, r15
adox rbx, r12
setc dl
clc
adcx r15, r11
adcx r9, rbp
adcx rbx, r10
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, r11
mulx r10, rbp, r15
mov r15, 0x7bc65c783158aea3 
mov [ rsp + 0x250 ], rbx
mov [ rsp + 0x258 ], r9
mulx r9, rbx, r15
adox rbp, r12
adcx rbp, rcx
adox rbx, r10
adcx rbx, r13
mov rcx, 0x6cfc5fd681c52056 
mulx r12, r13, rcx
adox r13, r9
adcx r13, r8
mov r8, 0x2341f27177344 
mulx r9, r10, r8
adox r10, r12
adcx r10, r14
mov rdx, 0x0 
adox r9, rdx
adcx r9, rdi
movzx r14, r11b
adc r14, 0x0
mov r11, [ rsp + 0x258 ]
mov rdi, 0xffffffffffffffff 
sub r11, rdi
mov r12, [ rsp + 0x250 ]
sbb r12, rdi
mov rdx, rbp
sbb rdx, rdi
mov rdi, rbx
mov r8, 0xfdc1767ae2ffffff 
sbb rdi, r8
mov r8, r13
sbb r8, r15
mov r15, r10
sbb r15, rcx
mov rcx, r9
mov [ rsp + 0x260 ], r11
mov r11, 0x2341f27177344 
sbb rcx, r11
sbb r14, 0x00000000
cmovc rdx, rbp
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], rdx
cmovc rdi, rbx
cmovc rcx, r9
cmovc r8, r13
mov [ r14 + 0x18 ], rdi
mov [ r14 + 0x30 ], rcx
mov [ r14 + 0x20 ], r8
cmovc r12, [ rsp + 0x250 ]
cmovc r15, r10
mov rbp, [ rsp + 0x260 ]
cmovc rbp, [ rsp + 0x258 ]
mov [ r14 + 0x0 ], rbp
mov [ r14 + 0x28 ], r15
mov [ r14 + 0x8 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 744
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.8387
; seed 1763012220594161 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12165894 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=48, initial num_batches=31): 236552 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019443864955588138
; number reverted permutation / tried permutation: 74690 / 90250 =82.759%
; number reverted decision / tried decision: 65297 / 89749 =72.755%
; validated in 575.243s
