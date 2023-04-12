SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 776
mov rdx, [ rsi + 0x28 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rdi
mulx rdi, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], rdi
mulx rdi, r15, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], r14
mulx r14, r13, rdx
xor rdx, rdx
adox r11, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
mov rdx, r15
adcx rdx, rbx
adox rbp, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rbp
mulx rbp, rcx, [ rsi + 0x28 ]
setc dl
clc
adcx rax, rbp
mov rbp, r15
mov [ rsp + 0x20 ], rax
seto al
mov [ rsp + 0x28 ], rcx
mov rcx, -0x2 
inc rcx
adox rbp, rdi
adox r15, rdi
adox r12, rdi
mov dil, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], r12
mulx r12, rcx, [ rsi + 0x18 ]
adcx r8, r10
adcx rcx, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], rbp
mulx rbp, r15, [ rsi + 0x20 ]
adcx rcx, r12
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], rcx
mulx rcx, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r11
mov byte [ rsp + 0x68 ], dil
mulx rdi, r11, [ rsi + 0x0 ]
adcx r13, r8
setc dl
clc
adcx r10, rdi
adcx r15, r9
adcx r12, rbp
adcx rcx, [ rsp + 0x8 ]
mov r9b, dl
mov rdx, [ rsi + 0x30 ]
mulx rbp, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], r8
mulx r8, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x78 ], r9b
mov [ rsp + 0x80 ], r13
mulx r13, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], rcx
mov [ rsp + 0x90 ], r12
mulx r12, rcx, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x98 ], r15
mov r15, -0x2 
inc r15
adox rdi, rbp
adox r8, [ rsp + 0x0 ]
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r8
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], r11
mov [ rsp + 0xc0 ], r8
mulx r8, r11, [ rsi + 0x0 ]
adcx rdi, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
adcx rcx, r10
mov rdx, 0x0 
adcx r12, rdx
clc
mov r10, -0x1 
movzx rax, al
adcx rax, r10
adcx r14, rdi
mov rdx, [ rsi + 0x30 ]
mulx rdi, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r12
mulx r12, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], rcx
mov [ rsp + 0xe8 ], r14
mulx r14, rcx, [ rsi + 0x20 ]
adcx r11, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r11
mulx r11, r15, [ rsi + 0x18 ]
adox r9, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], r11
mulx r11, r9, [ rsi + 0x0 ]
adox rcx, r13
adcx r9, r8
mov rdx, [ rsi + 0x30 ]
mulx r8, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rcx
mov [ rsp + 0x110 ], r8
mulx r8, rcx, [ rsi + 0x18 ]
adox r10, r14
adcx rax, r11
adox r13, r12
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx rcx, [ rsp - 0x18 ]
adcx r15, r8
mov r12, [ rsp - 0x38 ]
seto r14b
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r12, [ rsp - 0x48 ]
mov rbp, 0x6cfc5fd681c52056 
mov rdx, rbx
mulx r11, rbx, rbp
mov r8, [ rsp + 0x60 ]
seto bpl
mov [ rsp + 0x118 ], r13
movzx r13, byte [ rsp + 0x68 ]
mov [ rsp + 0x120 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox r13, r10
adox r8, [ rsp + 0x50 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x128 ], r14b
mulx r14, r10, rdx
adcx r10, [ rsp + 0x100 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x130 ], r10
mov [ rsp + 0x138 ], r15
mulx r15, r10, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], rcx
mulx rcx, r13, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x148 ], rcx
mov rcx, 0x0 
dec rcx
movzx rbp, bpl
adox rbp, rcx
adox rbx, [ rsp - 0x40 ]
adox r10, r11
seto bpl
inc rcx
adox r13, r8
mov r11, [ rsp + 0x18 ]
seto r8b
dec rcx
movzx rdx, dl
adox rdx, rcx
adox r11, [ rsp + 0x48 ]
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp + 0xe8 ]
adox r12, [ rsp + 0xf0 ]
adox rbx, r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x158 ], r12
mov [ rsp + 0x160 ], r9
mulx r9, r12, r13
adox r10, rax
movzx rax, bpl
lea rax, [ rax + r15 ]
adox rax, rdi
mov rdx, [ rsi + 0x20 ]
mulx r15, rdi, [ rsi + 0x18 ]
adcx rdi, r14
mov rdx, [ rsi + 0x18 ]
mulx rbp, r14, [ rsi + 0x28 ]
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x168 ], r14
mulx r14, r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], rdi
mov [ rsp + 0x178 ], r9
mulx r9, rdi, [ rsi + 0x30 ]
adcx rdi, rbp
setc dl
clc
adcx r15, [ rsp + 0x148 ]
adcx rcx, r14
seto bpl
mov r14, 0x0 
dec r14
movzx r8, r8b
adox r8, r14
adox r11, r15
mov r8b, dl
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x180 ], rdi
mov [ rsp + 0x188 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
adcx rdi, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x190 ], r11
mulx r11, rbx, [ rsi + 0x8 ]
adox rcx, [ rsp + 0x160 ]
adox rdi, [ rsp + 0x158 ]
adcx rbx, r12
adcx r15, r11
adox rbx, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x30 ]
mulx r11, r12, [ rsi + 0x8 ]
adcx r12, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x198 ], rbx
mulx rbx, r14, r13
movzx rdx, r8b
lea rdx, [ rdx + r9 ]
adox r15, r10
mov r10, r14
seto r9b
mov r8, -0x2 
inc r8
adox r10, rbx
setc r8b
clc
mov [ rsp + 0x1a0 ], rdx
mov rdx, -0x1 
movzx r9, r9b
adcx r9, rdx
adcx rax, r12
mov r12, r14
adox r12, rbx
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r13
mov [ rsp + 0x1a8 ], rax
mulx rax, r13, r9
adox r13, rbx
movzx rbx, r8b
lea rbx, [ rbx + r11 ]
movzx r11, bpl
adcx r11, rbx
mov rbp, 0x7bc65c783158aea3 
mulx rbx, r8, rbp
adox r8, rax
mov rax, 0x6cfc5fd681c52056 
mulx r9, rbp, rax
adox rbp, rbx
setc bl
clc
adcx r14, rdx
adcx r10, [ rsp + 0x190 ]
adcx r12, rcx
adcx r13, rdi
adox r9, [ rsp + 0x188 ]
mov r14, [ rsp + 0x178 ]
mov rdx, 0x0 
adox r14, rdx
adcx r8, [ rsp + 0x198 ]
adcx rbp, r15
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rsi + 0x10 ]
adcx r9, [ rsp + 0x1a8 ]
mov rdx, [ rsi + 0x10 ]
mulx rax, r15, rdx
mov rdx, -0x2 
inc rdx
adox r10, [ rsp - 0x8 ]
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x1b0 ], bl
mov [ rsp + 0x1b8 ], r9
mulx r9, rbx, r10
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1c0 ], r9
mov [ rsp + 0x1c8 ], rbx
mulx rbx, r9, r10
adcx r14, r11
setc r11b
clc
adcx rcx, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x1d0 ], r11b
mov [ rsp + 0x1d8 ], rbx
mulx rbx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1e0 ], r9
mov [ rsp + 0x1e8 ], r14
mulx r14, r9, [ rsi + 0x30 ]
adcx r15, rdi
adcx rax, [ rsp + 0xd0 ]
adox rcx, r12
mov rdx, [ rsi + 0x20 ]
mulx rdi, r12, [ rsi + 0x10 ]
adcx r12, [ rsp + 0xc0 ]
adcx r11, rdi
adcx r9, rbx
adox r15, r13
adox rax, r8
adox r12, rbp
mov rdx, 0xffffffffffffffff 
mulx r8, r13, r10
mov rbp, r13
setc bl
clc
adcx rbp, r8
adox r11, [ rsp + 0x1b8 ]
mov rdi, r13
adcx rdi, r8
adox r9, [ rsp + 0x1e8 ]
seto dl
mov [ rsp + 0x1f0 ], r9
mov r9, -0x2 
inc r9
adox r13, r10
adox rbp, rcx
adox rdi, r15
mov r13, 0x7bc65c783158aea3 
xchg rdx, r13
mulx r15, rcx, r10
mov r9, 0x6cfc5fd681c52056 
mov rdx, r9
mov byte [ rsp + 0x1f8 ], r13b
mulx r13, r9, r10
adcx r8, [ rsp + 0x1e0 ]
adox r8, rax
adcx rcx, [ rsp + 0x1d8 ]
adcx r9, r15
adox rcx, r12
adox r9, r11
seto r10b
mov rax, -0x2 
inc rax
adox rbp, [ rsp - 0x20 ]
adox rdi, [ rsp + 0x140 ]
mulx r11, r12, rbp
adox r8, [ rsp + 0x138 ]
adcx r13, [ rsp + 0x1c8 ]
mov r15, [ rsp + 0x1c0 ]
mov rax, 0x0 
adcx r15, rax
mov rax, 0xfdc1767ae2ffffff 
mov rdx, rbp
mov [ rsp + 0x200 ], r11
mulx r11, rbp, rax
adox rcx, [ rsp + 0x130 ]
adox r9, [ rsp + 0x170 ]
movzx rax, bl
lea rax, [ rax + r14 ]
movzx r14, byte [ rsp + 0x1d0 ]
movzx rbx, byte [ rsp + 0x1b0 ]
lea r14, [ r14 + rbx ]
clc
mov rbx, -0x1 
movzx r10, r10b
adcx r10, rbx
adcx r13, [ rsp + 0x1f0 ]
setc r10b
movzx rbx, byte [ rsp + 0x1f8 ]
clc
mov [ rsp + 0x208 ], r9
mov r9, -0x1 
adcx rbx, r9
adcx r14, rax
seto bl
inc r9
mov rax, -0x1 
movzx r10, r10b
adox r10, rax
adox r14, r15
seto r15b
adc r15b, 0x0
movzx r15, r15b
mov r10, 0xffffffffffffffff 
mulx rax, r9, r10
add bl, 0xFF
adcx r13, [ rsp + 0x168 ]
adcx r14, [ rsp + 0x180 ]
movzx r15, r15b
movzx rbx, r15b
adcx rbx, [ rsp + 0x1a0 ]
mov r15, r9
adox r15, rax
mov r10, r9
adox r10, rax
mov [ rsp + 0x210 ], rbx
setc bl
clc
adcx r9, rdx
adcx r15, rdi
mov r9, 0x7bc65c783158aea3 
mov byte [ rsp + 0x218 ], bl
mulx rbx, rdi, r9
adox rbp, rax
adcx r10, r8
adox rdi, r11
adox r12, rbx
adcx rbp, rcx
mov r8, 0x2341f27177344 
mulx rcx, r11, r8
adox r11, [ rsp + 0x200 ]
mov rdx, 0x0 
adox rcx, rdx
mov rax, -0x3 
inc rax
adox r15, [ rsp + 0xb8 ]
mov rdx, r15
mulx rbx, r15, r8
mov rax, 0xfdc1767ae2ffffff 
mulx r8, r9, rax
mov rax, 0xffffffffffffffff 
mov [ rsp + 0x220 ], rbx
mov [ rsp + 0x228 ], r15
mulx r15, rbx, rax
adcx rdi, [ rsp + 0x208 ]
adcx r12, r13
adox r10, [ rsp + 0xb0 ]
adcx r11, r14
adcx rcx, [ rsp + 0x210 ]
adox rbp, [ rsp + 0x98 ]
adox rdi, [ rsp + 0x90 ]
movzx r13, byte [ rsp + 0x218 ]
mov r14, 0x0 
adcx r13, r14
adox r12, [ rsp + 0x88 ]
adox r11, [ rsp + 0xc8 ]
mov rax, rbx
clc
adcx rax, rdx
mov rax, rbx
mov [ rsp + 0x230 ], r11
seto r11b
mov [ rsp + 0x238 ], r13
mov r13, -0x3 
inc r13
adox rax, r15
adox rbx, r15
adox r9, r15
adcx rax, r10
mov r15, 0x7bc65c783158aea3 
mulx r14, r10, r15
adox r10, r8
adcx rbx, rbp
seto r8b
inc r13
adox rax, [ rsp + 0x28 ]
adcx r9, rdi
adox rbx, [ rsp + 0x20 ]
xchg rdx, r15
mulx rdi, rbp, rax
adcx r10, r12
adox r9, [ rsp + 0x40 ]
adox r10, [ rsp + 0x38 ]
mov r12, 0x6cfc5fd681c52056 
mov rdx, rax
mulx r13, rax, r12
xchg rdx, r15
mov [ rsp + 0x240 ], r13
mov [ rsp + 0x248 ], r10
mulx r10, r13, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x250 ], r9
mulx r9, r12, [ rsi + 0x28 ]
setc dl
clc
mov [ rsp + 0x258 ], rbx
mov rbx, -0x1 
movzx r11, r11b
adcx r11, rbx
adcx rcx, [ rsp + 0xe0 ]
setc r11b
clc
movzx r8, r8b
adcx r8, rbx
adcx r14, r13
adcx r10, [ rsp + 0x228 ]
mov r8, [ rsp + 0x220 ]
mov r13, 0x0 
adcx r8, r13
mov r13, [ rsp + 0x238 ]
clc
movzx r11, r11b
adcx r11, rbx
adcx r13, [ rsp + 0xd8 ]
setc r11b
clc
movzx rdx, dl
adcx rdx, rbx
adcx r14, [ rsp + 0x230 ]
adcx r10, rcx
adox r14, [ rsp + 0x58 ]
adox r10, [ rsp + 0x80 ]
adcx r8, r13
mov rdx, 0xffffffffffffffff 
mulx r13, rcx, r15
movzx rbx, r11b
mov rdx, 0x0 
adcx rbx, rdx
movzx r11, byte [ rsp + 0x78 ]
clc
mov rdx, -0x1 
adcx r11, rdx
adcx r12, [ rsp + 0x10 ]
mov r11, 0x0 
adcx r9, r11
adox r12, r8
mov r8, rcx
clc
adcx r8, r13
mov r11, rcx
adcx r11, r13
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x260 ], r12
mov [ rsp + 0x268 ], r10
mulx r10, r12, r15
adcx r12, r13
adox r9, rbx
adcx rbp, r10
adcx rax, rdi
seto dil
mov r13, -0x2 
inc r13
adox rcx, r15
adox r8, [ rsp + 0x258 ]
adox r11, [ rsp + 0x250 ]
adox r12, [ rsp + 0x248 ]
mov rcx, 0x2341f27177344 
mov rdx, r15
mulx rbx, r15, rcx
adox rbp, r14
adox rax, [ rsp + 0x268 ]
adcx r15, [ rsp + 0x240 ]
mov rdx, 0x0 
adcx rbx, rdx
adox r15, [ rsp + 0x260 ]
adox rbx, r9
movzx r14, byte [ rsp + 0x128 ]
mov r10, [ rsp + 0x110 ]
lea r14, [ r14 + r10 ]
clc
adcx r8, [ rsp + 0x70 ]
mov r10, 0xffffffffffffffff 
mov rdx, r8
mulx r9, r8, r10
mov r13, r8
seto r10b
mov rcx, -0x2 
inc rcx
adox r13, rdx
adcx r11, [ rsp + 0xa8 ]
adcx r12, [ rsp + 0xa0 ]
adcx rbp, [ rsp + 0xf8 ]
adcx rax, [ rsp + 0x108 ]
adcx r15, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x118 ]
mov r13, r8
setc cl
clc
adcx r13, r9
adcx r8, r9
adox r13, r11
adox r8, r12
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x270 ], r8
mulx r8, r12, r11
adcx r12, r9
mov r9, 0x7bc65c783158aea3 
mov [ rsp + 0x278 ], r13
mulx r13, r11, r9
adcx r11, r8
mov r8, 0x6cfc5fd681c52056 
mov [ rsp + 0x280 ], r14
mulx r14, r9, r8
adcx r9, r13
adox r12, rbp
movzx rbp, r10b
movzx rdi, dil
lea rbp, [ rbp + rdi ]
mov rdi, 0x2341f27177344 
mulx r13, r10, rdi
adcx r10, r14
adox r11, rax
adox r9, r15
mov rdx, 0x0 
adcx r13, rdx
adox r10, rbx
clc
mov rax, -0x1 
movzx rcx, cl
adcx rcx, rax
adcx rbp, [ rsp + 0x280 ]
adox r13, rbp
seto r15b
adc r15b, 0x0
movzx r15, r15b
mov rcx, [ rsp + 0x278 ]
mov rbx, 0xffffffffffffffff 
sub rcx, rbx
mov r14, [ rsp + 0x270 ]
sbb r14, rbx
mov rbp, r12
sbb rbp, rbx
mov rdx, r11
mov rax, 0xfdc1767ae2ffffff 
sbb rdx, rax
mov rax, r9
mov rbx, 0x7bc65c783158aea3 
sbb rax, rbx
mov rbx, r10
sbb rbx, r8
mov r8, r13
sbb r8, rdi
movzx rdi, r15b
sbb rdi, 0x00000000
cmovc rbp, r12
cmovc rdx, r11
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], rbp
cmovc rbx, r10
mov [ rdi + 0x28 ], rbx
cmovc r14, [ rsp + 0x270 ]
cmovc r8, r13
mov [ rdi + 0x18 ], rdx
cmovc rcx, [ rsp + 0x278 ]
mov [ rdi + 0x0 ], rcx
cmovc rax, r9
mov [ rdi + 0x8 ], r14
mov [ rdi + 0x20 ], rax
mov [ rdi + 0x30 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 776
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.8674
; seed 2957537254069149 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7326477 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 141880 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019365378475903222
; number reverted permutation / tried permutation: 60422 / 89899 =67.211%
; number reverted decision / tried decision: 57567 / 90100 =63.892%
; validated in 329.325s
