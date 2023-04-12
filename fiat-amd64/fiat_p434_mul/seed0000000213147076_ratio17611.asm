SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 968
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], rdi
mulx rdi, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], rcx
mulx rcx, r15, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r11
mulx r11, r8, [ rax + 0x8 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r8
mulx r8, r11, rbp
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r15
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r15
mulx r15, rcx, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], rcx
mulx rcx, r15, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x58 ], r8
mov [ rsp + 0x60 ], r11
mulx r11, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], rdi
mulx rdi, rcx, [ rsi + 0x28 ]
test al, al
adox r8, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x78 ], r8
mulx r8, rdi, [ rsi + 0x28 ]
mov rdx, r15
adcx rdx, rbp
adox rdi, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x80 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
setc dl
clc
adcx r9, r12
adcx r13, rbx
mov bl, dl
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x88 ], rcx
mulx rcx, r12, [ rsi + 0x18 ]
adcx r11, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x90 ], r12
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x98 ], r8
mov [ rsp + 0xa0 ], rdi
mulx rdi, r8, [ rsi + 0x30 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xa8 ], rdi
mov [ rsp + 0xb0 ], r8
mulx r8, rdi, rbp
setc dl
clc
adcx r10, rcx
adcx r14, [ rsp + 0x70 ]
mov cl, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb8 ], r14
mov [ rsp + 0xc0 ], r10
mulx r10, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r10
mov byte [ rsp + 0xd0 ], cl
mulx rcx, r10, [ rax + 0x18 ]
adcx r10, r12
mov rdx, 0x2341f27177344 
mov [ rsp + 0xd8 ], r10
mulx r10, r12, rbp
mov rbp, r15
seto dl
mov [ rsp + 0xe0 ], r10
mov r10, -0x2 
inc r10
adox rbp, [ rsp + 0x68 ]
adox r15, [ rsp + 0x68 ]
adcx r14, rcx
setc cl
clc
movzx rbx, bl
adcx rbx, r10
adcx r9, rbp
adox rdi, [ rsp + 0x68 ]
adox r8, [ rsp + 0x60 ]
mov rbx, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x58 ]
mov bpl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe8 ], r14
mulx r14, r10, [ rax + 0x28 ]
adcx r15, r13
adcx rdi, r11
mov rdx, [ rsp + 0xa0 ]
setc r13b
movzx r11, byte [ rsp + 0xd0 ]
clc
mov byte [ rsp + 0xf0 ], cl
mov rcx, -0x1 
adcx r11, rcx
adcx rdx, [ rsp + 0x30 ]
adox r12, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x28 ]
mov r11, [ rsp + 0xe0 ]
mov rcx, 0x0 
adox r11, rcx
mov rcx, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xf8 ], r11
mov [ rsp + 0x100 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
adcx r11, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x108 ], r15
mulx r15, r14, [ rax + 0x18 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox rcx, r8
mov rdx, [ rax + 0x18 ]
mulx r13, r8, [ rsi + 0x30 ]
adox rbx, r10
seto dl
mov r10, 0x0 
dec r10
movzx rbp, bpl
adox rbp, r10
adox r14, [ rsp + 0x98 ]
setc bpl
clc
movzx rdx, dl
adcx rdx, r10
adcx r11, r12
movzx r12, bpl
lea r12, [ r12 + rdi ]
mov rdi, [ rsp + 0x0 ]
setc bpl
clc
adcx rdi, [ rsp + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x110 ], rdi
mulx rdi, r10, [ rsi + 0x30 ]
adcx r10, [ rsp + 0x8 ]
adcx r8, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r8
mulx r8, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], r10
mov [ rsp + 0x128 ], r13
mulx r13, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x130 ], r14
mov [ rsp + 0x138 ], r11
mulx r11, r14, [ rax + 0x18 ]
setc dl
clc
adcx r10, [ rsp - 0x8 ]
adcx r13, [ rsp + 0x40 ]
mov [ rsp + 0x140 ], r12
mov r12b, dl
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0x148 ], bpl
mov [ rsp + 0x150 ], r8
mulx r8, rbp, [ rsi + 0x28 ]
adox rdi, r15
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x158 ], r12b
mulx r12, r15, [ rax + 0x28 ]
adcx r14, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x160 ], rdi
mov [ rsp + 0x168 ], r12
mulx r12, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], rdi
mulx rdi, r12, [ rax + 0x20 ]
adcx r12, r11
adcx r15, rdi
mov rdx, [ rax + 0x0 ]
mulx rdi, r11, [ rsi + 0x20 ]
setc dl
clc
adcx r9, [ rsp - 0x10 ]
adcx r10, [ rsp + 0x108 ]
adcx r13, [ rsp + 0x100 ]
adcx r14, rcx
adcx r12, rbx
adox rbp, [ rsp + 0x150 ]
adox r8, [ rsp - 0x18 ]
mov rcx, [ rsp + 0xf8 ]
seto bl
mov [ rsp + 0x180 ], r8
movzx r8, byte [ rsp + 0x148 ]
mov [ rsp + 0x188 ], rbp
mov rbp, 0x0 
dec rbp
adox r8, rbp
adox rcx, [ rsp + 0x140 ]
adcx r15, [ rsp + 0x138 ]
mov r8b, dl
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x190 ], bl
mulx rbx, rbp, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x198 ], r11
mov r11, -0x1 
inc r11
mov r11, -0x1 
movzx r8, r8b
adox r8, r11
adox rbp, [ rsp + 0x168 ]
mov r8, 0x0 
adox rbx, r8
mov r11, -0x3 
inc r11
adox rdi, [ rsp + 0x178 ]
mov r8b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1a0 ], rdi
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1a8 ], r15
mov [ rsp + 0x1b0 ], r12
mulx r12, r15, [ rax + 0x10 ]
adcx rbp, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x1b8 ], rbp
mulx rbp, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1c0 ], r14
mov [ rsp + 0x1c8 ], r13
mulx r13, r14, [ rsi + 0x20 ]
adox r15, [ rsp + 0x170 ]
adox rcx, r12
adox r11, rbp
movzx rdx, r8b
adcx rdx, rbx
mov r8, 0xffffffffffffffff 
xchg rdx, r9
mulx r12, rbx, r8
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1d0 ], r11
mulx r11, r8, rbp
mov rbp, rdx
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1d8 ], rcx
mov [ rsp + 0x1e0 ], r15
mulx r15, rcx, [ rsi + 0x20 ]
adox r14, rdi
adox rcx, r13
mov rdx, rbx
setc dil
clc
adcx rdx, r12
mov r13, rbx
mov [ rsp + 0x1e8 ], rcx
seto cl
mov [ rsp + 0x1f0 ], r14
mov r14, -0x2 
inc r14
adox r13, rbp
adox rdx, r10
adcx rbx, r12
adcx r8, r12
adox rbx, [ rsp + 0x1c8 ]
adox r8, [ rsp + 0x1c0 ]
mov r13, 0x7bc65c783158aea3 
xchg rdx, r13
mulx r12, r10, rbp
mov r14, 0x6cfc5fd681c52056 
mov rdx, r14
mov [ rsp + 0x1f8 ], r15
mulx r15, r14, rbp
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x200 ], cl
mov [ rsp + 0x208 ], r8
mulx r8, rcx, rbp
adcx r10, r11
adcx r14, r12
mov rdx, [ rax + 0x0 ]
mulx r11, rbp, [ rsi + 0x10 ]
adcx rcx, r15
mov rdx, [ rax + 0x10 ]
mulx r15, r12, [ rsi + 0x10 ]
adox r10, [ rsp + 0x1b0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x210 ], r10
mov [ rsp + 0x218 ], r15
mulx r15, r10, [ rsi + 0x18 ]
adox r14, [ rsp + 0x1a8 ]
mov rdx, 0x0 
adcx r8, rdx
movzx rdx, byte [ rsp + 0xf0 ]
clc
mov [ rsp + 0x220 ], r14
mov r14, -0x1 
adcx rdx, r14
adcx r10, [ rsp + 0xc8 ]
adox rcx, [ rsp + 0x1b8 ]
adcx r15, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x228 ], r15
mulx r15, r14, [ rax + 0x8 ]
setc dl
clc
adcx r14, r11
adcx r12, r15
movzx r11, dl
mov r15, [ rsp + 0x48 ]
lea r11, [ r11 + r15 ]
adox r8, r9
movzx r15, dil
mov r9, 0x0 
adox r15, r9
mov rdi, -0x3 
inc rdi
adox rbp, r13
adox r14, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r13, [ rax + 0x20 ]
mov rdx, 0xffffffffffffffff 
mulx rdi, r9, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x230 ], r11
mov [ rsp + 0x238 ], r10
mulx r10, r11, [ rax + 0x18 ]
adcx r11, [ rsp + 0x218 ]
adcx r13, r10
adox r12, [ rsp + 0x208 ]
adox r11, [ rsp + 0x210 ]
adox r13, [ rsp + 0x220 ]
adcx rbx, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x240 ], r13
mulx r13, r10, [ rax + 0x30 ]
adcx r10, [ rsp - 0x38 ]
adox rbx, rcx
mov rdx, r9
setc cl
clc
adcx rdx, rbp
adox r10, r8
mov rdx, r9
seto r8b
mov [ rsp + 0x248 ], r10
mov r10, -0x2 
inc r10
adox rdx, rdi
adcx rdx, r14
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov [ rsp + 0x250 ], rbp
mulx rbp, r10, r14
adox r9, rdi
movzx r14, cl
lea r14, [ r14 + r13 ]
adox r10, rdi
mov rdi, 0x7bc65c783158aea3 
mulx rcx, r13, rdi
setc dil
clc
mov [ rsp + 0x258 ], rbx
mov rbx, -0x1 
movzx r8, r8b
adcx r8, rbx
adcx r15, r14
adox r13, rbp
setc r8b
clc
movzx rdi, dil
adcx rdi, rbx
adcx r12, r9
adcx r10, r11
adcx r13, [ rsp + 0x240 ]
mov r11, 0x6cfc5fd681c52056 
mulx rbp, rdi, r11
adox rdi, rcx
adcx rdi, [ rsp + 0x258 ]
mov r9, 0x2341f27177344 
mulx rcx, r14, r9
adox r14, rbp
adcx r14, [ rsp + 0x248 ]
mov rdx, [ rsp + 0x250 ]
seto bpl
inc rbx
adox rdx, [ rsp + 0x90 ]
mulx r9, rbx, r11
adox r12, [ rsp + 0xc0 ]
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x260 ], r9
mov [ rsp + 0x268 ], rbx
mulx rbx, r9, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x270 ], rbx
mov [ rsp + 0x278 ], r9
mulx r9, rbx, r11
movzx r11, bpl
lea r11, [ r11 + rcx ]
adox r10, [ rsp + 0xb8 ]
adox r13, [ rsp + 0xd8 ]
adcx r11, r15
adox rdi, [ rsp + 0xe8 ]
movzx r15, r8b
mov rcx, 0x0 
adcx r15, rcx
adox r14, [ rsp + 0x238 ]
mov r8, rbx
clc
adcx r8, r9
mov rbp, rbx
adcx rbp, r9
mov [ rsp + 0x280 ], r15
setc r15b
clc
adcx rbx, rdx
adcx r8, r12
seto bl
dec rcx
movzx r15, r15b
adox r15, rcx
adox r9, [ rsp + 0x278 ]
mov r12, 0x7bc65c783158aea3 
mulx rcx, r15, r12
adox r15, [ rsp + 0x270 ]
adcx rbp, r10
adcx r9, r13
adcx r15, rdi
adox rcx, [ rsp + 0x268 ]
mov r10, 0x2341f27177344 
mulx rdi, r13, r10
adox r13, [ rsp + 0x260 ]
movzx rdx, byte [ rsp + 0x200 ]
mov r12, [ rsp + 0x1f8 ]
lea rdx, [ rdx + r12 ]
seto r12b
mov r10, -0x2 
inc r10
adox r8, [ rsp + 0x198 ]
adox rbp, [ rsp + 0x1a0 ]
mov r10, 0x7bc65c783158aea3 
xchg rdx, r8
mov [ rsp + 0x288 ], rbp
mov [ rsp + 0x290 ], r8
mulx r8, rbp, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x298 ], r8
mov [ rsp + 0x2a0 ], rbp
mulx rbp, r8, r10
adox r9, [ rsp + 0x1e0 ]
adox r15, [ rsp + 0x1d8 ]
adcx rcx, r14
mov r14, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x2a8 ], r15
mulx r15, r10, [ rax + 0x20 ]
adox rcx, [ rsp + 0x1d0 ]
seto dl
mov [ rsp + 0x2b0 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx rbx, bl
adox rbx, r15
adox r11, [ rsp + 0x228 ]
adcx r13, r11
movzx rbx, r12b
lea rbx, [ rbx + rdi ]
mov rdi, [ rsp + 0x280 ]
adox rdi, [ rsp + 0x230 ]
adcx rbx, rdi
seto r12b
adc r12b, 0x0
movzx r12, r12b
add dl, 0xFF
adcx r13, [ rsp + 0x1f0 ]
adcx rbx, [ rsp + 0x1e8 ]
movzx r12, r12b
movzx rdx, r12b
adcx rdx, [ rsp + 0x290 ]
mov r11, r8
adox r11, rbp
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx r15, r12, r14
mov rdx, r8
adox rdx, rbp
adox r12, rbp
setc bpl
clc
adcx r8, r14
adcx r11, [ rsp + 0x288 ]
adcx rdx, r9
adcx r12, [ rsp + 0x2a8 ]
adox r15, [ rsp + 0x2a0 ]
mov r8, 0x6cfc5fd681c52056 
xchg rdx, r8
mov [ rsp + 0x2b8 ], r10
mulx r10, r9, r14
adox r9, [ rsp + 0x298 ]
adcx r15, rcx
adcx r9, r13
mov rcx, 0x2341f27177344 
mov rdx, r14
mulx r13, r14, rcx
adox r14, r10
seto dl
mov r10, -0x2 
inc r10
adox r11, [ rsp + 0x88 ]
movzx r10, dl
lea r10, [ r10 + r13 ]
mov r13, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx rcx, r11, r13
adox r8, [ rsp + 0x78 ]
adox r12, [ rsp + 0x80 ]
adcx r14, rbx
adcx r10, rdi
movzx rbx, bpl
mov rdi, 0x0 
adcx rbx, rdi
adox r15, [ rsp + 0x130 ]
adox r9, [ rsp + 0x160 ]
adox r14, [ rsp + 0x188 ]
movzx rbp, byte [ rsp + 0x190 ]
mov rdi, [ rsp - 0x40 ]
lea rbp, [ rbp + rdi ]
mov rdi, [ rsp + 0x2b8 ]
movzx r13, byte [ rsp + 0x158 ]
clc
mov [ rsp + 0x2c0 ], r14
mov r14, -0x1 
adcx r13, r14
adcx rdi, [ rsp + 0x128 ]
mov r13, [ rsp + 0x2b0 ]
adcx r13, [ rsp - 0x20 ]
mov r14, 0xffffffffffffffff 
mov [ rsp + 0x2c8 ], r13
mov [ rsp + 0x2d0 ], rdi
mulx rdi, r13, r14
mov r14, r13
mov [ rsp + 0x2d8 ], r9
setc r9b
clc
adcx r14, rdx
adox r10, [ rsp + 0x180 ]
adox rbp, rbx
mov r14, r13
seto bl
mov byte [ rsp + 0x2e0 ], r9b
mov r9, -0x2 
inc r9
adox r14, rdi
adox r13, rdi
adcx r14, r8
adox r11, rdi
adcx r13, r12
adcx r11, r15
mov r8, 0x2341f27177344 
mulx r15, r12, r8
mov rdi, 0x7bc65c783158aea3 
mulx r8, r9, rdi
adox r9, rcx
mov rcx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x2e8 ], bl
mulx rbx, rdi, rcx
adox rdi, r8
adox r12, rbx
mov rdx, 0x0 
adox r15, rdx
mov r8, -0x3 
inc r8
adox r14, [ rsp - 0x48 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r14
mulx r8, r14, rbx
adox r13, [ rsp + 0x110 ]
mov rcx, 0x7bc65c783158aea3 
mov [ rsp + 0x2f0 ], r13
mulx r13, rbx, rcx
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0x2f8 ], r13
mov [ rsp + 0x300 ], rbx
mulx rbx, r13, rcx
adcx r9, [ rsp + 0x2d8 ]
adcx rdi, [ rsp + 0x2c0 ]
adcx r12, r10
adox r11, [ rsp + 0x120 ]
adox r9, [ rsp + 0x118 ]
adcx r15, rbp
adox rdi, [ rsp + 0x2d0 ]
mov r10, [ rsp - 0x28 ]
setc bpl
movzx rcx, byte [ rsp + 0x2e0 ]
clc
mov [ rsp + 0x308 ], rdi
mov rdi, -0x1 
adcx rcx, rdi
adcx r10, [ rsp + 0xb0 ]
mov rcx, [ rsp + 0xa8 ]
mov rdi, 0x0 
adcx rcx, rdi
mov [ rsp + 0x310 ], r9
mov r9, r14
clc
adcx r9, r8
mov rdi, r14
adcx rdi, r8
adox r12, [ rsp + 0x2c8 ]
mov [ rsp + 0x318 ], r12
movzx r12, bpl
mov [ rsp + 0x320 ], rbx
movzx rbx, byte [ rsp + 0x2e8 ]
lea r12, [ r12 + rbx ]
adox r10, r15
setc bl
clc
adcx r14, rdx
mov r14, 0xfdc1767ae2ffffff 
mulx r15, rbp, r14
adox rcx, r12
setc r12b
clc
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx r8, rbp
adcx r15, [ rsp + 0x300 ]
mov rbx, 0x2341f27177344 
mulx r14, rbp, rbx
adcx r13, [ rsp + 0x2f8 ]
seto dl
mov rbx, 0x0 
dec rbx
movzx r12, r12b
adox r12, rbx
adox r9, [ rsp + 0x2f0 ]
adox rdi, r11
adcx rbp, [ rsp + 0x320 ]
adox r8, [ rsp + 0x310 ]
mov r11, 0x0 
adcx r14, r11
adox r15, [ rsp + 0x308 ]
adox r13, [ rsp + 0x318 ]
adox rbp, r10
seto r10b
mov r12, r9
mov rbx, 0xffffffffffffffff 
sub r12, rbx
mov r11, rdi
sbb r11, rbx
mov [ rsp + 0x328 ], r12
mov r12, r8
sbb r12, rbx
mov rbx, r15
mov [ rsp + 0x330 ], r12
mov r12, 0xfdc1767ae2ffffff 
sbb rbx, r12
mov r12, r13
mov [ rsp + 0x338 ], r11
mov r11, 0x7bc65c783158aea3 
sbb r12, r11
mov r11, rbp
mov [ rsp + 0x340 ], r12
mov r12, 0x6cfc5fd681c52056 
sbb r11, r12
mov r12, 0x0 
dec r12
movzx r10, r10b
adox r10, r12
adox rcx, r14
seto r14b
mov r10, rcx
mov r12, 0x2341f27177344 
sbb r10, r12
movzx r12, r14b
movzx rdx, dl
lea r12, [ r12 + rdx ]
sbb r12, 0x00000000
cmovc rbx, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], rbx
mov rdx, [ rsp + 0x340 ]
cmovc rdx, r13
mov r15, [ rsp + 0x338 ]
cmovc r15, rdi
mov rdi, [ rsp + 0x330 ]
cmovc rdi, r8
mov r8, [ rsp + 0x328 ]
cmovc r8, r9
cmovc r10, rcx
mov [ r12 + 0x30 ], r10
mov [ r12 + 0x20 ], rdx
cmovc r11, rbp
mov [ r12 + 0x28 ], r11
mov [ r12 + 0x8 ], r15
mov [ r12 + 0x0 ], r8
mov [ r12 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 968
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7611
; seed 3555594675871628 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7974011 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=28, initial num_batches=31): 149916 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018800576021277122
; number reverted permutation / tried permutation: 60569 / 89601 =67.599%
; number reverted decision / tried decision: 57354 / 90398 =63.446%
; validated in 386.666s
