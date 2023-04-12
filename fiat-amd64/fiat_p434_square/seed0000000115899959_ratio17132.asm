SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 944
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rdi
mulx rdi, r8, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r13
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r12
mulx r12, r9, [ rsi + 0x30 ]
test al, al
adox r11, r15
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x10 ], r12
mulx r12, r15, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r13
mulx r13, r9, [ rsi + 0x10 ]
mov rdx, r8
adcx rdx, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r9
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r13
mulx r13, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x28 ], r13
mov [ rsp + 0x30 ], r9
mulx r9, r13, [ rsi + 0x28 ]
mov rdx, r8
mov [ rsp + 0x38 ], r9
setc r9b
clc
adcx rdx, rdi
mov [ rsp + 0x40 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r12
mov [ rsp + 0x50 ], r15
mulx r15, r12, rdx
adcx r8, rdi
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r12
mulx r12, r15, r14
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rbx
mulx rbx, rbp, r14
adcx r15, rdi
adcx rbp, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], r12
mov [ rsp + 0x80 ], rbx
mulx rbx, r12, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x88 ], r12
mov r12, 0x0 
dec r12
movzx r9, r9b
adox r9, r12
adox r11, r13
setc r9b
clc
adcx rdi, r11
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x90 ], r12
mov [ rsp + 0x98 ], r11
mulx r11, r12, [ rsi + 0x10 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xa0 ], rbx
mov byte [ rsp + 0xa8 ], r9b
mulx r9, rbx, rdi
setc dl
clc
mov [ rsp + 0xb0 ], r9
mov r9, -0x1 
movzx r13, r13b
adcx r13, r9
adcx rcx, r12
mov r13b, dl
mov rdx, [ rsi + 0x0 ]
mulx r9, r12, [ rsi + 0x18 ]
adox r8, rcx
adcx r12, r11
adox r15, r12
mov rdx, 0x6cfc5fd681c52056 
mulx rcx, r11, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r15
mulx r15, r12, [ rsi + 0x0 ]
adcx rax, r9
adcx r10, [ rsp + 0x70 ]
adox rbp, rax
adcx r12, [ rsp + 0x68 ]
mov rdx, 0xffffffffffffffff 
mulx rax, r9, rdi
mov rdx, r9
mov [ rsp + 0xc0 ], rbp
setc bpl
clc
adcx rdx, rax
mov [ rsp + 0xc8 ], rdx
mov rdx, r9
adcx rdx, rax
mov [ rsp + 0xd0 ], rdx
mov rdx, 0x2341f27177344 
mov [ rsp + 0xd8 ], r8
mov byte [ rsp + 0xe0 ], r13b
mulx r13, r8, r14
movzx r14, bpl
lea r14, [ r14 + r15 ]
adcx rbx, rax
mov r15, [ rsp + 0x80 ]
setc bpl
movzx rax, byte [ rsp + 0xa8 ]
clc
mov rdx, -0x1 
adcx rax, rdx
adcx r15, [ rsp + 0x50 ]
adox r15, r10
adcx r8, [ rsp + 0x48 ]
mov rax, 0x7bc65c783158aea3 
mov rdx, rax
mulx r10, rax, rdi
adox r8, r12
mov r12, 0x0 
adcx r13, r12
clc
mov r12, -0x1 
movzx rbp, bpl
adcx rbp, r12
adcx rax, [ rsp + 0xb0 ]
adcx r11, r10
adox r13, r14
mov r14, 0x2341f27177344 
mov rdx, rdi
mulx rbp, rdi, r14
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r11
mov [ rsp + 0xf0 ], rax
mulx rax, r11, [ rsi + 0x0 ]
adcx rdi, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xf8 ], r11
mulx r11, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], rdi
mov [ rsp + 0x108 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x110 ], r13
mov r13, -0x2 
inc r13
adox rdi, rax
adox r12, rbx
mov al, dl
mov rdx, [ rsi + 0x30 ]
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], r13
mov [ rsp + 0x120 ], r12
mulx r12, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x128 ], rdi
mov byte [ rsp + 0x130 ], al
mulx rax, rdi, [ rsi + 0x10 ]
adox rcx, r14
adox r13, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, r14, [ rsi + 0x28 ]
setc dl
clc
adcx r14, [ rsp + 0x0 ]
mov [ rsp + 0x138 ], r14
movzx r14, dl
lea r14, [ r14 + rbp ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], r13
mulx r13, rbp, rdx
adox r12, [ rsp - 0x18 ]
adox rbx, [ rsp - 0x28 ]
mov rdx, [ rsp - 0x30 ]
mov [ rsp + 0x148 ], rbx
seto bl
mov [ rsp + 0x150 ], r12
mov r12, -0x2 
inc r12
adox rdx, [ rsp + 0x10 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x158 ], bl
mov [ rsp + 0x160 ], rcx
mulx rcx, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], r14
mov [ rsp + 0x170 ], r12
mulx r12, r14, [ rsi + 0x10 ]
adcx r14, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x178 ], r14
mulx r14, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x180 ], r8
mov [ rsp + 0x188 ], r15
mulx r15, r8, [ rsi + 0x10 ]
adcx rbx, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x190 ], rbx
mulx rbx, r12, [ rsi + 0x20 ]
adox rbp, [ rsp + 0x8 ]
adcx r12, rcx
adox rdi, r13
adox r11, rax
adox r8, r14
mov rdx, [ rsi + 0x10 ]
mulx r13, rax, [ rsi + 0x30 ]
adox rax, r15
mov rdx, [ rsi + 0x8 ]
mulx r14, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x198 ], r12
mulx r12, r15, [ rsi + 0x20 ]
adcx rbx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a0 ], rbx
mov [ rsp + 0x1a8 ], rax
mulx rax, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1b0 ], r8
mov [ rsp + 0x1b8 ], r11
mulx r11, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1c0 ], rdi
mov [ rsp + 0x1c8 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x40 ]
adcx rdx, [ rsp - 0x40 ]
mov [ rsp + 0x1d0 ], rdx
setc dl
clc
adcx rcx, [ rsp + 0x78 ]
mov byte [ rsp + 0x1d8 ], dl
mov rdx, 0x0 
adox r13, rdx
movzx rdx, byte [ rsp + 0xe0 ]
mov [ rsp + 0x1e0 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox rcx, [ rsp + 0xd8 ]
adcx rdi, r14
adcx r8, rbp
adox rdi, [ rsp + 0xb8 ]
adcx r15, r11
mov rdx, [ rsi + 0x20 ]
mulx r11, r14, [ rsi + 0x0 ]
setc dl
clc
adcx rbx, r11
mov bpl, dl
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, [ rsi + 0x20 ]
adcx rax, [ rsp + 0x20 ]
adcx r11, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1e8 ], r11
mov [ rsp + 0x1f0 ], rax
mulx rax, r11, [ rsi + 0x28 ]
adcx r13, [ rsp + 0x60 ]
adox r8, [ rsp + 0xc0 ]
adox r15, [ rsp + 0x188 ]
seto dl
mov [ rsp + 0x1f8 ], r13
mov r13, 0x0 
dec r13
movzx rbp, bpl
adox rbp, r13
adox r12, r11
setc bpl
clc
movzx rdx, dl
adcx rdx, r13
adcx r12, [ rsp + 0x180 ]
mov rdx, [ rsi + 0x30 ]
mulx r13, r11, [ rsi + 0x8 ]
adox r11, rax
seto dl
mov rax, -0x2 
inc rax
adox r9, r10
adox rcx, [ rsp + 0xc8 ]
adox rdi, [ rsp + 0xd0 ]
movzx r9, dl
lea r9, [ r9 + r13 ]
adcx r11, [ rsp + 0x110 ]
movzx r10, byte [ rsp + 0x130 ]
adcx r10, r9
adox r8, [ rsp + 0x108 ]
seto r13b
inc rax
adox rcx, [ rsp - 0x48 ]
adox rdi, [ rsp + 0x170 ]
mov rdx, 0x6cfc5fd681c52056 
mulx rax, r9, rcx
adox r8, [ rsp + 0x1c8 ]
setc dl
clc
mov [ rsp + 0x200 ], rbx
mov rbx, -0x1 
movzx r13, r13b
adcx r13, rbx
adcx r15, [ rsp + 0xf0 ]
adcx r12, [ rsp + 0xe8 ]
adcx r11, [ rsp + 0x100 ]
adcx r10, [ rsp + 0x168 ]
movzx r13, dl
mov rbx, 0x0 
adcx r13, rbx
adox r15, [ rsp + 0x1c0 ]
adox r12, [ rsp + 0x1b8 ]
mov rdx, [ rsp + 0x30 ]
clc
mov rbx, -0x1 
movzx rbp, bpl
adcx rbp, rbx
adcx rdx, [ rsp + 0x58 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mov [ rsp + 0x208 ], rbp
mulx rbp, rbx, rcx
adox r11, [ rsp + 0x1b0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x210 ], r14
mov [ rsp + 0x218 ], r13
mulx r13, r14, [ rsi + 0x20 ]
adox r10, [ rsp + 0x1a8 ]
mov rdx, rbx
mov [ rsp + 0x220 ], r13
seto r13b
mov [ rsp + 0x228 ], r10
mov r10, -0x2 
inc r10
adox rdx, rbp
adcx r14, [ rsp + 0x28 ]
mov r10, rbx
adox r10, rbp
mov [ rsp + 0x230 ], r14
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov byte [ rsp + 0x238 ], r13b
mov [ rsp + 0x240 ], r11
mulx r11, r13, r14
setc r14b
clc
adcx rbx, rdx
adcx rcx, rdi
adox r13, rbp
adcx r10, r8
adcx r13, r15
mov rbx, 0x2341f27177344 
mulx r8, rdi, rbx
mov r15, 0x7bc65c783158aea3 
mulx rbx, rbp, r15
adox rbp, r11
adox r9, rbx
adox rdi, rax
mov rdx, 0x0 
adox r8, rdx
adcx rbp, r12
adcx r9, [ rsp + 0x240 ]
mov rax, [ rsp + 0x218 ]
movzx r12, byte [ rsp + 0x238 ]
dec rdx
adox r12, rdx
adox rax, [ rsp + 0x1e0 ]
adcx rdi, [ rsp + 0x228 ]
adcx r8, rax
seto r12b
adc r12b, 0x0
movzx r12, r12b
adox rcx, [ rsp + 0xf8 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rbx, r11, rcx
adox r10, [ rsp + 0x128 ]
mov rdx, rcx
mulx rax, rcx, r15
adox r13, [ rsp + 0x120 ]
adox rbp, [ rsp + 0x160 ]
adox r9, [ rsp + 0x140 ]
adox rdi, [ rsp + 0x150 ]
movzx r15, byte [ rsp + 0x158 ]
adcx r15, [ rsp + 0x118 ]
mov [ rsp + 0x248 ], rdi
mov rdi, r11
clc
adcx rdi, rbx
mov byte [ rsp + 0x250 ], r14b
mov r14, r11
adcx r14, rbx
adox r8, [ rsp + 0x148 ]
mov [ rsp + 0x258 ], r8
movzx r8, r12b
adox r8, r15
seto r12b
mov r15, -0x2 
inc r15
adox r11, rdx
adox rdi, r10
mov r11, 0xfdc1767ae2ffffff 
mulx r15, r10, r11
adcx r10, rbx
adcx rcx, r15
adox r14, r13
setc bl
clc
adcx rdi, [ rsp + 0x210 ]
mov r13, 0xffffffffffffffff 
xchg rdx, rdi
mulx r11, r15, r13
adcx r14, [ rsp + 0x200 ]
mov r13, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x260 ], r12b
mov [ rsp + 0x268 ], r8
mulx r8, r12, r13
adox r10, rbp
adcx r10, [ rsp + 0x1f0 ]
adox rcx, r9
adcx rcx, [ rsp + 0x1e8 ]
mov rbp, r15
setc r9b
clc
adcx rbp, r11
mov r13, r15
adcx r13, r11
mov byte [ rsp + 0x270 ], r9b
seto r9b
mov [ rsp + 0x278 ], rax
mov rax, -0x2 
inc rax
adox r15, rdx
adox rbp, r14
adox r13, r10
seto r15b
inc rax
adox rbp, [ rsp - 0x20 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rbp
mulx rax, r10, r14
mov r14, 0x7bc65c783158aea3 
mov byte [ rsp + 0x280 ], r9b
mov byte [ rsp + 0x288 ], bl
mulx rbx, r9, r14
xchg rdx, r14
mov [ rsp + 0x290 ], rbx
mov [ rsp + 0x298 ], r9
mulx r9, rbx, rbp
adcx r12, r11
setc r11b
clc
mov rdx, -0x1 
movzx r15, r15b
adcx r15, rdx
adcx rcx, r12
setc r15b
clc
movzx r11, r11b
adcx r11, rdx
adcx r8, rbx
mov rbx, 0x6cfc5fd681c52056 
mov rdx, rbx
mulx r11, rbx, rbp
adox r13, [ rsp + 0x138 ]
mov r12, 0x2341f27177344 
mov rdx, r12
mov [ rsp + 0x2a0 ], r13
mulx r13, r12, rbp
adcx rbx, r9
adcx r12, r11
mov rbp, 0x0 
adcx r13, rbp
mov r9, 0x6cfc5fd681c52056 
mov rdx, r9
mulx r11, r9, rdi
mov rdx, r10
clc
adcx rdx, rax
mov rbp, r10
adcx rbp, rax
mov [ rsp + 0x2a8 ], rbp
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mov [ rsp + 0x2b0 ], r13
mov [ rsp + 0x2b8 ], rbp
mulx rbp, r13, r14
adcx r13, rax
mov rax, 0x2341f27177344 
mov rdx, rdi
mov [ rsp + 0x2c0 ], r13
mulx r13, rdi, rax
mov rdx, r14
mov [ rsp + 0x2c8 ], r12
mulx r12, r14, rax
adcx rbp, [ rsp + 0x298 ]
mov rax, 0x6cfc5fd681c52056 
mov [ rsp + 0x2d0 ], rbp
mov [ rsp + 0x2d8 ], rbx
mulx rbx, rbp, rax
adcx rbp, [ rsp + 0x290 ]
seto al
mov [ rsp + 0x2e0 ], rbp
movzx rbp, byte [ rsp + 0x288 ]
mov [ rsp + 0x2e8 ], rcx
mov rcx, 0x0 
dec rcx
adox rbp, rcx
adox r9, [ rsp + 0x278 ]
adox rdi, r11
adcx r14, rbx
mov rbp, 0x0 
adox r13, rbp
adc r12, 0x0
movzx r11, byte [ rsp + 0x250 ]
add r11, [ rsp + 0x220 ]
add byte [ rsp + 0x280 ], 0x7F
adox r9, [ rsp + 0x248 ]
adox rdi, [ rsp + 0x258 ]
adox r13, [ rsp + 0x268 ]
movzx rbx, byte [ rsp + 0x270 ]
adcx rbx, rcx
adcx r9, [ rsp + 0x1f8 ]
adcx rdi, [ rsp + 0x208 ]
movzx rbx, byte [ rsp + 0x260 ]
adox rbx, rbp
adcx r13, [ rsp + 0x230 ]
dec rbp
movzx r15, r15b
adox r15, rbp
adox r9, r8
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rsp + 0x178 ]
setc bpl
clc
mov [ rsp + 0x2f0 ], r12
mov r12, -0x1 
movzx rax, al
adcx rax, r12
adcx rdx, [ rsp + 0x2e8 ]
seto al
inc r12
mov r12, -0x1 
movzx rbp, bpl
adox rbp, r12
adox rbx, r11
movzx r11, byte [ rsp + 0x1d8 ]
mov rbp, [ rsp + 0x38 ]
lea r11, [ r11 + rbp ]
seto bpl
inc r12
adox r10, rcx
adcx r9, [ rsp + 0x190 ]
setc r10b
clc
adcx r15, [ rsp + 0xa0 ]
adcx r8, [ rsp - 0x8 ]
mov rcx, [ rsp - 0x10 ]
adcx rcx, [ rsp + 0x98 ]
setc r12b
clc
mov [ rsp + 0x2f8 ], rcx
mov rcx, -0x1 
movzx rax, al
adcx rax, rcx
adcx rdi, [ rsp + 0x2d8 ]
adcx r13, [ rsp + 0x2c8 ]
mov rax, [ rsp + 0x2a0 ]
adox rax, [ rsp + 0x2b8 ]
adcx rbx, [ rsp + 0x2b0 ]
adox rdx, [ rsp + 0x2a8 ]
adox r9, [ rsp + 0x2c0 ]
setc cl
clc
mov byte [ rsp + 0x300 ], r12b
mov r12, -0x1 
movzx r10, r10b
adcx r10, r12
adcx rdi, [ rsp + 0x198 ]
adcx r13, [ rsp + 0x1a0 ]
adox rdi, [ rsp + 0x2d0 ]
adcx rbx, [ rsp + 0x1d0 ]
adox r13, [ rsp + 0x2e0 ]
movzx r10, cl
movzx rbp, bpl
lea r10, [ r10 + rbp ]
adcx r11, r10
setc bpl
clc
adcx rax, [ rsp + 0x88 ]
adcx r15, rdx
mov rcx, 0x2341f27177344 
mov rdx, rcx
mulx r10, rcx, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x308 ], r10
mulx r10, r12, [ rsi + 0x30 ]
adox r14, rbx
adcx r8, r9
adox r11, [ rsp + 0x2f0 ]
mov rdx, [ rsi + 0x30 ]
mulx rbx, r9, rdx
movzx rdx, bpl
mov [ rsp + 0x310 ], rcx
mov rcx, 0x0 
adox rdx, rcx
movzx rbp, byte [ rsp + 0x300 ]
dec rcx
adox rbp, rcx
adox r12, [ rsp + 0x90 ]
mov rbp, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x318 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
adox rcx, r10
adcx rdi, [ rsp + 0x2f8 ]
adox r9, r8
adcx r12, r13
mov rdx, 0x0 
adox rbx, rdx
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r10, r13, rax
adcx rcx, r14
mov r14, r13
mov r8, -0x2 
inc r8
adox r14, r10
adcx r9, r11
mov r11, r13
setc r8b
clc
adcx r11, rax
adcx r14, r15
adox r13, r10
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r15, r11, rax
adox r11, r10
adcx r13, [ rsp + 0x318 ]
mov r10, 0x7bc65c783158aea3 
mov rdx, rax
mov [ rsp + 0x320 ], r13
mulx r13, rax, r10
adox rax, r15
mov r15, 0x6cfc5fd681c52056 
mov [ rsp + 0x328 ], r14
mulx r14, r10, r15
adox r10, r13
adox r14, [ rsp + 0x310 ]
adcx r11, rdi
adcx rax, r12
setc dl
clc
mov rdi, -0x1 
movzx r8, r8b
adcx r8, rdi
adcx rbp, rbx
setc r12b
clc
movzx rdx, dl
adcx rdx, rdi
adcx rcx, r10
adcx r14, r9
mov rbx, [ rsp + 0x308 ]
mov r8, 0x0 
adox rbx, r8
adcx rbx, rbp
setc r9b
mov r13, [ rsp + 0x328 ]
mov r10, 0xffffffffffffffff 
sub r13, r10
mov rdx, [ rsp + 0x320 ]
sbb rdx, r10
mov rbp, r11
sbb rbp, r10
mov r8, rax
mov rdi, 0xfdc1767ae2ffffff 
sbb r8, rdi
mov rdi, rcx
mov r10, 0x7bc65c783158aea3 
sbb rdi, r10
mov r10, r14
sbb r10, r15
movzx r15, r9b
movzx r12, r12b
lea r15, [ r15 + r12 ]
mov r12, rbx
mov r9, 0x2341f27177344 
sbb r12, r9
sbb r15, 0x00000000
cmovc r8, rax
cmovc rbp, r11
cmovc r12, rbx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x30 ], r12
mov [ r15 + 0x10 ], rbp
cmovc rdx, [ rsp + 0x320 ]
mov [ r15 + 0x8 ], rdx
cmovc r10, r14
mov [ r15 + 0x28 ], r10
cmovc rdi, rcx
mov [ r15 + 0x20 ], rdi
cmovc r13, [ rsp + 0x328 ]
mov [ r15 + 0x0 ], r13
mov [ r15 + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 944
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7132
; seed 4279962211607476 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7946688 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=30, initial num_batches=31): 147539 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018566099486981243
; number reverted permutation / tried permutation: 61075 / 89795 =68.016%
; number reverted decision / tried decision: 57676 / 90204 =63.940%
; validated in 329.763s
