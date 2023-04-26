SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 1248
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r12
mulx r12, r13, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], r9
mulx r9, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], rdi
mulx rdi, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
test al, al
adox r11, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r10
mulx r10, rbx, [ rsi + 0x8 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x28 ], r10
mov [ rsp + 0x30 ], rbx
mulx rbx, r10, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], rbx
mov [ rsp + 0x40 ], r10
mulx r10, rbx, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x48 ], rax
mov [ rsp + 0x50 ], r15
mulx r15, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], rax
mulx rax, r15, [ rsi + 0x28 ]
mov rdx, rbx
adcx rdx, r10
mov [ rsp + 0x68 ], rax
mov rax, rbx
mov [ rsp + 0x70 ], r15
setc r15b
clc
adcx rax, r9
mov rax, 0x2341f27177344 
xchg rdx, r9
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r12
mulx r12, r8, rax
adcx r9, r11
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r12
mulx r12, rax, [ rsi + 0x0 ]
adox rax, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r12
mulx r12, rcx, rdx
mov rdx, r10
mov [ rsp + 0x98 ], r12
seto r12b
mov [ rsp + 0xa0 ], rcx
mov rcx, 0x0 
dec rcx
movzx r15, r15b
adox r15, rcx
adox rdx, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r15, [ rsi + 0x18 ]
adcx rbx, rax
seto dl
mov rax, -0x2 
inc rax
adox rdi, rcx
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rdi
mulx rdi, rax, [ rsi + 0x8 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], rax
mulx rax, rdi, r11
setc dl
clc
mov [ rsp + 0xc0 ], r15
mov r15, -0x1 
movzx rcx, cl
adcx rcx, r15
adcx r10, rdi
mov cl, dl
mov rdx, [ rsi + 0x8 ]
mulx r15, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], rbx
mov [ rsp + 0xd0 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xd8 ], cl
mov byte [ rsp + 0xe0 ], r12b
mulx r12, rcx, [ rsi + 0x30 ]
adox rbx, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe8 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
adox r13, r10
setc dl
clc
adcx rbp, r9
seto r9b
mov r10, -0x2 
inc r10
adox rdi, r12
adox r14, r15
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mulx r10, r12, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xf0 ], r14
mov [ rsp + 0xf8 ], rdi
mulx rdi, r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], rbx
mulx rbx, r13, rdx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x110 ], r14
mov [ rsp + 0x118 ], rdi
mulx rdi, r14, rbp
seto dl
mov [ rsp + 0x120 ], rdi
mov rdi, -0x2 
inc rdi
adox r13, rcx
adox r12, rbx
mov rcx, [ rsp + 0x80 ]
setc bl
clc
movzx r9, r9b
adcx r9, rdi
adcx rcx, [ rsp + 0x78 ]
mov r9, 0x2341f27177344 
xchg rdx, rbp
mov [ rsp + 0x128 ], rcx
mulx rcx, rdi, r9
mov r9, [ rsp + 0x50 ]
mov [ rsp + 0x130 ], rcx
setc cl
clc
mov [ rsp + 0x138 ], rdi
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r9, [ rsp + 0x48 ]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x140 ], r9
mulx r9, rdi, [ rsi + 0x18 ]
setc dl
clc
mov byte [ rsp + 0x148 ], cl
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rax, [ rsp + 0x40 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r15
mov byte [ rsp + 0x150 ], r15b
mulx r15, rcx, r11
adcx rcx, [ rsp + 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], r14
mulx r14, r11, [ rsi + 0x0 ]
adox rdi, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x160 ], rdi
mulx rdi, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x168 ], r9
mov [ rsp + 0x170 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
adcx r8, r15
setc dl
movzx r15, byte [ rsp + 0xe0 ]
clc
mov [ rsp + 0x178 ], r8
mov r8, -0x1 
adcx r15, r8
adcx r11, [ rsp + 0x90 ]
adcx r9, r14
seto r15b
inc r8
adox r10, [ rsp + 0x20 ]
adox rdi, [ rsp + 0x18 ]
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x180 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
adcx r8, rcx
seto dl
movzx rcx, byte [ rsp + 0xd8 ]
mov [ rsp + 0x188 ], r10
mov r10, -0x1 
inc r10
mov r10, -0x1 
adox rcx, r10
adox r11, [ rsp + 0xd0 ]
adox rax, r9
seto cl
inc r10
mov r9, -0x1 
movzx rbx, bl
adox rbx, r9
adox r13, [ rsp + 0xc8 ]
adox r12, r11
setc bl
clc
movzx rcx, cl
adcx rcx, r9
adcx r8, [ rsp + 0x170 ]
mov r11b, dl
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, [ rsi + 0x20 ]
setc dl
clc
movzx r15, r15b
adcx r15, r9
adcx rcx, [ rsp + 0x168 ]
adcx r10, [ rsp + 0x30 ]
adox rax, [ rsp + 0x160 ]
mov r15, [ rsp + 0x60 ]
adcx r15, [ rsp + 0x28 ]
mov r9b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], r15
mov [ rsp + 0x198 ], r10
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x1a0 ], r14b
mov byte [ rsp + 0x1a8 ], r11b
mulx r11, r14, rbp
adox rcx, r8
mov r8, [ rsp + 0x118 ]
mov rdx, r8
mov [ rsp + 0x1b0 ], rcx
seto cl
mov [ rsp + 0x1b8 ], r11
mov r11, -0x2 
inc r11
adox rdx, [ rsp + 0x110 ]
mov r11, rbp
mov byte [ rsp + 0x1c0 ], cl
setc cl
clc
adcx r11, [ rsp + 0x110 ]
adcx rdx, r13
mov r11, r8
adox r11, [ rsp + 0x110 ]
adox r14, r8
movzx r8, cl
mov r13, [ rsp + 0x58 ]
lea r8, [ r8 + r13 ]
adcx r11, r12
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, [ rsi + 0x20 ]
adcx r14, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1c8 ], r8
mulx r8, rax, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0x1d0 ], rcx
mov rcx, -0x2 
inc rcx
adox rax, r13
mov r13, 0xffffffffffffffff 
xchg rdx, rax
mov byte [ rsp + 0x1d8 ], al
mulx rax, rcx, r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1e0 ], rax
mov [ rsp + 0x1e8 ], r12
mulx r12, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x1f0 ], r12
mov [ rsp + 0x1f8 ], r14
mulx r14, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x200 ], rax
mov [ rsp + 0x208 ], r14
mulx r14, rax, [ rsi + 0x8 ]
setc dl
clc
mov [ rsp + 0x210 ], r11
mov r11, -0x1 
movzx rbx, bl
adcx rbx, r11
adcx rdi, r15
mov rbx, rcx
setc r15b
clc
adcx rbx, r13
movzx rbx, r15b
lea rbx, [ rbx + r10 ]
setc r10b
clc
movzx r9, r9b
adcx r9, r11
adcx rdi, [ rsp + 0x178 ]
setc r9b
clc
adcx rax, r8
adcx r12, r14
adox rax, [ rsp + 0x210 ]
mov r8, [ rsp + 0x208 ]
adcx r8, [ rsp + 0x200 ]
adox r12, [ rsp + 0x1f8 ]
mov r14, [ rsp + 0x10 ]
setc r15b
movzx r11, byte [ rsp + 0x1a8 ]
clc
mov [ rsp + 0x218 ], r12
mov r12, -0x1 
adcx r11, r12
adcx r14, [ rsp + 0x1e8 ]
mov r11, [ rsp + 0x1d0 ]
adcx r11, [ rsp - 0x8 ]
movzx r12, byte [ rsp + 0x1a0 ]
mov [ rsp + 0x220 ], r11
mov r11, [ rsp + 0x88 ]
lea r12, [ r12 + r11 ]
mov r11, [ rsp - 0x10 ]
adcx r11, [ rsp + 0x70 ]
mov [ rsp + 0x228 ], r11
mov r11, rcx
mov [ rsp + 0x230 ], r14
seto r14b
mov [ rsp + 0x238 ], r8
mov r8, -0x2 
inc r8
adox r11, [ rsp + 0x1e0 ]
adox rcx, [ rsp + 0x1e0 ]
setc r8b
clc
mov [ rsp + 0x240 ], rcx
mov rcx, -0x1 
movzx r9, r9b
adcx r9, rcx
adcx rbx, r12
seto r9b
inc rcx
mov r12, -0x1 
movzx r10, r10b
adox r10, r12
adox rax, r11
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r10
mulx rcx, r11, rbp
seto bpl
inc r12
adox rax, [ rsp + 0xc0 ]
mov r12, 0xffffffffffffffff 
mov rdx, r12
mov byte [ rsp + 0x248 ], bpl
mulx rbp, r12, rax
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x250 ], r12
mov [ rsp + 0x258 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rsp + 0x68 ]
mov byte [ rsp + 0x260 ], r9b
seto r9b
mov [ rsp + 0x268 ], rbp
mov rbp, 0x0 
dec rbp
movzx r8, r8b
adox r8, rbp
adox rdx, [ rsp - 0x18 ]
mov r8, 0x2341f27177344 
xchg rdx, rax
mov [ rsp + 0x270 ], rax
mulx rax, rbp, r8
mov r8, [ rsp + 0x158 ]
mov [ rsp + 0x278 ], rax
seto al
mov [ rsp + 0x280 ], rbp
movzx rbp, byte [ rsp + 0x1d8 ]
mov byte [ rsp + 0x288 ], r9b
mov r9, 0x0 
dec r9
adox rbp, r9
adox r8, [ rsp + 0x1b8 ]
adox r11, [ rsp + 0x120 ]
adox rcx, [ rsp + 0x138 ]
seto bpl
movzx r9, byte [ rsp + 0x1c0 ]
mov byte [ rsp + 0x290 ], al
mov rax, -0x1 
inc rax
mov rax, -0x1 
adox r9, rax
adox rdi, [ rsp + 0x198 ]
adox rbx, [ rsp + 0x190 ]
seto r9b
movzx r9, r9b
adcx r9, [ rsp + 0x1c8 ]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x298 ], r9
mov [ rsp + 0x2a0 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r15, r15b
adox r15, rdx
adox r9, [ rsp + 0x1f0 ]
setc r15b
clc
movzx r10, r10b
adcx r10, rdx
adcx r8, [ rsp + 0x1b0 ]
adcx r11, rdi
mov rdx, [ rsi + 0x28 ]
mulx rdi, r10, [ rsi + 0x10 ]
adox r10, rcx
adox r12, rdi
movzx rdx, bpl
mov rcx, [ rsp + 0x130 ]
lea rdx, [ rdx + rcx ]
seto cl
mov rbp, -0x1 
inc rbp
mov rdi, -0x1 
movzx r14, r14b
adox r14, rdi
adox r8, [ rsp + 0x238 ]
adcx rbx, [ rsp + 0x2a0 ]
adox r9, r11
movzx r14, cl
mov r11, [ rsp + 0x268 ]
lea r14, [ r14 + r11 ]
adcx rdx, [ rsp + 0x298 ]
mov r11, 0xfdc1767ae2ffffff 
xchg rdx, r11
mulx rbp, rcx, r13
adox r10, rbx
adox r12, r11
mov rbx, 0x7bc65c783158aea3 
mov rdx, r13
mulx r11, r13, rbx
mov rdi, 0x6cfc5fd681c52056 
mov [ rsp + 0x2a8 ], r14
mulx r14, rbx, rdi
seto dil
mov byte [ rsp + 0x2b0 ], r15b
movzx r15, byte [ rsp + 0x260 ]
mov [ rsp + 0x2b8 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r15, r12
adox rcx, [ rsp + 0x1e0 ]
adox r13, rbp
adox rbx, r11
mov r15, [ rsp + 0x218 ]
setc bpl
movzx r11, byte [ rsp + 0x248 ]
clc
adcx r11, r12
adcx r15, [ rsp + 0x240 ]
adcx rcx, r8
mov r11, 0x2341f27177344 
mulx r12, r8, r11
adox r8, r14
adcx r13, r9
adcx rbx, r10
mov rdx, 0x0 
adox r12, rdx
movzx r9, byte [ rsp + 0x288 ]
dec rdx
adox r9, rdx
adox r15, [ rsp + 0xa8 ]
adox rcx, [ rsp + 0x108 ]
adcx r8, [ rsp + 0x2b8 ]
adox r13, [ rsp + 0x100 ]
mov r9, [ rsp - 0x28 ]
setc r10b
movzx r14, byte [ rsp + 0x148 ]
clc
adcx r14, rdx
adcx r9, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mulx r11, r14, [ rsi + 0x18 ]
adcx r14, [ rsp + 0x0 ]
mov rdx, [ rsp + 0x258 ]
mov [ rsp + 0x2c0 ], r13
mov r13, rdx
mov [ rsp + 0x2c8 ], r14
setc r14b
clc
adcx r13, [ rsp + 0x250 ]
mov [ rsp + 0x2d0 ], r11
mov r11, rdx
adcx r11, [ rsp + 0x250 ]
adox rbx, [ rsp + 0x128 ]
adox r9, r8
mov r8, rax
mov [ rsp + 0x2d8 ], r9
setc r9b
clc
adcx r8, [ rsp + 0x250 ]
movzx r8, bpl
mov [ rsp + 0x2e0 ], rbx
movzx rbx, byte [ rsp + 0x2b0 ]
lea r8, [ r8 + rbx ]
adcx r13, r15
seto bl
mov rbp, -0x2 
inc rbp
adox r13, [ rsp - 0x30 ]
mov r15, 0xfdc1767ae2ffffff 
xchg rdx, r15
mov byte [ rsp + 0x2e8 ], bl
mulx rbx, rbp, r13
adcx r11, rcx
setc cl
clc
mov rdx, -0x1 
movzx rdi, dil
adcx rdi, rdx
adcx r8, [ rsp + 0x2a8 ]
adox r11, [ rsp + 0x188 ]
mov rdi, 0x6cfc5fd681c52056 
mov rdx, rdi
mov [ rsp + 0x2f0 ], rbx
mulx rbx, rdi, r13
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x2f8 ], rbx
mov [ rsp + 0x300 ], rdi
mulx rdi, rbx, rax
seto dl
mov [ rsp + 0x308 ], rbp
mov rbp, 0x0 
dec rbp
movzx r10, r10b
adox r10, rbp
adox r8, r12
seto r12b
adc r12b, 0x0
movzx r12, r12b
add r9b, 0x7F
adox r15, rbx
mov r10, 0x6cfc5fd681c52056 
xchg rdx, rax
mulx rbx, r9, r10
movzx rbp, r14b
adcx rbp, [ rsp + 0x2d0 ]
movzx r14, byte [ rsp + 0x2e8 ]
clc
mov r10, -0x1 
adcx r14, r10
adcx r8, [ rsp + 0x2c8 ]
mov r14, 0x7bc65c783158aea3 
mov [ rsp + 0x310 ], r11
mulx r11, r10, r14
movzx rdx, r12b
adcx rdx, rbp
adox r10, rdi
setc dil
clc
mov r12, -0x1 
movzx rcx, cl
adcx rcx, r12
adcx r15, [ rsp + 0x2c0 ]
setc cl
clc
movzx rax, al
adcx rax, r12
adcx r15, [ rsp + 0x180 ]
adox r9, r11
adox rbx, [ rsp + 0x280 ]
seto al
inc r12
mov rbp, -0x1 
movzx rcx, cl
adox rcx, rbp
adox r10, [ rsp + 0x2e0 ]
movzx r11, al
mov rcx, [ rsp + 0x278 ]
lea r11, [ r11 + rcx ]
adox r9, [ rsp + 0x2d8 ]
adox rbx, r8
adcx r10, [ rsp + 0x230 ]
mov rcx, rdx
mov rdx, [ rsi + 0x30 ]
mulx rax, r8, [ rsi + 0x20 ]
adcx r9, [ rsp + 0x220 ]
adox r11, rcx
adcx rbx, [ rsp + 0x228 ]
mov rdx, 0xffffffffffffffff 
mulx r12, rcx, r13
mov rbp, rcx
setc r14b
clc
adcx rbp, r12
movzx rdx, dil
mov [ rsp + 0x318 ], rax
mov rax, 0x0 
adox rdx, rax
mov rdi, rcx
mov [ rsp + 0x320 ], rdx
mov rdx, -0x3 
inc rdx
adox rdi, r13
adox rbp, [ rsp + 0x310 ]
adcx rcx, r12
adox rcx, r15
mov rdi, 0x7bc65c783158aea3 
mov rdx, rdi
mulx r15, rdi, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x328 ], rbx
mulx rbx, rax, [ rsi + 0x0 ]
adcx r12, [ rsp + 0x308 ]
adcx rdi, [ rsp + 0x2f0 ]
seto dl
mov [ rsp + 0x330 ], r11
mov r11, -0x2 
inc r11
adox rax, rbp
adcx r15, [ rsp + 0x300 ]
mov rbp, 0x2341f27177344 
xchg rdx, rax
mov [ rsp + 0x338 ], r15
mulx r15, r11, rbp
seto bpl
mov [ rsp + 0x340 ], r15
mov r15, 0x0 
dec r15
movzx rax, al
adox rax, r15
adox r10, r12
setc al
clc
adcx rbx, [ rsp + 0xb8 ]
adox rdi, r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mulx r15, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x348 ], r11
mov [ rsp + 0x350 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
adcx r11, [ rsp + 0xb0 ]
seto dl
mov byte [ rsp + 0x358 ], r14b
movzx r14, byte [ rsp + 0x150 ]
mov byte [ rsp + 0x360 ], al
mov rax, -0x1 
inc rax
mov rax, -0x1 
adox r14, rax
adox r8, [ rsp - 0x20 ]
adcx r12, rdi
adcx r15, [ rsp - 0x38 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mulx rax, rdi, r9
mov rdx, rdi
mov [ rsp + 0x368 ], r8
seto r8b
mov [ rsp + 0x370 ], r15
mov r15, -0x2 
inc r15
adox rdx, rax
mov r15, rdi
adox r15, rax
mov byte [ rsp + 0x378 ], r8b
seto r8b
mov byte [ rsp + 0x380 ], r14b
mov r14, -0x2 
inc r14
adox rdi, r9
mov rdi, [ rsp + 0xa0 ]
adcx rdi, [ rsp - 0x48 ]
mov r14, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x388 ], rdi
mov byte [ rsp + 0x390 ], r8b
mulx r8, rdi, [ rsi + 0x30 ]
adcx rdi, [ rsp + 0x98 ]
seto dl
mov [ rsp + 0x398 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx rbp, bpl
adox rbp, rdi
adox rcx, rbx
adox r11, r10
seto bpl
inc rdi
mov r10, -0x1 
movzx rdx, dl
adox rdx, r10
adox rcx, r14
adox r15, r11
seto bl
mov r14, -0x3 
inc r14
adox rcx, [ rsp + 0xe8 ]
mov rdx, 0x2341f27177344 
mulx rdi, r11, r13
mov r13, 0xffffffffffffffff 
mov rdx, rcx
mulx r14, rcx, r13
mov r10, rcx
seto r13b
mov [ rsp + 0x3a0 ], r15
mov r15, -0x2 
inc r15
adox r10, r14
mov r15, 0x0 
adcx r8, r15
mov r15, 0xfdc1767ae2ffffff 
mov [ rsp + 0x3a8 ], r10
mov [ rsp + 0x3b0 ], r8
mulx r8, r10, r15
xchg rdx, r9
mov [ rsp + 0x3b8 ], r8
mov [ rsp + 0x3c0 ], r10
mulx r10, r8, r15
movzx r15, byte [ rsp + 0x360 ]
clc
mov byte [ rsp + 0x3c8 ], r13b
mov r13, -0x1 
adcx r15, r13
adcx r11, [ rsp + 0x2f8 ]
mov r15, 0x6cfc5fd681c52056 
xchg rdx, r15
mov byte [ rsp + 0x3d0 ], bl
mulx rbx, r13, r9
mov rdx, [ rsp + 0x330 ]
mov [ rsp + 0x3d8 ], rbx
setc bl
mov [ rsp + 0x3e0 ], r13
movzx r13, byte [ rsp + 0x358 ]
clc
mov [ rsp + 0x3e8 ], r10
mov r10, -0x1 
adcx r13, r10
adcx rdx, [ rsp + 0x270 ]
movzx r13, bl
lea r13, [ r13 + rdi ]
mov rdi, rcx
adox rdi, r14
seto bl
inc r10
mov r10, -0x1 
movzx rbp, bpl
adox rbp, r10
adox r12, [ rsp + 0x350 ]
mov rbp, [ rsp + 0x338 ]
setc r10b
mov [ rsp + 0x3f0 ], rdi
movzx rdi, byte [ rsp + 0x380 ]
clc
mov byte [ rsp + 0x3f8 ], bl
mov rbx, -0x1 
adcx rdi, rbx
adcx rbp, [ rsp + 0x328 ]
seto dil
movzx rbx, byte [ rsp + 0x390 ]
mov [ rsp + 0x400 ], r13
mov r13, 0x0 
dec r13
adox rbx, r13
adox rax, r8
adcx r11, rdx
mov rbx, 0x7bc65c783158aea3 
mov rdx, rbx
mulx r8, rbx, r15
adox rbx, [ rsp + 0x3e8 ]
seto r13b
movzx rdx, byte [ rsp + 0x3d0 ]
mov [ rsp + 0x408 ], rbx
mov rbx, 0x0 
dec rbx
adox rdx, rbx
adox r12, rax
mov rdx, 0x6cfc5fd681c52056 
mulx rbx, rax, r15
mov r15, [ rsp + 0xf8 ]
seto dl
mov byte [ rsp + 0x410 ], r10b
movzx r10, byte [ rsp + 0x3c8 ]
mov [ rsp + 0x418 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
adox r10, r12
adox r15, [ rsp + 0x3a0 ]
setc r10b
clc
movzx r13, r13b
adcx r13, r12
adcx r8, rax
seto r13b
inc r12
mov rax, -0x1 
movzx rdi, dil
adox rdi, rax
adox rbp, [ rsp + 0x370 ]
adcx rbx, [ rsp + 0x348 ]
adox r11, [ rsp + 0x388 ]
movzx rdi, byte [ rsp + 0x290 ]
mov r12, [ rsp - 0x40 ]
lea rdi, [ rdi + r12 ]
mov r12, [ rsp + 0xf0 ]
seto al
mov [ rsp + 0x420 ], r15
mov r15, -0x1 
inc r15
mov r15, -0x1 
movzx r13, r13b
adox r13, r15
adox r12, [ rsp + 0x418 ]
seto r13b
movzx r15, byte [ rsp + 0x410 ]
mov [ rsp + 0x428 ], r12
mov r12, 0x0 
dec r12
adox r15, r12
adox rdi, [ rsp + 0x320 ]
setc r15b
clc
movzx r10, r10b
adcx r10, r12
adcx rdi, [ rsp + 0x400 ]
setc r10b
clc
movzx rax, al
adcx rax, r12
adcx rdi, [ rsp + 0x398 ]
mov al, dl
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x430 ], r13b
mulx r13, r12, [ rsi + 0x28 ]
movzx rdx, r10b
mov [ rsp + 0x438 ], r13
mov r13, 0x0 
adox rdx, r13
adcx rdx, [ rsp + 0x3b0 ]
dec r13
movzx rax, al
adox rax, r13
adox rbp, [ rsp + 0x408 ]
adox r8, r11
movzx rax, r15b
mov r11, [ rsp + 0x340 ]
lea rax, [ rax + r11 ]
adox rbx, rdi
adox rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx r15, r11, rdx
seto dl
adc dl, 0x0
movzx rdx, dl
add byte [ rsp + 0x378 ], 0xFF
adcx r12, [ rsp + 0x318 ]
adcx r11, [ rsp + 0x438 ]
movzx r10, byte [ rsp + 0x430 ]
adox r10, r13
adox rbp, [ rsp + 0x140 ]
mov r10, 0x0 
adcx r15, r10
mov rdi, 0x7bc65c783158aea3 
xchg rdx, r9
mulx r13, r10, rdi
clc
adcx rcx, rdx
adox r8, [ rsp + 0x368 ]
adox r12, rbx
seto cl
movzx rbx, byte [ rsp + 0x3f8 ]
mov rdi, 0x0 
dec rdi
adox rbx, rdi
adox r14, [ rsp + 0x3c0 ]
mov rbx, 0x2341f27177344 
mov [ rsp + 0x440 ], r15
mulx r15, rdi, rbx
mov rdx, [ rsp + 0x420 ]
adcx rdx, [ rsp + 0x3a8 ]
mov rbx, [ rsp + 0x428 ]
adcx rbx, [ rsp + 0x3f0 ]
adcx r14, rbp
adox r10, [ rsp + 0x3b8 ]
adox r13, [ rsp + 0x3e0 ]
adox rdi, [ rsp + 0x3d8 ]
adcx r10, r8
adcx r13, r12
seto bpl
mov r8, 0x0 
dec r8
movzx rcx, cl
adox rcx, r8
adox rax, r11
adcx rdi, rax
setc r11b
seto cl
mov r12, rdx
mov rax, 0xffffffffffffffff 
sub r12, rax
mov r8, rbx
sbb r8, rax
mov [ rsp + 0x448 ], r12
mov r12, r14
sbb r12, rax
movzx rax, bpl
lea rax, [ rax + r15 ]
movzx r15, r9b
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx rcx, cl
adox rcx, rbp
adox r15, [ rsp + 0x440 ]
seto r9b
inc rbp
mov rcx, -0x1 
movzx r11, r11b
adox r11, rcx
adox r15, rax
seto r11b
mov rax, r10
mov rbp, 0xfdc1767ae2ffffff 
sbb rax, rbp
mov rcx, r13
mov rbp, 0x7bc65c783158aea3 
sbb rcx, rbp
mov rbp, rdi
mov [ rsp + 0x450 ], rcx
mov rcx, 0x6cfc5fd681c52056 
sbb rbp, rcx
mov rcx, r15
mov [ rsp + 0x458 ], rax
mov rax, 0x2341f27177344 
sbb rcx, rax
movzx rax, r11b
movzx r9, r9b
lea rax, [ rax + r9 ]
sbb rax, 0x00000000
cmovc r8, rbx
cmovc r12, r14
mov rax, [ rsp + 0x448 ]
cmovc rax, rdx
cmovc rbp, rdi
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x28 ], rbp
cmovc rcx, r15
mov [ rdx + 0x8 ], r8
mov rbx, [ rsp + 0x458 ]
cmovc rbx, r10
mov r14, [ rsp + 0x450 ]
cmovc r14, r13
mov [ rdx + 0x18 ], rbx
mov [ rdx + 0x10 ], r12
mov [ rdx + 0x0 ], rax
mov [ rdx + 0x30 ], rcx
mov [ rdx + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 1248
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.4136
; seed 3284406264469582 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 16573009 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=22, initial num_batches=31): 296823 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.017910024667216435
; number reverted permutation / tried permutation: 66243 / 89907 =73.679%
; number reverted decision / tried decision: 52380 / 90092 =58.141%
; validated in 392.59s
