SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 792
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov [ rsp - 0x68 ], r13
mov r13, rbp
test al, al
adox r13, r12
mov [ rsp - 0x60 ], r14
mov r14, rbp
adox r14, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r14
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r13
mulx r13, r15, [ rax + 0x8 ]
adox rdi, r12
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x8 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
adcx r15, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], rdi
mulx rdi, r11, [ rax + 0x10 ]
adcx r11, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r12
mulx r12, r13, [ rsi + 0x0 ]
adcx r13, rdi
adcx r8, r12
mov rdx, [ rsi + 0x20 ]
mulx r12, rdi, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x10 ], r8
mov r8, -0x2 
inc r8
adox rdi, r14
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rdi
mulx rdi, r8, [ rax + 0x28 ]
adcx r8, rcx
adcx r9, rdi
mov rdx, [ rax + 0x10 ]
mulx rdi, rcx, [ rsi + 0x20 ]
adox rcx, r12
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx rbp, r10
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, [ rax + 0x0 ]
adcx r15, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], rbp
mulx rbp, rcx, [ rsi + 0x10 ]
adcx r13, [ rsp - 0x8 ]
setc dl
clc
adcx rcx, r12
adcx rbp, [ rsp - 0x30 ]
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x30 ], rbp
mov [ rsp + 0x38 ], rcx
mulx rcx, rbp, [ rax + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x40 ], rdi
mov [ rsp + 0x48 ], r13
mulx r13, rdi, r10
seto dl
mov [ rsp + 0x50 ], r11
mov r11, 0x0 
dec r11
movzx r14, r14b
adox r14, r11
adox rdi, [ rsp - 0x28 ]
mov r14b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x58 ], r15
mulx r15, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov byte [ rsp + 0x60 ], r14b
mov [ rsp + 0x68 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
adcx rbp, [ rsp - 0x38 ]
adcx r11, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r11
mulx r11, rcx, [ rax + 0x28 ]
adcx rcx, r15
adcx r14, r11
mov rdx, 0x6cfc5fd681c52056 
mulx r11, r15, r10
mov rdx, 0x2341f27177344 
mov [ rsp + 0x78 ], r14
mov [ rsp + 0x80 ], rcx
mulx rcx, r14, r10
adox r15, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, [ rax + 0x10 ]
mov rdx, 0x0 
adcx rbx, rdx
adox r14, r11
adox rcx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x88 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
add r12b, 0xFF
adcx rdi, [ rsp + 0x10 ]
adcx r15, r8
adcx r14, r9
mov rdx, [ rax + 0x8 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x90 ], rbp
mulx rbp, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r12
mov [ rsp + 0xa0 ], r14
mulx r14, r12, [ rax + 0x8 ]
adox r12, rbx
adox r10, r14
mov rdx, [ rax + 0x10 ]
mulx r14, rbx, [ rsi + 0x28 ]
seto dl
mov [ rsp + 0xa8 ], r15
mov r15, -0x2 
inc r15
adox r8, rbp
adox rbx, r9
adox r14, [ rsp - 0x40 ]
adcx rcx, [ rsp + 0x68 ]
mov r9b, dl
mov rdx, [ rsi + 0x20 ]
mulx r15, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb0 ], r14
mov [ rsp + 0xb8 ], rbx
mulx rbx, r14, [ rsi + 0x20 ]
setc dl
clc
adcx r11, [ rsp + 0x58 ]
adcx r12, [ rsp + 0x50 ]
adcx r10, [ rsp + 0x48 ]
mov [ rsp + 0xc0 ], r8
setc r8b
mov byte [ rsp + 0xc8 ], dl
movzx rdx, byte [ rsp + 0x60 ]
clc
mov [ rsp + 0xd0 ], rcx
mov rcx, -0x1 
adcx rdx, rcx
adcx r14, [ rsp + 0x40 ]
adcx rbp, rbx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], rbp
mov [ rsp + 0xe0 ], r14
mulx r14, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xe8 ], rdi
mov byte [ rsp + 0xf0 ], r8b
mulx r8, rdi, [ rsi + 0x28 ]
adcx rbx, r15
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf8 ], rbx
mulx rbx, r15, [ rsi + 0x28 ]
adox r15, [ rsp - 0x48 ]
adox rbp, rbx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], rbp
mulx rbp, rbx, [ rax + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x108 ], r15
mov [ rsp + 0x110 ], r13
mulx r13, r15, [ rsi + 0x18 ]
adox rdi, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x120 ], r14
mov [ rsp + 0x128 ], r13
mulx r13, r14, [ rsi + 0x18 ]
adcx rbx, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x130 ], rbx
mulx rbx, rcx, r11
seto dl
mov byte [ rsp + 0x138 ], r9b
mov r9, -0x2 
inc r9
adox r14, rdi
mov rdi, 0x0 
adcx rbp, rdi
mov r9, rcx
clc
adcx r9, r11
adox r15, r13
movzx r9, dl
lea r9, [ r9 + r8 ]
mov r8, rcx
seto dl
mov r13, -0x3 
inc r13
adox r8, rbx
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mov [ rsp + 0x140 ], r9
mulx r9, r13, r11
adcx r8, r12
adox rcx, rbx
adcx rcx, r10
adox r13, rbx
mov rdx, [ rax + 0x8 ]
mulx r10, r12, [ rsi + 0x30 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x148 ], rbp
mulx rbp, rbx, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x150 ], r15
mov [ rsp + 0x158 ], r14
mulx r14, r15, [ rsi + 0x30 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x160 ], rcx
mov [ rsp + 0x168 ], r8
mulx r8, rcx, r11
adox rbx, r9
mov rdx, [ rsi + 0x30 ]
mov byte [ rsp + 0x170 ], dil
mulx rdi, r9, [ rax + 0x0 ]
adox rcx, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x178 ], r9
mulx r9, rbp, [ rsi + 0x30 ]
setc dl
clc
adcx r12, rdi
mov rdi, 0x2341f27177344 
xchg rdx, r11
mov [ rsp + 0x180 ], r12
mov [ rsp + 0x188 ], rcx
mulx rcx, r12, rdi
adox r12, r8
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rax + 0x20 ]
mulx rdi, r8, [ rsi + 0x30 ]
adcx r15, r10
adcx rbp, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x190 ], rbp
mov [ rsp + 0x198 ], r15
mulx r15, rbp, [ rax + 0x28 ]
movzx rdx, byte [ rsp + 0x138 ]
mov [ rsp + 0x1a0 ], rcx
mov rcx, 0x0 
dec rcx
adox rdx, rcx
adox r10, [ rsp + 0x110 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x1a8 ], r12
mulx r12, rcx, [ rax + 0x20 ]
adcx r8, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1b0 ], r8
mulx r8, r9, [ rsi + 0x8 ]
adox rcx, r14
adcx rbp, rdi
adox r9, r12
adox r8, [ rsp + 0x8 ]
mov rdx, [ rsp + 0x0 ]
mov rdi, 0x0 
adox rdx, rdi
mov r14, rdx
mov rdx, [ rax + 0x30 ]
mulx rdi, r12, [ rsi + 0x30 ]
movzx rdx, byte [ rsp + 0xf0 ]
mov [ rsp + 0x1b8 ], rbp
mov rbp, 0x0 
dec rbp
adox rdx, rbp
adox r10, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0xa8 ]
adox r9, [ rsp + 0xa0 ]
seto dl
inc rbp
mov rbp, -0x1 
movzx r11, r11b
adox r11, rbp
adox r10, r13
adox rbx, rcx
mov r11b, dl
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, [ rax + 0x18 ]
adcx r12, r15
mov rdx, 0x0 
adcx rdi, rdx
movzx r15, byte [ rsp + 0x170 ]
clc
adcx r15, rbp
adcx r13, [ rsp + 0x128 ]
mov rdx, [ rax + 0x20 ]
mulx rbp, r15, [ rsi + 0x18 ]
adcx r15, rcx
mov rdx, [ rsp + 0x168 ]
seto cl
mov [ rsp + 0x1c0 ], rdi
mov rdi, -0x2 
inc rdi
adox rdx, [ rsp + 0x28 ]
mov rdi, [ rsp + 0x160 ]
adox rdi, [ rsp + 0x38 ]
adox r10, [ rsp + 0x30 ]
adox rbx, [ rsp + 0x90 ]
mov [ rsp + 0x1c8 ], r12
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1d0 ], r15
mov [ rsp + 0x1d8 ], r13
mulx r13, r15, [ rsi + 0x18 ]
adcx r15, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1e0 ], r15
mulx r15, rbp, [ rax + 0x30 ]
adcx rbp, r13
setc dl
clc
mov r13, -0x1 
movzx r11, r11b
adcx r11, r13
adcx r8, [ rsp + 0xd0 ]
seto r11b
inc r13
mov r13, -0x1 
movzx rcx, cl
adox rcx, r13
adox r9, [ rsp + 0x188 ]
adox r8, [ rsp + 0x1a8 ]
movzx rcx, byte [ rsp + 0xc8 ]
adcx rcx, r14
movzx r14, dl
lea r14, [ r14 + r15 ]
adox rcx, [ rsp + 0x1a0 ]
seto r15b
adc r15b, 0x0
movzx r15, r15b
add r11b, 0xFF
adcx r9, [ rsp + 0x70 ]
mov r11, 0xffffffffffffffff 
mov rdx, r12
mulx r13, r12, r11
adcx r8, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0x78 ]
mov r11, r12
adox r11, rdx
mov r11, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1e8 ], r14
mov [ rsp + 0x1f0 ], rbp
mulx rbp, r14, r11
movzx r15, r15b
movzx r11, r15b
adcx r11, [ rsp + 0x88 ]
mov r15, r12
mov [ rsp + 0x1f8 ], r11
setc r11b
clc
adcx r15, r13
adox r15, rdi
adcx r12, r13
adox r12, r10
adcx r14, r13
mov rdi, 0x7bc65c783158aea3 
mulx r13, r10, rdi
adcx r10, rbp
adox r14, rbx
mov rbx, 0x6cfc5fd681c52056 
mulx rdi, rbp, rbx
adcx rbp, r13
mov r13, 0x2341f27177344 
mov byte [ rsp + 0x200 ], r11b
mulx r11, rbx, r13
adcx rbx, rdi
setc dl
clc
adcx r15, [ rsp + 0x120 ]
adcx r12, [ rsp + 0x158 ]
movzx rdi, dl
lea rdi, [ rdi + r11 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r13, r11, r15
adox r10, r9
adox rbp, r8
adcx r14, [ rsp + 0x150 ]
adcx r10, [ rsp + 0x1d8 ]
mov r9, r11
setc r8b
clc
adcx r9, r13
adox rbx, rcx
mov rcx, r11
adcx rcx, r13
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x208 ], rbx
mov [ rsp + 0x210 ], rbp
mulx rbp, rbx, r15
adcx rbx, r13
setc r13b
clc
adcx r11, r15
adcx r9, r12
adox rdi, [ rsp + 0x1f8 ]
adcx rcx, r14
seto r11b
mov r12, -0x2 
inc r12
adox r9, [ rsp - 0x18 ]
mulx r12, r14, r9
adox rcx, [ rsp + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x218 ], rdi
mov byte [ rsp + 0x220 ], r11b
mulx r11, rdi, r9
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x228 ], r8b
mov [ rsp + 0x230 ], r11
mulx r11, r8, r9
adcx rbx, r10
adox rbx, [ rsp + 0x20 ]
mov r10, r8
seto dl
mov [ rsp + 0x238 ], rdi
mov rdi, -0x2 
inc rdi
adox r10, r9
mov r10, r8
setc dil
clc
adcx r10, r11
adox r10, rcx
adcx r8, r11
adox r8, rbx
adcx r14, r11
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r15
mulx rbx, r11, rcx
seto cl
mov [ rsp + 0x240 ], r8
mov r8, 0x0 
dec r8
movzx r13, r13b
adox r13, r8
adox rbp, r11
mov r13, 0x2341f27177344 
mulx r8, r11, r13
mov r13, 0x6cfc5fd681c52056 
mov [ rsp + 0x248 ], r10
mov [ rsp + 0x250 ], r14
mulx r14, r10, r13
adox r10, rbx
adox r11, r14
mov rdx, 0x2341f27177344 
mulx r14, rbx, r9
mov rdx, 0x0 
adox r8, rdx
mov rdx, r9
mov byte [ rsp + 0x258 ], cl
mulx rcx, r9, r13
adcx r12, [ rsp + 0x238 ]
adcx r9, [ rsp + 0x230 ]
adcx rbx, rcx
adc r14, 0x0
mov rdx, [ rsp + 0x210 ]
add byte [ rsp + 0x228 ], 0x7F
adox rdx, [ rsp + 0x1d0 ]
mov rcx, [ rsp + 0x208 ]
adox rcx, [ rsp + 0x1e0 ]
mov r13, -0x1 
movzx rdi, dil
adcx rdi, r13
adcx rdx, rbp
movzx rdi, byte [ rsp + 0x220 ]
movzx rbp, byte [ rsp + 0x200 ]
lea rdi, [ rdi + rbp ]
mov rbp, [ rsp + 0x1f0 ]
adox rbp, [ rsp + 0x218 ]
adcx r10, rcx
adcx r11, rbp
adox rdi, [ rsp + 0x1e8 ]
adcx r8, rdi
seto cl
adc cl, 0x0
movzx rcx, cl
add r15b, 0xFF
adcx rdx, [ rsp + 0xe0 ]
adcx r10, [ rsp + 0xd8 ]
movzx r15, byte [ rsp + 0x258 ]
adox r15, r13
adox rdx, [ rsp + 0x250 ]
adcx r11, [ rsp + 0xf8 ]
adcx r8, [ rsp + 0x130 ]
movzx rcx, cl
movzx r15, cl
adcx r15, [ rsp + 0x148 ]
adox r12, r10
adox r9, r11
adox rbx, r8
adox r14, r15
mov rbp, [ rsp + 0x248 ]
setc dil
clc
adcx rbp, [ rsp + 0x98 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rcx
mulx r11, r10, rbp
mov r8, r10
seto r15b
inc r13
adox r8, r11
mov r13, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0x240 ]
mov rdx, r10
adox rdx, r11
adcx rcx, [ rsp + 0xb8 ]
adcx r12, [ rsp + 0xb0 ]
adcx r9, [ rsp + 0x108 ]
adcx rbx, [ rsp + 0x100 ]
mov [ rsp + 0x260 ], rbx
movzx rbx, r15b
movzx rdi, dil
lea rbx, [ rbx + rdi ]
adcx r14, [ rsp + 0x118 ]
adcx rbx, [ rsp + 0x140 ]
setc dil
clc
adcx r10, rbp
adcx r8, r13
adcx rdx, rcx
mov r10, 0xfdc1767ae2ffffff 
xchg rdx, rbp
mulx r13, r15, r10
adox r15, r11
adcx r15, r12
mov r11, 0x7bc65c783158aea3 
mulx r12, rcx, r11
adox rcx, r13
adcx rcx, r9
mov r9, 0x6cfc5fd681c52056 
mulx r10, r13, r9
adox r13, r12
mov r12, 0x2341f27177344 
mulx r11, r9, r12
adcx r13, [ rsp + 0x260 ]
adox r9, r10
adcx r9, r14
seto dl
mov r14, -0x2 
inc r14
adox r8, [ rsp + 0x178 ]
adox rbp, [ rsp + 0x180 ]
mov r10, 0x6cfc5fd681c52056 
xchg rdx, r8
mulx r12, r14, r10
movzx r10, r8b
lea r10, [ r10 + r11 ]
adcx r10, rbx
mov rbx, 0xffffffffffffffff 
mulx r8, r11, rbx
movzx rbx, dil
mov [ rsp + 0x268 ], r12
mov r12, 0x0 
adcx rbx, r12
adox r15, [ rsp + 0x198 ]
adox rcx, [ rsp + 0x190 ]
adox r13, [ rsp + 0x1b0 ]
adox r9, [ rsp + 0x1b8 ]
adox r10, [ rsp + 0x1c8 ]
mov rdi, r11
clc
adcx rdi, r8
adox rbx, [ rsp + 0x1c0 ]
mov r12, r11
adcx r12, r8
mov [ rsp + 0x270 ], rbx
seto bl
mov [ rsp + 0x278 ], r10
mov r10, -0x2 
inc r10
adox r11, rdx
adox rdi, rbp
adox r12, r15
mov r11, 0xfdc1767ae2ffffff 
mulx r15, rbp, r11
adcx rbp, r8
adox rbp, rcx
mov r8, 0x7bc65c783158aea3 
mulx r10, rcx, r8
adcx rcx, r15
adcx r14, r10
mov r15, 0x2341f27177344 
mulx r8, r10, r15
adox rcx, r13
adcx r10, [ rsp + 0x268 ]
adox r14, r9
adox r10, [ rsp + 0x278 ]
mov rdx, 0x0 
adcx r8, rdx
adox r8, [ rsp + 0x270 ]
seto r13b
mov r9, rdi
mov r11, 0xffffffffffffffff 
sub r9, r11
mov rdx, r12
sbb rdx, r11
mov r15, rbp
sbb r15, r11
mov r11, rcx
mov [ rsp + 0x280 ], r15
mov r15, 0xfdc1767ae2ffffff 
sbb r11, r15
mov r15, r14
mov [ rsp + 0x288 ], rdx
mov rdx, 0x7bc65c783158aea3 
sbb r15, rdx
mov rdx, r10
mov [ rsp + 0x290 ], r15
mov r15, 0x6cfc5fd681c52056 
sbb rdx, r15
movzx r15, r13b
movzx rbx, bl
lea r15, [ r15 + rbx ]
mov rbx, r8
mov r13, 0x2341f27177344 
sbb rbx, r13
sbb r15, 0x00000000
cmovc r9, rdi
cmovc rbx, r8
cmovc r11, rcx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], r9
cmovc rdx, r10
mov rdi, [ rsp + 0x288 ]
cmovc rdi, r12
mov [ r15 + 0x8 ], rdi
mov [ r15 + 0x28 ], rdx
mov [ r15 + 0x30 ], rbx
mov r12, [ rsp + 0x280 ]
cmovc r12, rbp
mov rbp, [ rsp + 0x290 ]
cmovc rbp, r14
mov [ r15 + 0x20 ], rbp
mov [ r15 + 0x10 ], r12
mov [ r15 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 792
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7266
; seed 4131619680615264 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13538673 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=26, initial num_batches=31): 250283 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018486523753103425
; number reverted permutation / tried permutation: 71691 / 90267 =79.421%
; number reverted decision / tried decision: 63655 / 89732 =70.939%
; validated in 431.438s
