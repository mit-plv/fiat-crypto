SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 744
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r12
mulx r12, r9, [ rsi + 0x8 ]
add r10, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r12
mulx r12, r14, [ rax + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], r10
mulx r10, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], rbp
mulx rbp, r13, [ rax + 0x30 ]
adcx r12, r11
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], rbp
mulx rbp, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], r12
mulx r12, r13, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r13, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r13
mulx r13, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r13
mulx r13, rbp, [ rax + 0x10 ]
adox rbp, r12
adox rcx, r13
mov rdx, [ rax + 0x10 ]
mulx r13, r12, [ rsi + 0x20 ]
adox r14, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x20 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x38 ], rbp
mov rbp, -0x2 
inc rbp
adox r8, r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x40 ], r8
mulx r8, rbp, [ rax + 0x10 ]
adox rbp, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], rbp
mulx rbp, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x50 ], r14b
mov [ rsp + 0x58 ], r13
mulx r13, r14, [ rax + 0x18 ]
adcx r14, r10
adox rcx, r8
adcx r9, r13
mov rdx, [ rax + 0x18 ]
mulx r8, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x60 ], rcx
mulx rcx, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x68 ], r9
mov [ rsp + 0x70 ], r13
mulx r13, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x78 ], r14
mov [ rsp + 0x80 ], rbp
mulx rbp, r14, [ rsi + 0x30 ]
setc dl
clc
adcx r15, rbx
adcx r14, rdi
adcx r10, rbp
seto bl
mov rdi, -0x2 
inc rdi
adox r9, rcx
mov cl, dl
mov rdx, [ rax + 0x10 ]
mulx rdi, rbp, [ rsi + 0x10 ]
adox rbp, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r10
mulx r10, r13, [ rax + 0x18 ]
adox r13, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x90 ], r14
mulx r14, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r13
mulx r13, r15, [ rsi + 0x10 ]
adox rdi, r10
adox r15, r14
mov rdx, [ rax + 0x28 ]
mulx r14, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r15
mulx r15, r14, [ rsi + 0x30 ]
adcx r14, r8
adcx r10, r15
mov rdx, [ rsi + 0x28 ]
mulx r15, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xb8 ], r10
mov [ rsp + 0xc0 ], r14
mulx r14, r10, [ rsi + 0x28 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xc8 ], rdi
mov [ rsp + 0xd0 ], rbp
mulx rbp, rdi, r11
mov rdx, rdi
mov [ rsp + 0xd8 ], r9
setc r9b
clc
adcx rdx, rbp
mov byte [ rsp + 0xe0 ], r9b
mov r9, rdi
adcx r9, rbp
mov byte [ rsp + 0xe8 ], cl
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], r9
mov byte [ rsp + 0xf8 ], bl
mulx rbx, r9, [ rax + 0x30 ]
adox r9, r13
mov rdx, 0x0 
adox rbx, rdx
mov r13, -0x3 
inc r13
adox r8, [ rsp + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x100 ], r8
mulx r8, r13, r11
adox r10, r15
mov r15, 0xfdc1767ae2ffffff 
mov rdx, r15
mov [ rsp + 0x108 ], r10
mulx r10, r15, r11
adcx r15, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x110 ], rbx
mulx rbx, rbp, [ rsi + 0x20 ]
adcx r13, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], rbp
mulx rbp, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x120 ], r9
mov [ rsp + 0x128 ], r8
mulx r8, r9, [ rsi + 0x18 ]
adox r10, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x130 ], r10
mulx r10, r14, [ rax + 0x8 ]
setc dl
clc
adcx r14, rbx
adcx r12, r10
mov bl, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x138 ], r12
mulx r12, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x140 ], r14
mov [ rsp + 0x148 ], r12
mulx r12, r14, [ rax + 0x20 ]
adox r14, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r14
mulx r14, rbp, [ rax + 0x28 ]
adox rbp, r12
adox r14, [ rsp - 0x18 ]
seto dl
movzx r12, byte [ rsp + 0xf8 ]
mov [ rsp + 0x158 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox r12, r14
adox r9, [ rsp + 0x80 ]
adcx r10, [ rsp + 0x58 ]
setc r12b
clc
adcx rdi, r11
adcx rcx, [ rsp + 0x8 ]
mov rdi, [ rsp + 0xf0 ]
adcx rdi, [ rsp + 0x38 ]
adcx r15, [ rsp + 0x30 ]
mov r14b, dl
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x160 ], rbp
mov [ rsp + 0x168 ], r10
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x170 ], r14b
mov [ rsp + 0x178 ], r9
mulx r9, r14, r11
adcx r13, [ rsp + 0x20 ]
setc dl
clc
adcx rcx, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
adcx r15, [ rsp + 0x0 ]
adox rbp, r8
mov r8, 0x2341f27177344 
xchg rdx, r8
mov [ rsp + 0x180 ], rbp
mov byte [ rsp + 0x188 ], r8b
mulx r8, rbp, r11
adox r10, [ rsp - 0x8 ]
adcx r13, [ rsp + 0x78 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x190 ], r10
mulx r10, r11, rcx
seto dl
mov byte [ rsp + 0x198 ], r12b
mov r12, 0x0 
dec r12
movzx rbx, bl
adox rbx, r12
adox r14, [ rsp + 0x128 ]
adox rbp, r9
mov rbx, 0x0 
adox r8, rbx
mov r9, r11
mov r12, -0x3 
inc r12
adox r9, rcx
mov r9, r11
setc r12b
clc
adcx r9, r10
mov rbx, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov byte [ rsp + 0x1a0 ], bl
mov [ rsp + 0x1a8 ], r8
mulx r8, rbx, rcx
adcx r11, r10
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1b0 ], rbp
mov byte [ rsp + 0x1b8 ], r12b
mulx r12, rbp, rcx
adcx rbx, r10
adox r9, rdi
adox r11, r15
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r15, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, r10, [ rax + 0x20 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1c0 ], rbp
mov [ rsp + 0x1c8 ], r14
mulx r14, rbp, rcx
adcx rbp, r12
adox rbx, r13
mov r13, 0x2341f27177344 
mov rdx, rcx
mulx r12, rcx, r13
adcx rcx, r14
mov rdx, [ rax + 0x28 ]
mulx r13, r14, [ rsi + 0x8 ]
setc dl
mov [ rsp + 0x1d0 ], rcx
movzx rcx, byte [ rsp + 0x198 ]
clc
mov [ rsp + 0x1d8 ], rbp
mov rbp, -0x1 
adcx rcx, rbp
adcx r10, [ rsp + 0x148 ]
movzx rcx, dl
lea rcx, [ rcx + r12 ]
seto r12b
movzx rdx, byte [ rsp + 0xe8 ]
inc rbp
mov rbp, -0x1 
adox rdx, rbp
adox r14, [ rsp - 0x38 ]
adox rdi, r13
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, [ rax + 0x28 ]
mov rdx, -0x2 
inc rdx
adox r9, [ rsp + 0x70 ]
adox r11, [ rsp + 0xd8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1e0 ], r10
mov [ rsp + 0x1e8 ], r11
mulx r11, r10, [ rax + 0x30 ]
adox rbx, [ rsp + 0xd0 ]
adcx r13, r8
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x1f0 ], r13
mulx r13, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1f8 ], rbx
mov [ rsp + 0x200 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
adcx rbx, rbp
seto dl
movzx rbp, byte [ rsp + 0x50 ]
mov [ rsp + 0x208 ], rbx
mov rbx, 0x0 
dec rbx
adox rbp, rbx
adox r8, [ rsp - 0x30 ]
adox r10, r13
mov rbp, 0x0 
adox r11, rbp
adc r9, 0x0
add byte [ rsp + 0x188 ], 0xFF
adcx r8, [ rsp + 0x1c8 ]
movzx r13, byte [ rsp + 0x1b8 ]
adox r13, rbx
adox r8, [ rsp + 0x68 ]
adcx r10, [ rsp + 0x1b0 ]
adox r14, r10
adcx r11, [ rsp + 0x1a8 ]
adox rdi, r11
setc r13b
movzx r13, r13b
adox r13, r15
clc
movzx r12, r12b
adcx r12, rbx
adcx r8, [ rsp + 0x1c0 ]
adcx r14, [ rsp + 0x1d8 ]
adcx rdi, [ rsp + 0x1d0 ]
adcx rcx, r13
seto r12b
adc r12b, 0x0
movzx r12, r12b
add dl, 0xFF
adcx r8, [ rsp + 0xa0 ]
adcx r14, [ rsp + 0xc8 ]
adcx rdi, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0x120 ]
mov r15, 0xffffffffffffffff 
mov rdx, [ rsp + 0x200 ]
mulx r11, r10, r15
mov r13, r10
adox r13, rdx
movzx r12, r12b
movzx r13, r12b
adcx r13, [ rsp + 0x110 ]
mov r12, r10
setc bl
clc
adcx r12, r11
adcx r10, r11
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x210 ], r9
mulx r9, r15, rbp
adcx r15, r11
adox r12, [ rsp + 0x1e8 ]
adox r10, [ rsp + 0x1f8 ]
adox r15, r8
mov r8, 0x7bc65c783158aea3 
mulx rbp, r11, r8
adcx r11, r9
adox r11, r14
mov r14, 0x6cfc5fd681c52056 
mulx r8, r9, r14
adcx r9, rbp
adox r9, rdi
mov rdi, 0x2341f27177344 
mulx r14, rbp, rdi
adcx rbp, r8
setc dl
clc
adcx r12, [ rsp + 0x28 ]
adcx r10, [ rsp + 0x40 ]
adcx r15, [ rsp + 0x48 ]
mov r8, 0xfdc1767ae2ffffff 
xchg rdx, r8
mov [ rsp + 0x218 ], r15
mulx r15, rdi, r12
movzx rdx, r8b
lea rdx, [ rdx + r14 ]
adcx r11, [ rsp + 0x60 ]
adox rbp, rcx
adox rdx, r13
movzx rcx, bl
mov r13, 0x0 
adox rcx, r13
adcx r9, [ rsp + 0x178 ]
movzx rbx, byte [ rsp + 0x1a0 ]
mov r14, [ rsp - 0x10 ]
lea rbx, [ rbx + r14 ]
adcx rbp, [ rsp + 0x180 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r12
mulx r13, r8, r14
mov r14, r8
mov [ rsp + 0x220 ], rbp
mov rbp, -0x2 
inc rbp
adox r14, r13
adcx r12, [ rsp + 0x190 ]
mov rbp, r8
adox rbp, r13
adcx rbx, rcx
adox rdi, r13
setc cl
clc
adcx r8, rdx
adcx r14, r10
adcx rbp, [ rsp + 0x218 ]
adcx rdi, r11
mov r8, 0x7bc65c783158aea3 
mulx r11, r10, r8
adox r10, r15
mov r15, 0x6cfc5fd681c52056 
mulx r8, r13, r15
adox r13, r11
adcx r10, r9
mov r9, 0x2341f27177344 
mulx r15, r11, r9
adcx r13, [ rsp + 0x220 ]
adox r11, r8
adcx r11, r12
mov rdx, 0x0 
adox r15, rdx
adcx r15, rbx
movzx r12, cl
adc r12, 0x0
test al, al
adox r14, [ rsp + 0x118 ]
mov rcx, 0xffffffffffffffff 
mov rdx, r14
mulx rbx, r14, rcx
mov r8, r14
adcx r8, rbx
adox rbp, [ rsp + 0x140 ]
adox rdi, [ rsp + 0x138 ]
mov r9, r14
adcx r9, rbx
adox r10, [ rsp + 0x168 ]
adox r13, [ rsp + 0x1e0 ]
adox r11, [ rsp + 0x1f0 ]
adox r15, [ rsp + 0x208 ]
adox r12, [ rsp + 0x210 ]
seto cl
mov [ rsp + 0x228 ], r12
mov r12, -0x2 
inc r12
adox r14, rdx
adox r8, rbp
adox r9, rdi
mov r14, 0xfdc1767ae2ffffff 
mulx rdi, rbp, r14
mov r12, 0x7bc65c783158aea3 
mov byte [ rsp + 0x230 ], cl
mulx rcx, r14, r12
adcx rbp, rbx
adcx r14, rdi
adox rbp, r10
mov rbx, 0x6cfc5fd681c52056 
mulx rdi, r10, rbx
adox r14, r13
adcx r10, rcx
mov r13, 0x2341f27177344 
mulx rbx, rcx, r13
adcx rcx, rdi
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r8, [ rsp + 0x10 ]
adox r10, r11
adox rcx, r15
adcx r9, [ rsp + 0x100 ]
movzx r11, byte [ rsp + 0x170 ]
mov r15, [ rsp - 0x40 ]
lea r11, [ r11 + r15 ]
adox rbx, [ rsp + 0x228 ]
movzx r15, byte [ rsp + 0x230 ]
adox r15, rdx
adcx rbp, [ rsp + 0x108 ]
mov rdx, r8
mulx rdi, r8, r13
adcx r14, [ rsp + 0x130 ]
adcx r10, [ rsp + 0x150 ]
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x238 ], rdi
mulx rdi, r12, r13
mov r13, r12
mov [ rsp + 0x240 ], r8
mov r8, -0x2 
inc r8
adox r13, rdi
adcx rcx, [ rsp + 0x160 ]
mov r8, r12
adox r8, rdi
adcx rbx, [ rsp + 0x158 ]
adcx r11, r15
setc r15b
clc
adcx r12, rdx
adcx r13, r9
adcx r8, rbp
mov r12, 0xfdc1767ae2ffffff 
mulx rbp, r9, r12
adox r9, rdi
adcx r9, r14
mov r14, 0x7bc65c783158aea3 
mulx r12, rdi, r14
adox rdi, rbp
adcx rdi, r10
mov r10, 0x6cfc5fd681c52056 
mulx r14, rbp, r10
adox rbp, r12
adox r14, [ rsp + 0x240 ]
adcx rbp, rcx
mov rdx, [ rsp + 0x238 ]
mov rcx, 0x0 
adox rdx, rcx
adcx r14, rbx
adcx rdx, r11
movzx rbx, r15b
adc rbx, 0x0
add r13, [ rsp - 0x48 ]
adcx r8, [ rsp + 0x98 ]
mov r15, 0xffffffffffffffff 
xchg rdx, r13
mulx r12, r11, r15
mov r10, r11
mov r15, -0x3 
inc r15
adox r10, rdx
adcx r9, [ rsp + 0x90 ]
adcx rdi, [ rsp + 0x88 ]
adcx rbp, [ rsp + 0xc0 ]
mov r10, 0xfdc1767ae2ffffff 
mulx r15, rcx, r10
adcx r14, [ rsp + 0xb8 ]
mov r10, r11
mov [ rsp + 0x248 ], rbx
setc bl
clc
adcx r10, r12
adox r10, r8
adcx r11, r12
adcx rcx, r12
adox r11, r9
mov r8, 0x7bc65c783158aea3 
mulx r9, r12, r8
adcx r12, r15
adox rcx, rdi
mov rdi, 0x6cfc5fd681c52056 
mulx r8, r15, rdi
adox r12, rbp
adcx r15, r9
adox r15, r14
mov rbp, 0x2341f27177344 
mulx r9, r14, rbp
adcx r14, r8
mov rdx, [ rsi + 0x30 ]
mulx rbp, r8, [ rax + 0x30 ]
mov rdx, 0x0 
adcx r9, rdx
movzx rdx, byte [ rsp + 0xe0 ]
clc
mov rdi, -0x1 
adcx rdx, rdi
adcx r8, [ rsp + 0xa8 ]
setc dl
clc
movzx rbx, bl
adcx rbx, rdi
adcx r13, r8
movzx rbx, dl
lea rbx, [ rbx + rbp ]
adox r14, r13
adcx rbx, [ rsp + 0x248 ]
adox r9, rbx
setc bpl
seto r8b
mov rdx, r10
mov r13, 0xffffffffffffffff 
sub rdx, r13
movzx rbx, r8b
movzx rbp, bpl
lea rbx, [ rbx + rbp ]
mov rbp, r11
sbb rbp, r13
mov r8, rcx
sbb r8, r13
mov rdi, r12
mov r13, 0xfdc1767ae2ffffff 
sbb rdi, r13
mov r13, r15
mov [ rsp + 0x250 ], r8
mov r8, 0x7bc65c783158aea3 
sbb r13, r8
mov r8, r14
mov [ rsp + 0x258 ], r13
mov r13, 0x6cfc5fd681c52056 
sbb r8, r13
mov r13, r9
mov [ rsp + 0x260 ], rbp
mov rbp, 0x2341f27177344 
sbb r13, rbp
sbb rbx, 0x00000000
cmovc rdx, r10
cmovc r13, r9
cmovc rdi, r12
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], rdx
cmovc r8, r14
mov r10, [ rsp + 0x260 ]
cmovc r10, r11
mov [ rbx + 0x28 ], r8
mov r11, [ rsp + 0x258 ]
cmovc r11, r15
mov [ rbx + 0x20 ], r11
mov [ rbx + 0x18 ], rdi
mov r12, [ rsp + 0x250 ]
cmovc r12, rcx
mov [ rbx + 0x30 ], r13
mov [ rbx + 0x8 ], r10
mov [ rbx + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 744
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.8852
; seed 0504316506317710 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11154040 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 232750 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.020866878727349013
; number reverted permutation / tried permutation: 74406 / 90271 =82.425%
; number reverted decision / tried decision: 63941 / 89728 =71.261%
; validated in 551.96s
