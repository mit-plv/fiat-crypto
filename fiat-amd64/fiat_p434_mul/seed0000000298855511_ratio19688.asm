SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 704
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r9
mulx r9, r15, [ rax + 0x8 ]
test al, al
adox r15, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
adox r10, r9
adox rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, [ rax + 0x20 ]
adox rcx, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r10
mulx r10, rdi, [ rax + 0x0 ]
adcx r15, r10
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x18 ], r15
mulx r15, r10, [ rsi + 0x28 ]
adox r10, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r10
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r9
mulx r9, rdi, [ rsi + 0x28 ]
adcx r8, rcx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r12
mulx r12, r11, [ rax + 0x18 ]
adcx r11, r10
adcx rcx, r12
adox rdi, r15
mov rdx, [ rax + 0x28 ]
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r9, rdx
adcx r15, r8
adcx r13, r10
adc r14, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r9
mulx r9, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r14
mulx r14, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r13
mov [ rsp + 0x40 ], r15
mulx r15, r13, [ rax + 0x8 ]
xor rdx, rdx
adox rdi, r9
adox r8, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, r9, [ rax + 0x10 ]
adcx r13, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
adcx r9, r15
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x50 ], r11
mulx r11, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x58 ], r15
mov [ rsp + 0x60 ], r8
mulx r8, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x68 ], rdi
mov [ rsp + 0x70 ], r10
mulx r10, rdi, [ rax + 0x10 ]
adox rbx, r12
seto dl
mov r12, -0x2 
inc r12
adox rbp, r11
adox rdi, [ rsp + 0x18 ]
mov r11b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x78 ], rdi
mulx rdi, r12, [ rax + 0x30 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
adcx rbp, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], rbp
mulx rbp, r14, [ rax + 0x8 ]
adcx rbx, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], rbx
mov [ rsp + 0xa0 ], r9
mulx r9, rbx, [ rax + 0x20 ]
adox r15, r10
adox rbx, r8
mov rdx, [ rax + 0x28 ]
mulx r10, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
adox r8, r9
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb8 ], r8
mulx r8, r9, [ rsi + 0x30 ]
adox rbx, r10
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc0 ], r9
mulx r9, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
mov rdx, 0x0 
dec rdx
movzx r11, r11b
adox r11, rdx
adox rcx, r15
seto r11b
inc rdx
adox r14, r8
mov rdx, [ rsi + 0x30 ]
mulx r15, r8, [ rax + 0x10 ]
adox r8, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd8 ], r8
mulx r8, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe0 ], r14
mov [ rsp + 0xe8 ], rcx
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xf0 ], r14
mov [ rsp + 0xf8 ], r13
mulx r13, r14, [ rsi + 0x30 ]
setc dl
clc
adcx r10, rcx
mov cl, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x100 ], r10
mov [ rsp + 0x108 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
adox r14, r15
adcx r10, r9
adox rbp, r13
mov rdx, 0x7bc65c783158aea3 
mulx r15, r9, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x110 ], rbp
mulx rbp, r13, [ rax + 0x28 ]
adox r13, r8
adox r12, rbp
mov rdx, 0x6cfc5fd681c52056 
mulx rbp, r8, [ rsp - 0x40 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x118 ], r12
mov [ rsp + 0x120 ], r13
mulx r13, r12, [ rsp - 0x40 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x128 ], r14
mov [ rsp + 0x130 ], r10
mulx r10, r14, [ rsp - 0x40 ]
mov rdx, r14
mov [ rsp + 0x138 ], rbx
setc bl
clc
adcx rdx, r10
mov [ rsp + 0x140 ], rdx
mov rdx, r14
adcx rdx, r10
mov [ rsp + 0x148 ], rdx
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x150 ], bl
mov byte [ rsp + 0x158 ], cl
mulx rcx, rbx, [ rsp - 0x40 ]
adcx r12, r10
adcx r9, r13
mov r13, 0x0 
adox rdi, r13
adcx r8, r15
adcx rbx, rbp
mov rdx, [ rax + 0x30 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, [ rax + 0x28 ]
adc rcx, 0x0
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x160 ], rdi
mov [ rsp + 0x168 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
add r11b, 0xFF
adcx r10, [ rsp + 0x108 ]
adcx r15, r13
adc rbp, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x170 ], rbp
mov [ rsp + 0x178 ], r15
mulx r15, rbp, [ rax + 0x28 ]
add byte [ rsp + 0x158 ], 0xFF
adcx rbp, [ rsp + 0x0 ]
adcx rdi, r15
adc rcx, 0x0
add byte [ rsp + 0x150 ], 0x7F
adox r11, [ rsp + 0x138 ]
adcx r14, [ rsp - 0x40 ]
mov rdx, [ rax + 0x20 ]
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsp + 0x140 ]
adcx rdx, [ rsp + 0xf8 ]
mov [ rsp + 0x180 ], r11
mov r11, [ rsp + 0xa0 ]
adcx r11, [ rsp + 0x148 ]
adcx r12, [ rsp + 0x90 ]
adcx r9, [ rsp + 0x98 ]
adcx r8, rbp
adox r14, r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x188 ], r14
mulx r14, rbp, [ rax + 0x28 ]
adox rbp, r15
adcx rbx, rdi
adcx rcx, [ rsp + 0x168 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rdi, [ rax + 0x30 ]
adox rdi, r14
setc dl
clc
adcx r13, [ rsp + 0x70 ]
adcx r11, [ rsp + 0x68 ]
adcx r12, [ rsp + 0x60 ]
adcx r9, [ rsp + 0x88 ]
adcx r8, [ rsp + 0xe8 ]
adcx r10, rbx
mov r14, 0x0 
adox r15, r14
adcx rcx, [ rsp + 0x178 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, r13
mov [ rsp + 0x190 ], r15
mulx r15, r14, rbx
movzx r13, r13b
movzx rbx, r13b
adcx rbx, [ rsp + 0x170 ]
mov r13, r14
mov [ rsp + 0x198 ], rdi
mov rdi, -0x2 
inc rdi
adox r13, r15
mov rdi, r14
adox rdi, r15
mov [ rsp + 0x1a0 ], rbp
setc bpl
clc
adcx r14, rdx
adcx r13, r11
adcx rdi, r12
mov r14, 0xfdc1767ae2ffffff 
mulx r12, r11, r14
adox r11, r15
adcx r11, r9
mov r9, 0x7bc65c783158aea3 
mulx r14, r15, r9
adox r15, r12
adcx r15, r8
mov r8, 0x6cfc5fd681c52056 
mulx r9, r12, r8
adox r12, r14
adcx r12, r10
mov r10, 0x2341f27177344 
mulx r8, r14, r10
adox r14, r9
adcx r14, rcx
mov rdx, 0x0 
adox r8, rdx
adcx r8, rbx
movzx rcx, bpl
adc rcx, 0x0
xor rbp, rbp
adox r13, [ rsp - 0x8 ]
adox rdi, [ rsp - 0x18 ]
adox r11, [ rsp + 0x8 ]
adox r15, [ rsp + 0x50 ]
adox r12, [ rsp + 0x48 ]
mov rdx, 0xffffffffffffffff 
mulx r9, rbx, r13
mov r10, rbx
adcx r10, r9
adox r14, [ rsp + 0x40 ]
adox r8, [ rsp + 0x38 ]
adox rcx, [ rsp + 0x30 ]
mov rdx, rbx
mov [ rsp + 0x1a8 ], rcx
seto cl
mov [ rsp + 0x1b0 ], r8
mov r8, -0x3 
inc r8
adox rdx, r13
adox r10, rdi
adcx rbx, r9
mov rdx, 0xfdc1767ae2ffffff 
mulx rbp, rdi, r13
adcx rdi, r9
mov r9, 0x7bc65c783158aea3 
mov rdx, r13
mulx r8, r13, r9
adox rbx, r11
adcx r13, rbp
adox rdi, r15
mov r11, 0x6cfc5fd681c52056 
mulx rbp, r15, r11
adcx r15, r8
adox r13, r12
mov r12, 0x2341f27177344 
mulx r11, r8, r12
adcx r8, rbp
adox r15, r14
adox r8, [ rsp + 0x1b0 ]
mov rdx, 0x0 
adcx r11, rdx
adox r11, [ rsp + 0x1a8 ]
clc
adcx r10, [ rsp + 0xf0 ]
movzx r14, cl
adox r14, rdx
mov rcx, 0xffffffffffffffff 
mov rdx, r10
mulx rbp, r10, rcx
adcx rbx, [ rsp + 0x100 ]
mulx rcx, r12, r9
adcx rdi, [ rsp + 0x130 ]
adcx r13, [ rsp + 0x180 ]
adcx r15, [ rsp + 0x188 ]
adcx r8, [ rsp + 0x1a0 ]
adcx r11, [ rsp + 0x198 ]
adcx r14, [ rsp + 0x190 ]
mov r9, r10
mov [ rsp + 0x1b8 ], r14
mov r14, -0x2 
inc r14
adox r9, rdx
mov r9, r10
setc r14b
clc
adcx r9, rbp
adcx r10, rbp
adox r9, rbx
mov rbx, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x1c0 ], r14b
mov [ rsp + 0x1c8 ], r11
mulx r11, r14, rbx
adcx r14, rbp
adcx r12, r11
adox r10, rdi
setc bpl
clc
adcx r9, [ rsp + 0x58 ]
adox r14, r13
mov rdi, 0xffffffffffffffff 
xchg rdx, r9
mulx r11, r13, rdi
mov [ rsp + 0x1d0 ], r8
mulx r8, rdi, rbx
adcx r10, [ rsp + 0x80 ]
adcx r14, [ rsp + 0x78 ]
adox r12, r15
adcx r12, [ rsp + 0xb0 ]
mov r15, r13
seto bl
mov [ rsp + 0x1d8 ], rcx
mov rcx, -0x2 
inc rcx
adox r15, rdx
mov r15, r13
setc cl
clc
adcx r15, r11
adcx r13, r11
adcx rdi, r11
adox r15, r10
adox r13, r14
adox rdi, r12
mov r11, 0x7bc65c783158aea3 
mulx r14, r10, r11
adcx r10, r8
seto r8b
mov r12, -0x2 
inc r12
adox r15, [ rsp - 0x48 ]
adox r13, [ rsp - 0x38 ]
mov r12, 0x2341f27177344 
xchg rdx, r12
mov [ rsp + 0x1e0 ], r13
mulx r13, r11, r15
adox rdi, [ rsp - 0x20 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x1e8 ], r13
mov [ rsp + 0x1f0 ], rdi
mulx rdi, r13, r12
adcx r13, r14
mov [ rsp + 0x1f8 ], r11
mulx r11, r14, r9
mov rdx, 0x2341f27177344 
mov [ rsp + 0x200 ], r13
mov [ rsp + 0x208 ], r10
mulx r10, r13, r12
adcx r13, rdi
mulx rdi, r12, r9
seto r9b
mov rdx, 0x0 
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r14, [ rsp + 0x1d8 ]
adox r12, r11
mov rbp, 0x0 
adcx r10, rbp
clc
movzx rbx, bl
adcx rbx, rdx
adcx r14, [ rsp + 0x1d0 ]
adox rdi, rbp
adcx r12, [ rsp + 0x1c8 ]
adcx rdi, [ rsp + 0x1b8 ]
movzx rbx, byte [ rsp + 0x1c0 ]
adc rbx, 0x0
add cl, 0xFF
adcx r14, [ rsp + 0xa8 ]
movzx r8, r8b
adox r8, rdx
adox r14, [ rsp + 0x208 ]
adcx r12, [ rsp + 0xb8 ]
adox r12, [ rsp + 0x200 ]
adcx rdi, [ rsp + 0xd0 ]
adcx rbx, [ rsp + 0xc8 ]
adox r13, rdi
adox r10, rbx
mov rcx, 0xffffffffffffffff 
mov rdx, r15
mulx r8, r15, rcx
seto r11b
adc r11b, 0x0
movzx r11, r11b
add r9b, 0x7F
adox r14, [ rsp - 0x28 ]
adox r12, [ rsp - 0x30 ]
adox r13, [ rsp - 0x10 ]
mov r9, r15
adcx r9, r8
adox r10, [ rsp + 0x28 ]
mov rdi, r15
adcx rdi, r8
mov rbx, 0x7bc65c783158aea3 
mulx rcx, rbp, rbx
mov rbx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x210 ], r10
mov [ rsp + 0x218 ], r13
mulx r13, r10, rbx
adcx r10, r8
adcx rbp, r13
movzx r11, r11b
movzx r8, r11b
adox r8, [ rsp + 0x20 ]
mov r11, 0x6cfc5fd681c52056 
mulx rbx, r13, r11
adcx r13, rcx
adcx rbx, [ rsp + 0x1f8 ]
seto cl
mov r11, -0x2 
inc r11
adox r15, rdx
adox r9, [ rsp + 0x1e0 ]
adox rdi, [ rsp + 0x1f0 ]
adox r10, r14
mov r15, [ rsp + 0x1e8 ]
mov rdx, 0x0 
adcx r15, rdx
clc
adcx r9, [ rsp + 0xc0 ]
adox rbp, r12
adox r13, [ rsp + 0x218 ]
adox rbx, [ rsp + 0x210 ]
adox r15, r8
mov r14, 0x7bc65c783158aea3 
mov rdx, r9
mulx r12, r9, r14
movzx r8, cl
mov r11, 0x0 
adox r8, r11
adcx rdi, [ rsp + 0xe0 ]
mov rcx, 0xffffffffffffffff 
mulx r14, r11, rcx
adcx r10, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x128 ]
adcx r13, [ rsp + 0x110 ]
adcx rbx, [ rsp + 0x120 ]
adcx r15, [ rsp + 0x118 ]
adcx r8, [ rsp + 0x160 ]
mov rcx, r11
mov [ rsp + 0x220 ], r8
mov r8, -0x2 
inc r8
adox rcx, rdx
mov rcx, r11
setc r8b
clc
adcx rcx, r14
adox rcx, rdi
adcx r11, r14
adox r11, r10
mov rdi, 0xfdc1767ae2ffffff 
mov [ rsp + 0x228 ], r11
mulx r11, r10, rdi
adcx r10, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x230 ], rcx
mulx rcx, rdi, r14
adcx r9, r11
adox r10, rbp
adox r9, r13
adcx rdi, r12
adox rdi, rbx
mov r12, 0x2341f27177344 
mulx r13, rbp, r12
adcx rbp, rcx
mov rdx, 0x0 
adcx r13, rdx
adox rbp, r15
adox r13, [ rsp + 0x220 ]
movzx rbx, r8b
adox rbx, rdx
mov r15, [ rsp + 0x230 ]
mov r8, 0xffffffffffffffff 
sub r15, r8
mov r11, [ rsp + 0x228 ]
sbb r11, r8
mov rcx, r10
sbb rcx, r8
mov rdx, r9
mov r12, 0xfdc1767ae2ffffff 
sbb rdx, r12
mov r8, rdi
mov r12, 0x7bc65c783158aea3 
sbb r8, r12
mov r12, rbp
sbb r12, r14
mov r14, r13
mov [ rsp + 0x238 ], rdx
mov rdx, 0x2341f27177344 
sbb r14, rdx
sbb rbx, 0x00000000
cmovc r15, [ rsp + 0x230 ]
cmovc r11, [ rsp + 0x228 ]
cmovc rcx, r10
cmovc r8, rdi
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x20 ], r8
mov [ rbx + 0x8 ], r11
cmovc r12, rbp
mov [ rbx + 0x28 ], r12
mov [ rbx + 0x0 ], r15
mov r10, [ rsp + 0x238 ]
cmovc r10, r9
mov [ rbx + 0x18 ], r10
mov [ rbx + 0x10 ], rcx
cmovc r14, r13
mov [ rbx + 0x30 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 704
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.9688
; seed 3777099984904796 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11449209 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=48, initial num_batches=31): 225787 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019720751014327714
; number reverted permutation / tried permutation: 73719 / 89793 =82.099%
; number reverted decision / tried decision: 64030 / 90206 =70.982%
; validated in 538.336s
