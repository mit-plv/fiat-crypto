SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 704
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
test al, al
adox r10, r8
adox r13, r11
mov rdx, [ rax + 0x18 ]
mulx r8, r11, [ rsi + 0x30 ]
adox r11, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x38 ], r11
mulx r11, r14, [ rsi + 0x30 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r10
mulx r10, r13, [ rsi + 0x18 ]
adcx r13, r12
adox r14, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r12, [ rax + 0x10 ]
adcx r12, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r14
mulx r14, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r13
mulx r13, r12, [ rax + 0x18 ]
adcx r12, r8
adcx r10, r13
adcx rcx, r14
mov rdx, [ rax + 0x28 ]
mulx r14, r8, [ rsi + 0x30 ]
adcx r9, rbp
mov rdx, [ rsi + 0x30 ]
mulx r13, rbp, [ rax + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], rcx
mulx rcx, r9, [ rsi + 0x28 ]
adox r8, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r8
mulx r8, r11, [ rsi + 0x28 ]
adox rbp, r14
mov rdx, 0x0 
adcx rbx, rdx
adox r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r9
mulx r9, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r10
mulx r10, rbx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x38 ], r12
mov [ rsp + 0x40 ], r10
mulx r10, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, rcx
adox rbx, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x0 ]
adcx r12, r8
adcx r15, r10
adcx rbp, rdi
mov rdx, 0xffffffffffffffff 
mulx r10, rdi, r14
mov r8, rdi
seto dl
mov [ rsp + 0x48 ], rbx
mov rbx, -0x2 
inc rbx
adox r8, r10
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], rbp
mulx rbp, r11, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], r15
mov [ rsp + 0x68 ], r12
mulx r12, r15, [ rax + 0x8 ]
mov rdx, rdi
adox rdx, r10
mov [ rsp + 0x70 ], rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0x78 ], rbp
mov byte [ rsp + 0x80 ], bl
mulx rbx, rbp, rcx
adox rbp, r10
mov r10, 0x7bc65c783158aea3 
mov [ rsp + 0x88 ], rbp
mulx rbp, rcx, r10
adox rcx, rbx
mov rbx, 0x6cfc5fd681c52056 
mov [ rsp + 0x90 ], rcx
mulx rcx, r10, rbx
adox r10, rbp
adcx r11, r9
mov r9, 0x2341f27177344 
mulx rbx, rbp, r9
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x98 ], r11
mov [ rsp + 0xa0 ], r10
mulx r10, r11, [ rsi + 0x0 ]
adox rbp, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xa8 ], rbp
mulx rbp, rcx, [ rsi + 0x0 ]
seto dl
mov [ rsp + 0xb0 ], r10
mov r10, -0x2 
inc r10
adox r15, r13
adox rcx, r12
adox r11, rbp
setc r13b
clc
adcx rdi, r9
adcx r8, r15
adcx r14, rcx
adcx r11, [ rsp + 0x88 ]
movzx rdi, dl
lea rdi, [ rdi + rbx ]
mov rdx, [ rax + 0x0 ]
mulx r12, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, [ rax + 0x8 ]
setc dl
clc
adcx rbx, r12
seto r15b
inc r10
adox r9, r8
adox rbx, r14
mov cl, dl
mov rdx, [ rax + 0x10 ]
mulx r14, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r10, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], rdi
mov byte [ rsp + 0xc0 ], cl
mulx rcx, rdi, [ rax + 0x8 ]
adcx r8, rbp
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0xc8 ], r15b
mulx r15, rbp, [ rsi + 0x8 ]
adcx rbp, r14
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
adox r8, r11
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, r11, [ rax + 0x28 ]
adcx r11, rbp
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd8 ], r11
mulx r11, rbp, [ rax + 0x0 ]
seto dl
mov [ rsp + 0xe0 ], rbp
mov rbp, -0x2 
inc rbp
adox rdi, r11
mov r11b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rdi
mulx rdi, rbp, [ rax + 0x18 ]
adox r12, rcx
adox rbp, r10
mov rdx, [ rax + 0x30 ]
mulx rcx, r10, [ rsi + 0x8 ]
adcx r10, r15
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xf0 ], rbp
mulx rbp, r15, [ rsi + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf8 ], r12
mov [ rsp + 0x100 ], r10
mulx r10, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x108 ], r14
mov byte [ rsp + 0x110 ], r11b
mulx r11, r14, [ rax + 0x20 ]
adox r14, rdi
adox r12, r11
mov rdx, [ rax + 0x30 ]
mulx r11, rdi, [ rsi + 0x20 ]
mov rdx, 0x0 
adcx rcx, rdx
adox rdi, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, r10, [ rax + 0x18 ]
movzx rdx, byte [ rsp + 0x80 ]
clc
mov [ rsp + 0x120 ], r12
mov r12, -0x1 
adcx rdx, r12
adcx r10, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x128 ], r10
mulx r10, r12, [ rax + 0x28 ]
adcx r15, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x130 ], r15
mulx r15, rdi, [ rax + 0x28 ]
adcx rdi, rbp
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x138 ], rdi
mulx rdi, rbp, [ rsi + 0x28 ]
adcx rbp, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x140 ], rbp
mulx rbp, r15, [ rax + 0x30 ]
mov rdx, 0x0 
adox r11, rdx
adc rdi, 0x0
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x148 ], rdi
mov [ rsp + 0x150 ], r11
mulx r11, rdi, r9
add r13b, 0xFF
adcx r12, [ rsp + 0x78 ]
adcx r15, r10
mov r13, rdi
adox r13, r9
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, [ rax + 0x20 ]
mov rdx, 0x0 
adcx rbp, rdx
mov [ rsp + 0x158 ], r14
mov r14, rdi
clc
adcx r14, r11
adox r14, rbx
adcx rdi, r11
adox rdi, r8
setc bl
clc
adcx r14, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0x68 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x160 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
setc dl
mov [ rsp + 0x168 ], rbp
movzx rbp, byte [ rsp + 0xc8 ]
clc
mov [ rsp + 0x170 ], r15
mov r15, -0x1 
adcx rbp, r15
adcx r13, [ rsp + 0xb0 ]
seto bpl
movzx r15, byte [ rsp + 0xc0 ]
mov [ rsp + 0x178 ], r12
mov r12, 0x0 
dec r12
adox r15, r12
adox r13, [ rsp + 0x90 ]
adcx r8, r10
mov r15b, dl
mov rdx, [ rsi + 0x0 ]
mulx r12, r10, [ rax + 0x30 ]
adcx r10, rdi
adox r8, [ rsp + 0xa0 ]
adox r10, [ rsp + 0xa8 ]
setc dl
movzx rdi, byte [ rsp + 0x110 ]
clc
mov byte [ rsp + 0x180 ], r15b
mov r15, -0x1 
adcx rdi, r15
adcx r13, [ rsp + 0xd0 ]
adcx r8, [ rsp + 0x108 ]
movzx rdi, dl
lea rdi, [ rdi + r12 ]
mov r12, 0xfdc1767ae2ffffff 
mov rdx, r9
mulx r15, r9, r12
adox rdi, [ rsp + 0xb8 ]
adcx r10, [ rsp + 0xd8 ]
adcx rdi, [ rsp + 0x100 ]
seto r12b
movzx r12, r12b
adcx r12, rcx
mov rcx, -0x1 
inc rcx
mov rcx, -0x1 
movzx rbx, bl
adox rbx, rcx
adox r11, r9
setc bl
clc
movzx rbp, bpl
adcx rbp, rcx
adcx r13, r11
mov rbp, 0x7bc65c783158aea3 
mulx r11, r9, rbp
adox r9, r15
adcx r9, r8
mov r8, 0x6cfc5fd681c52056 
mulx rcx, r15, r8
adox r15, r11
adcx r15, r10
mov r10, 0x2341f27177344 
mulx r8, r11, r10
adox r11, rcx
adcx r11, rdi
mov rdx, 0x0 
adox r8, rdx
adcx r8, r12
movzx rdi, bl
adc rdi, 0x0
mov r12, 0xffffffffffffffff 
mov rdx, r14
mulx rbx, r14, r12
add byte [ rsp + 0x180 ], 0xFF
adcx r13, [ rsp + 0x60 ]
mov rcx, r14
adox rcx, rdx
adcx r9, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x98 ]
adcx r11, [ rsp + 0x178 ]
adcx r8, [ rsp + 0x170 ]
mulx r10, rcx, rbp
adcx rdi, [ rsp + 0x168 ]
mov rbp, r14
setc r12b
clc
adcx rbp, rbx
adcx r14, rbx
mov byte [ rsp + 0x188 ], r12b
mov r12, 0xfdc1767ae2ffffff 
mov [ rsp + 0x190 ], rdi
mov [ rsp + 0x198 ], r8
mulx r8, rdi, r12
adcx rdi, rbx
adcx rcx, r8
adox rbp, [ rsp + 0x160 ]
adox r14, r13
adox rdi, r9
adox rcx, r15
setc bl
clc
adcx rbp, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx r15, r9, rbp
mov r8, r9
seto r12b
mov rdx, -0x2 
inc rdx
adox r8, r15
adcx rcx, [ rsp + 0x38 ]
mov rdx, r9
mov [ rsp + 0x1a0 ], rcx
setc cl
clc
adcx rdx, rbp
mov rdx, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x1a8 ], cl
mov [ rsp + 0x1b0 ], r11
mulx r11, rcx, r13
adcx r8, r14
adox r9, r15
adcx r9, rdi
mov r14, 0x2341f27177344 
mov rdx, r13
mulx rdi, r13, r14
setc dl
clc
mov r14, -0x1 
movzx rbx, bl
adcx rbx, r14
adcx r10, rcx
seto bl
inc r14
adox r8, [ rsp + 0xe0 ]
adcx r13, r11
adox r9, [ rsp + 0xe8 ]
seto cl
dec r14
movzx r12, r12b
adox r12, r14
adox r10, [ rsp + 0x1b0 ]
setc r12b
movzx r11, byte [ rsp + 0x1a8 ]
clc
adcx r11, r14
adcx r10, [ rsp + 0x30 ]
adox r13, [ rsp + 0x198 ]
adcx r13, [ rsp + 0x0 ]
movzx r11, r12b
lea r11, [ r11 + rdi ]
adox r11, [ rsp + 0x190 ]
movzx rdi, byte [ rsp + 0x188 ]
mov r12, 0x0 
adox rdi, r12
mov r12, 0xffffffffffffffff 
xchg rdx, r8
mov [ rsp + 0x1b8 ], r9
mulx r9, r14, r12
mov r12, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x1c0 ], cl
mov [ rsp + 0x1c8 ], r13
mulx r13, rcx, r12
mov r12, r14
mov [ rsp + 0x1d0 ], r10
mov r10, -0x2 
inc r10
adox r12, r9
mov r10, r14
adox r10, r9
adox rcx, r9
mov r9, 0x7bc65c783158aea3 
mov [ rsp + 0x1d8 ], rcx
mov [ rsp + 0x1e0 ], r10
mulx r10, rcx, r9
adcx r11, [ rsp - 0x8 ]
adox rcx, r13
mov r13, 0x6cfc5fd681c52056 
mov [ rsp + 0x1e8 ], rcx
mulx rcx, r9, r13
adcx rdi, [ rsp + 0x28 ]
adox r9, r10
mov r10, 0x2341f27177344 
mov [ rsp + 0x1f0 ], r9
mulx r9, r13, r10
adox r13, rcx
mov rcx, 0xfdc1767ae2ffffff 
xchg rdx, rcx
mov [ rsp + 0x1f8 ], r13
mulx r13, r10, rbp
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x200 ], r12
mov [ rsp + 0x208 ], rdi
mulx rdi, r12, rbp
mov rdx, 0x0 
adox r9, rdx
dec rdx
movzx rbx, bl
adox rbx, rdx
adox r15, r10
setc bl
clc
movzx r8, r8b
adcx r8, rdx
adcx r15, [ rsp + 0x1a0 ]
adox r12, r13
adcx r12, [ rsp + 0x1d0 ]
mov r8, 0x6cfc5fd681c52056 
mov rdx, rbp
mulx r10, rbp, r8
adox rbp, rdi
mov r13, 0x2341f27177344 
mulx r8, rdi, r13
adcx rbp, [ rsp + 0x1c8 ]
adox rdi, r10
adcx rdi, r11
mov rdx, 0x0 
adox r8, rdx
adcx r8, [ rsp + 0x208 ]
movzx r11, bl
adc r11, 0x0
add byte [ rsp + 0x1c0 ], 0xFF
adcx r15, [ rsp + 0xf8 ]
adcx r12, [ rsp + 0xf0 ]
adcx rbp, [ rsp + 0x158 ]
adcx rdi, [ rsp + 0x120 ]
adcx r8, [ rsp + 0x118 ]
adox r14, rcx
mov r14, [ rsp + 0x1b8 ]
adox r14, [ rsp + 0x200 ]
adox r15, [ rsp + 0x1e0 ]
adox r12, [ rsp + 0x1d8 ]
adox rbp, [ rsp + 0x1e8 ]
adox rdi, [ rsp + 0x1f0 ]
adox r8, [ rsp + 0x1f8 ]
adcx r11, [ rsp + 0x150 ]
adox r9, r11
seto cl
adc cl, 0x0
movzx rcx, cl
adox r14, [ rsp + 0x20 ]
adox r15, [ rsp + 0x50 ]
adox r12, [ rsp + 0x48 ]
adox rbp, [ rsp + 0x128 ]
adox rdi, [ rsp + 0x130 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r14
mulx r10, r14, rbx
adox r8, [ rsp + 0x138 ]
mov r11, 0xfdc1767ae2ffffff 
mulx rbx, r13, r11
mov r11, r14
adcx r11, r10
adox r9, [ rsp + 0x140 ]
mov [ rsp + 0x210 ], r9
mov r9, r14
adcx r9, r10
movzx rcx, cl
mov [ rsp + 0x218 ], r8
movzx r8, cl
adox r8, [ rsp + 0x148 ]
adcx r13, r10
seto cl
mov r10, -0x2 
inc r10
adox r14, rdx
adox r11, r15
adox r9, r12
adox r13, rbp
mov r14, 0x7bc65c783158aea3 
mulx r12, r15, r14
adcx r15, rbx
adox r15, rdi
mov rbp, 0x6cfc5fd681c52056 
mulx rbx, rdi, rbp
mov r10, 0x2341f27177344 
mulx r14, rbp, r10
adcx rdi, r12
adox rdi, [ rsp + 0x218 ]
adcx rbp, rbx
mov rdx, 0x0 
adcx r14, rdx
adox rbp, [ rsp + 0x210 ]
adox r14, r8
movzx r8, cl
adox r8, rdx
add r11, [ rsp - 0x48 ]
adcx r9, [ rsp - 0x28 ]
mov rcx, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r12, r11, rcx
adcx r13, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x20 ]
adcx rbp, [ rsp + 0x8 ]
mov rbx, 0xffffffffffffffff 
mulx rcx, r10, rbx
mov rbx, r10
mov [ rsp + 0x220 ], rbp
mov rbp, -0x2 
inc rbp
adox rbx, rcx
mov rbp, r10
adox rbp, rcx
adox r11, rcx
adcx r14, [ rsp + 0x18 ]
adcx r8, [ rsp + 0x10 ]
setc cl
clc
adcx r10, rdx
adcx rbx, r9
adcx rbp, r13
adcx r11, r15
mov r10, 0x7bc65c783158aea3 
mulx r13, r9, r10
adox r9, r12
adcx r9, rdi
mov r12, 0x6cfc5fd681c52056 
mulx rdi, r15, r12
adox r15, r13
adcx r15, [ rsp + 0x220 ]
mov r13, 0x2341f27177344 
mulx r10, r12, r13
adox r12, rdi
mov rdx, 0x0 
adox r10, rdx
adcx r12, r14
adcx r10, r8
movzx r14, cl
adc r14, 0x0
mov rcx, rbx
mov r8, 0xffffffffffffffff 
sub rcx, r8
mov rdi, rbp
sbb rdi, r8
mov rdx, r11
sbb rdx, r8
mov r13, r9
mov r8, 0xfdc1767ae2ffffff 
sbb r13, r8
mov r8, r15
mov [ rsp + 0x228 ], r13
mov r13, 0x7bc65c783158aea3 
sbb r8, r13
mov r13, r12
mov [ rsp + 0x230 ], r8
mov r8, 0x6cfc5fd681c52056 
sbb r13, r8
mov r8, r10
mov [ rsp + 0x238 ], rdx
mov rdx, 0x2341f27177344 
sbb r8, rdx
sbb r14, 0x00000000
cmovc r8, r10
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x30 ], r8
cmovc rdi, rbp
cmovc r13, r12
cmovc rcx, rbx
mov [ r14 + 0x0 ], rcx
mov rbx, [ rsp + 0x238 ]
cmovc rbx, r11
mov [ r14 + 0x10 ], rbx
mov rbp, [ rsp + 0x228 ]
cmovc rbp, r9
mov [ r14 + 0x18 ], rbp
mov r11, [ rsp + 0x230 ]
cmovc r11, r15
mov [ r14 + 0x28 ], r13
mov [ r14 + 0x8 ], rdi
mov [ r14 + 0x20 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 704
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.8016
; seed 0157939846892472 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7826727 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=26, initial num_batches=31): 151254 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019325319510952663
; number reverted permutation / tried permutation: 73460 / 89876 =81.735%
; number reverted decision / tried decision: 65737 / 90123 =72.941%
; validated in 407.282s
