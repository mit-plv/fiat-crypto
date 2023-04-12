SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 640
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r9
mulx r9, r13, [ rax + 0x8 ]
xor rdx, rdx
adox r13, r12
adox r10, r9
mov rdx, [ rax + 0x8 ]
mulx r9, r12, [ rsi + 0x28 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
adcx r12, r14
adcx r8, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r14, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r12
mulx r12, r8, [ rax + 0x20 ]
adcx r14, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x18 ], r14
mulx r14, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, [ rax + 0x10 ]
adcx r8, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r8
mulx r8, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], r9
mov [ rsp + 0x10 ], r12
mulx r12, r9, [ rax + 0x18 ]
adox r9, r11
setc dl
clc
adcx r15, r8
adcx r14, rdi
mov r11b, dl
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rax + 0x18 ]
adcx rdi, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], rdi
mulx rdi, rcx, rbp
mov rdx, rcx
mov [ rsp + 0x20 ], r14
seto r14b
mov [ rsp + 0x28 ], r15
mov r15, -0x2 
inc r15
adox rdx, rdi
mov r15, rcx
mov [ rsp + 0x30 ], r12
setc r12b
clc
adcx r15, rbp
adcx rdx, r13
adox rcx, rdi
adcx rcx, r10
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mulx r10, r13, rbp
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r15
mulx r15, rcx, rbp
adox rcx, rdi
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x48 ], r14b
mulx r14, rdi, [ rax + 0x10 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x50 ], r8
mov byte [ rsp + 0x58 ], r12b
mulx r12, r8, rbp
adcx rcx, r9
setc r9b
clc
adcx rbx, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], rdi
mov [ rsp + 0x68 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
adox r13, r15
adcx rdi, r14
mov rdx, 0x6cfc5fd681c52056 
mulx r14, r15, rbp
adox r15, r10
adox r8, r14
mov rbp, 0x0 
adox r12, rbp
mov rdx, [ rax + 0x20 ]
mulx r14, r10, [ rsi + 0x30 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x70 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x78 ], rbp
mov [ rsp + 0x80 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x88 ], r12
mov [ rsp + 0x90 ], r8
mulx r8, r12, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r15
mov [ rsp + 0xa0 ], r13
mulx r13, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0xa8 ], r9b
mov [ rsp + 0xb0 ], r14
mulx r14, r9, [ rsi + 0x28 ]
mov rdx, -0x2 
inc rdx
adox r15, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xb8 ], r15
mulx r15, rdi, [ rax + 0x18 ]
adox r12, r13
adox rdi, r8
adox r10, r15
seto dl
mov r8, 0x0 
dec r8
movzx r11, r11b
adox r11, r8
adox r9, [ rsp + 0x10 ]
mov r11b, dl
mov rdx, [ rax + 0x30 ]
mulx r15, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r10
mulx r10, r8, [ rax + 0x28 ]
adcx rbp, rbx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xc8 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
adox r13, r14
adcx rbx, rcx
mov rdx, [ rsi + 0x30 ]
mulx r14, rcx, [ rax + 0x30 ]
setc dl
clc
mov [ rsp + 0xd0 ], r12
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r8, [ rsp + 0xb0 ]
adcx rcx, r10
mov r11b, dl
mov rdx, [ rax + 0x0 ]
mulx r12, r10, [ rsi + 0x20 ]
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], rcx
mulx rcx, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r8
mov [ rsp + 0xf0 ], r13
mulx r13, r8, [ rax + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xf8 ], r9
mov [ rsp + 0x100 ], r10
mulx r10, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
clc
adcx rbx, r12
adcx r9, rbp
adcx r14, r10
mov rdx, [ rsi + 0x20 ]
mulx r10, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x118 ], r14
mulx r14, rbp, [ rsi + 0x20 ]
adcx rbp, rcx
adcx r12, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], r12
mov [ rsp + 0x128 ], rbp
mulx rbp, r12, [ rax + 0x30 ]
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x130 ], r9
mov [ rsp + 0x138 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
adcx r12, r10
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x140 ], r12
mulx r12, r10, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rbp, rdx
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rdi, r8
mov r11, 0x0 
adox r15, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r8, [ rax + 0x28 ]
adc r13, 0x0
add byte [ rsp + 0x58 ], 0xFF
adcx rcx, [ rsp + 0x50 ]
adcx r10, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x148 ], r15
mulx r15, r14, [ rax + 0x18 ]
adcx r9, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x150 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
adc rbx, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x158 ], r13
mov [ rsp + 0x160 ], rdi
mulx rdi, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x168 ], rbx
mov [ rsp + 0x170 ], r9
mulx r9, rbx, [ rax + 0x30 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x178 ], r10
mov [ rsp + 0x180 ], rcx
mulx rcx, r10, [ rsi + 0x0 ]
add byte [ rsp + 0x48 ], 0xFF
adcx r10, [ rsp + 0x30 ]
adcx r8, rcx
adcx rbx, r11
adc r9, 0x0
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rax + 0x0 ]
add byte [ rsp + 0xa8 ], 0xFF
adcx r10, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x98 ]
adcx rbx, [ rsp + 0x90 ]
adox r13, rcx
adox r12, rdi
adcx r9, [ rsp + 0x88 ]
setc dl
clc
adcx r11, [ rsp + 0x40 ]
adox r14, rbp
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mulx rcx, rdi, [ rax + 0x20 ]
adox rdi, r15
adcx r13, [ rsp + 0x38 ]
adcx r12, [ rsp + 0x80 ]
adcx r14, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rax + 0x30 ]
adox rcx, [ rsp - 0x8 ]
adcx rdi, r8
adox r15, [ rsp - 0x10 ]
mov rdx, 0x0 
adox r10, rdx
adcx rcx, rbx
mov r8, 0xffffffffffffffff 
mov rdx, r11
mulx rbx, r11, r8
adcx r15, r9
mov r9, r11
mov r8, -0x2 
inc r8
adox r9, rbx
movzx r8, bpl
adcx r8, r10
mov rbp, r11
setc r10b
clc
adcx rbp, rdx
adcx r9, r13
adox r11, rbx
adcx r11, r12
mov rbp, 0xfdc1767ae2ffffff 
mulx r12, r13, rbp
adox r13, rbx
adcx r13, r14
mov r14, 0x7bc65c783158aea3 
mulx rbp, rbx, r14
adox rbx, r12
adcx rbx, rdi
mov rdi, 0x6cfc5fd681c52056 
mulx r14, r12, rdi
adox r12, rbp
adcx r12, rcx
mov rcx, 0x2341f27177344 
mulx rdi, rbp, rcx
adox rbp, r14
mov rdx, 0x0 
adox rdi, rdx
adcx rbp, r15
adcx rdi, r8
movzx r15, r10b
adc r15, 0x0
add r9, [ rsp + 0x8 ]
adcx r11, [ rsp + 0x28 ]
adcx r13, [ rsp + 0x20 ]
mov r10, 0xffffffffffffffff 
mov rdx, r9
mulx r8, r9, r10
mov r14, r9
mov rcx, -0x2 
inc rcx
adox r14, r8
adcx rbx, [ rsp + 0x18 ]
adcx r12, [ rsp + 0x180 ]
adcx rbp, [ rsp + 0x178 ]
adcx rdi, [ rsp + 0x170 ]
adcx r15, [ rsp + 0x168 ]
mov rcx, r9
setc r10b
clc
adcx rcx, rdx
adox r9, r8
adcx r14, r11
adcx r9, r13
mov rcx, 0xfdc1767ae2ffffff 
mulx r13, r11, rcx
adox r11, r8
adcx r11, rbx
mov r8, 0x7bc65c783158aea3 
mulx rcx, rbx, r8
adox rbx, r13
adcx rbx, r12
mov r12, 0x6cfc5fd681c52056 
mulx r8, r13, r12
adox r13, rcx
adcx r13, rbp
mov rbp, 0x2341f27177344 
mulx r12, rcx, rbp
adox rcx, r8
adcx rcx, rdi
setc dl
clc
adcx r14, [ rsp - 0x40 ]
adcx r9, [ rsp + 0x68 ]
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx rbp, r8, r14
adcx r11, [ rsp + 0x60 ]
mov rdx, 0x0 
adox r12, rdx
adcx rbx, [ rsp + 0x70 ]
dec rdx
movzx rdi, dil
adox rdi, rdx
adox r15, r12
adcx r13, [ rsp + 0x110 ]
adcx rcx, [ rsp + 0x108 ]
adcx r15, [ rsp + 0x160 ]
movzx rdi, r10b
mov r12, 0x0 
adox rdi, r12
mov r10, 0xffffffffffffffff 
mov rdx, r14
mulx r12, r14, r10
adcx rdi, [ rsp + 0x158 ]
mov r10, r14
mov [ rsp + 0x188 ], rdi
mov rdi, -0x2 
inc rdi
adox r10, rdx
mov r10, r14
setc dil
clc
adcx r10, r12
adox r10, r9
adcx r14, r12
adcx r8, r12
adox r14, r11
mov r9, 0x7bc65c783158aea3 
mulx r12, r11, r9
adcx r11, rbp
adox r8, rbx
adox r11, r13
mov rbp, 0x6cfc5fd681c52056 
mulx r13, rbx, rbp
adcx rbx, r12
adox rbx, rcx
mov rcx, 0x2341f27177344 
mulx rbp, r12, rcx
adcx r12, r13
adox r12, r15
setc dl
clc
adcx r10, [ rsp + 0x100 ]
movzx r15, dl
lea r15, [ r15 + rbp ]
mov rdx, r10
mulx r13, r10, r9
adcx r14, [ rsp + 0x138 ]
adcx r8, [ rsp + 0x130 ]
adcx r11, [ rsp + 0x118 ]
adcx rbx, [ rsp + 0x128 ]
adox r15, [ rsp + 0x188 ]
adcx r12, [ rsp + 0x120 ]
movzx rbp, dil
mov rcx, 0x0 
adox rbp, rcx
adcx r15, [ rsp + 0x140 ]
mov rdi, 0xffffffffffffffff 
mulx r9, rcx, rdi
mov rdi, rcx
mov [ rsp + 0x190 ], r15
mov r15, -0x2 
inc r15
adox rdi, r9
adcx rbp, [ rsp + 0x150 ]
mov r15, 0xfdc1767ae2ffffff 
mov [ rsp + 0x198 ], rbp
mov [ rsp + 0x1a0 ], r12
mulx r12, rbp, r15
mov r15, rcx
adox r15, r9
mov [ rsp + 0x1a8 ], rbx
setc bl
clc
adcx rcx, rdx
adcx rdi, r14
adox rbp, r9
adcx r15, r8
adcx rbp, r11
setc cl
clc
adcx rdi, [ rsp - 0x48 ]
adcx r15, [ rsp - 0x20 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rdi
mulx r11, r8, r14
mov r9, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x1b0 ], bl
mulx rbx, r14, r9
adcx rbp, [ rsp - 0x28 ]
mov r9, r8
mov [ rsp + 0x1b8 ], rbp
setc bpl
clc
adcx r9, r11
mov [ rsp + 0x1c0 ], r9
mov r9, r8
adcx r9, r11
adcx r14, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x1c8 ], r14
mov [ rsp + 0x1d0 ], r9
mulx r9, r14, r11
adcx r14, rbx
adox r10, r12
mov r12, 0x6cfc5fd681c52056 
mulx r11, rbx, r12
xchg rdx, r12
mov [ rsp + 0x1d8 ], r14
mov [ rsp + 0x1e0 ], r15
mulx r15, r14, rdi
adcx rbx, r9
adox r14, r13
setc r13b
clc
mov r9, -0x1 
movzx rcx, cl
adcx rcx, r9
adcx r10, [ rsp + 0x1a8 ]
mov rcx, 0x2341f27177344 
mov rdx, rcx
mulx r9, rcx, rdi
adox rcx, r15
adcx r14, [ rsp + 0x1a0 ]
mov rdi, 0x0 
adox r9, rdi
adcx rcx, [ rsp + 0x190 ]
adcx r9, [ rsp + 0x198 ]
mulx rdi, r15, r12
mov rdx, 0x0 
dec rdx
movzx rbp, bpl
adox rbp, rdx
adox r10, [ rsp - 0x18 ]
setc bpl
clc
movzx r13, r13b
adcx r13, rdx
adcx r11, r15
adox r14, [ rsp + 0x0 ]
adox rcx, [ rsp + 0xf8 ]
setc r13b
clc
adcx r8, r12
mov r8, [ rsp + 0x1c0 ]
adcx r8, [ rsp + 0x1e0 ]
adox r9, [ rsp + 0xf0 ]
mov r12, [ rsp + 0x1b8 ]
adcx r12, [ rsp + 0x1d0 ]
adcx r10, [ rsp + 0x1c8 ]
adcx r14, [ rsp + 0x1d8 ]
adcx rbx, rcx
movzx r15, bpl
movzx rcx, byte [ rsp + 0x1b0 ]
lea r15, [ r15 + rcx ]
adox r15, [ rsp + 0x148 ]
movzx rcx, r13b
lea rcx, [ rcx + rdi ]
adcx r11, r9
adcx rcx, r15
seto bpl
adc bpl, 0x0
movzx rbp, bpl
adox r8, [ rsp + 0x78 ]
mov rdi, 0xffffffffffffffff 
mov rdx, r8
mulx r13, r8, rdi
adox r12, [ rsp + 0xb8 ]
adox r10, [ rsp + 0xd0 ]
adox r14, [ rsp + 0xc8 ]
adox rbx, [ rsp + 0xc0 ]
adox r11, [ rsp + 0xe8 ]
adox rcx, [ rsp + 0xe0 ]
mov r9, r8
adcx r9, rdx
movzx rbp, bpl
movzx r9, bpl
adox r9, [ rsp + 0xd8 ]
mov r15, r8
seto bpl
mov rdi, -0x2 
inc rdi
adox r15, r13
adox r8, r13
adcx r15, r12
adcx r8, r10
mov r12, 0xfdc1767ae2ffffff 
mulx rdi, r10, r12
adox r10, r13
mov r13, 0x7bc65c783158aea3 
mov [ rsp + 0x1e8 ], r8
mulx r8, r12, r13
adox r12, rdi
adcx r10, r14
adcx r12, rbx
mov r14, 0x6cfc5fd681c52056 
mulx rdi, rbx, r14
adox rbx, r8
adcx rbx, r11
mov r11, 0x2341f27177344 
mulx r14, r8, r11
adox r8, rdi
adcx r8, rcx
mov rdx, 0x0 
adox r14, rdx
adcx r14, r9
movzx rcx, bpl
adc rcx, 0x0
mov rbp, r15
mov r9, 0xffffffffffffffff 
sub rbp, r9
mov rdi, [ rsp + 0x1e8 ]
sbb rdi, r9
mov rdx, r10
sbb rdx, r9
mov r11, r12
mov r13, 0xfdc1767ae2ffffff 
sbb r11, r13
mov r13, rbx
mov r9, 0x7bc65c783158aea3 
sbb r13, r9
mov r9, r8
mov [ rsp + 0x1f0 ], rdx
mov rdx, 0x6cfc5fd681c52056 
sbb r9, rdx
mov rdx, r14
mov [ rsp + 0x1f8 ], r9
mov r9, 0x2341f27177344 
sbb rdx, r9
sbb rcx, 0x00000000
cmovc rdi, [ rsp + 0x1e8 ]
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], rdi
cmovc r11, r12
cmovc r13, rbx
cmovc rbp, r15
mov [ rcx + 0x0 ], rbp
cmovc rdx, r14
mov r15, [ rsp + 0x1f0 ]
cmovc r15, r10
mov [ rcx + 0x10 ], r15
mov [ rcx + 0x30 ], rdx
mov r10, [ rsp + 0x1f8 ]
cmovc r10, r8
mov [ rcx + 0x20 ], r13
mov [ rcx + 0x18 ], r11
mov [ rcx + 0x28 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 640
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.8760
; seed 0645042749485548 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7844264 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=26, initial num_batches=31): 148681 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018954104553339866
; number reverted permutation / tried permutation: 72554 / 89775 =80.818%
; number reverted decision / tried decision: 64600 / 90224 =71.600%
; validated in 423.971s
