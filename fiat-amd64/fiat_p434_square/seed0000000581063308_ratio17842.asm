SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 736
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
add r12, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r12
mulx r12, rbp, rax
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], rbx
mulx rbx, r14, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r14
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rdi
mulx rdi, r11, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], r10
mulx r10, r15, [ rsi + 0x20 ]
adcx rbx, r13
adcx r11, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, r13, [ rsi + 0x28 ]
adcx r8, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x8 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
adcx r13, r9
adcx rdi, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, r9, rdx
mov rdx, -0x2 
inc rdx
adox r9, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], rdi
mulx rdi, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r11
mulx r11, r13, [ rsi + 0x8 ]
adox r13, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rbx
mulx rbx, r14, rdx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r13
mulx r13, rcx, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], r13
mov [ rsp + 0x48 ], r10
mulx r10, r13, [ rsi + 0x10 ]
mov rdx, rbp
mov [ rsp + 0x50 ], r15
setc r15b
clc
adcx rdx, r12
mov [ rsp + 0x58 ], r9
mov r9, rbp
adcx r9, r12
adcx rcx, r12
movzx r12, r15b
lea r12, [ r12 + r8 ]
setc r8b
clc
adcx r13, rdi
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r13
mov byte [ rsp + 0x70 ], r8b
mulx r8, r13, [ rsi + 0x10 ]
adcx r14, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r14
mulx r14, r10, [ rsi + 0x8 ]
adcx r13, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
adox rbx, r11
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x88 ], rbx
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], r11
mov [ rsp + 0x98 ], r12
mulx r12, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa0 ], r12
mov [ rsp + 0xa8 ], rcx
mulx rcx, r12, [ rsi + 0x20 ]
adcx rdi, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], rdi
mulx rdi, r8, [ rsi + 0x10 ]
adox r10, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r10
mulx r10, r13, [ rsi + 0x28 ]
adox r13, r14
setc dl
clc
adcx r12, rbx
adcx r8, rcx
mov r14b, dl
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r12
mulx r12, r8, [ rsi + 0x8 ]
adox r8, r10
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r8
mulx r8, r10, [ rsi + 0x18 ]
adcx r11, rdi
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbx, [ rsp + 0x0 ]
adox rdi, rcx
setc cl
clc
adcx rbp, rax
adcx r15, rbx
mov rdx, [ rsi + 0x30 ]
mulx rbx, rbp, [ rsi + 0x0 ]
adcx r9, rdi
adox r11, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf0 ], rbp
mulx rbp, rdi, [ rsi + 0x30 ]
adcx r11, [ rsp + 0xa8 ]
setc dl
clc
adcx r12, rbx
adcx rdi, r13
mov r13b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf8 ], rdi
mulx rdi, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x100 ], r12
mov byte [ rsp + 0x108 ], cl
mulx rcx, r12, [ rsi + 0x0 ]
adox r12, [ rsp - 0x10 ]
seto dl
mov [ rsp + 0x110 ], r12
mov r12, -0x2 
inc r12
adox r15, [ rsp - 0x18 ]
adcx r10, rbp
adox r9, [ rsp + 0x58 ]
adcx r8, [ rsp + 0x50 ]
adcx rbx, [ rsp + 0x48 ]
adox r11, [ rsp + 0x38 ]
mov bpl, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], rbx
mulx rbx, r12, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x120 ], r8
mov r8, 0x0 
dec r8
movzx r14, r14b
adox r14, r8
adox r12, [ rsp + 0x98 ]
mov r14b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], r10
mulx r10, r8, rdx
adcx r8, rdi
mov rdx, 0x2341f27177344 
mov [ rsp + 0x130 ], r8
mulx r8, rdi, rax
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r10
mov [ rsp + 0x140 ], r12
mulx r12, r10, [ rsi + 0x30 ]
adox r10, rbx
mov rdx, 0x0 
adox r12, rdx
mov rbx, 0x7bc65c783158aea3 
mov rdx, rbx
mov [ rsp + 0x148 ], r12
mulx r12, rbx, rax
add byte [ rsp + 0x70 ], 0xFF
adcx rbx, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r10
mulx r10, rax, [ rsi + 0x28 ]
adcx r12, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
adc r8, 0x0
add bpl, 0x7F
adox rcx, rax
mov rdx, [ rsi + 0x30 ]
mulx rax, rbp, [ rsi + 0x0 ]
adox rbp, r10
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx rbx, [ rsp + 0x110 ]
mov r13, 0x0 
adox rax, r13
adcx r12, rcx
adcx rdi, rbp
mov r10, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r10
adcx r8, rax
mov rbp, r15
mov rax, -0x3 
inc rax
adox rbp, rdx
mov rbp, r15
setc al
clc
adcx rbp, rcx
adcx r15, rcx
mov r13, 0x7bc65c783158aea3 
mov byte [ rsp + 0x158 ], al
mulx rax, r10, r13
mov r13, 0xfdc1767ae2ffffff 
mov [ rsp + 0x160 ], r8
mov [ rsp + 0x168 ], rdi
mulx rdi, r8, r13
adcx r8, rcx
adcx r10, rdi
adox rbp, r9
mov r9, 0x6cfc5fd681c52056 
mulx rdi, rcx, r9
adcx rcx, rax
mov rax, 0x2341f27177344 
mulx r13, r9, rax
adcx r9, rdi
adox r15, r11
mov rdx, 0x0 
adcx r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx rdi, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x170 ], r11
mulx r11, rax, [ rsi + 0x8 ]
clc
adcx rax, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x178 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
adcx rdi, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x180 ], rdi
mulx rdi, r11, [ rsi + 0x28 ]
adcx r11, rax
setc dl
clc
mov rax, -0x1 
movzx r14, r14b
adcx r14, rax
adcx rbx, [ rsp + 0x88 ]
adox r8, rbx
adcx r12, [ rsp + 0xb8 ]
mov r14b, dl
mov rdx, [ rsi + 0x28 ]
mulx rax, rbx, rdx
mov rdx, [ rsp + 0x168 ]
adcx rdx, [ rsp + 0xe8 ]
mov [ rsp + 0x188 ], r11
mov r11, [ rsp + 0xd0 ]
adcx r11, [ rsp + 0x160 ]
adox r10, r12
mov r12, [ rsp + 0xe0 ]
mov [ rsp + 0x190 ], rax
movzx rax, byte [ rsp + 0x158 ]
adcx rax, r12
adox rcx, rdx
adox r9, r11
setc r12b
clc
adcx rbp, [ rsp + 0x30 ]
adox r13, rax
mov rdx, [ rsi + 0x20 ]
mulx rax, r11, [ rsi + 0x28 ]
adcx r15, [ rsp + 0x68 ]
movzx rdx, r12b
mov [ rsp + 0x198 ], r15
mov r15, 0x0 
adox rdx, r15
dec r15
movzx r14, r14b
adox r14, r15
adox rdi, r11
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r12, rdx
adox rbx, rax
adcx r8, [ rsp + 0x78 ]
adcx r10, [ rsp + 0x80 ]
adcx rcx, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, rax, [ rsi + 0x20 ]
adcx r9, [ rsp + 0x140 ]
adcx r13, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x1a0 ], rbx
mov [ rsp + 0x1a8 ], rdi
mulx rdi, rbx, [ rsi + 0x28 ]
adox rbx, [ rsp + 0x190 ]
adcx r14, [ rsp + 0x148 ]
seto dl
mov [ rsp + 0x1b0 ], rbx
movzx rbx, byte [ rsp + 0x108 ]
mov [ rsp + 0x1b8 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
adox rbx, r14
adox r12, [ rsp + 0xa0 ]
adox rax, r11
adox r15, [ rsp - 0x30 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, rbp
mulx r14, r11, rbx
mov rbx, r11
mov [ rsp + 0x1c0 ], r15
seto r15b
mov [ rsp + 0x1c8 ], rax
mov rax, -0x2 
inc rax
adox rbx, r14
movzx rax, bpl
lea rax, [ rax + rdi ]
mov rdi, r11
adox rdi, r14
mov rbp, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1d0 ], rax
mov byte [ rsp + 0x1d8 ], r15b
mulx r15, rax, rbp
adox rax, r14
setc r14b
clc
adcx r11, rdx
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x1e0 ], r12
mulx r12, rbp, r11
adcx rbx, [ rsp + 0x198 ]
mov r11, 0x6cfc5fd681c52056 
mov byte [ rsp + 0x1e8 ], r14b
mov [ rsp + 0x1f0 ], r13
mulx r13, r14, r11
adox rbp, r15
adcx rdi, r8
adcx rax, r10
adcx rbp, rcx
adox r14, r12
adcx r14, r9
setc r8b
clc
adcx rbx, [ rsp - 0x38 ]
xchg rdx, r11
mulx rcx, r10, rbx
adcx rdi, [ rsp - 0x40 ]
mov r9, 0x7bc65c783158aea3 
mov rdx, r9
mulx r15, r9, rbx
adcx rax, [ rsp + 0x28 ]
adcx rbp, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x8 ]
mov r12, 0xffffffffffffffff 
mov rdx, r12
mov [ rsp + 0x1f8 ], r14
mulx r14, r12, rbx
mov rdx, r12
mov [ rsp + 0x200 ], rbp
setc bpl
clc
adcx rdx, r14
mov byte [ rsp + 0x208 ], bpl
mov rbp, r12
adcx rbp, r14
mov [ rsp + 0x210 ], rbp
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, rbx
mov [ rsp + 0x218 ], rax
mov [ rsp + 0x220 ], rbx
mulx rbx, rax, rbp
adcx rax, r14
adcx r9, rbx
adcx r10, r15
mov r15, 0x2341f27177344 
mulx rbx, r14, r15
adcx r14, rcx
xchg rdx, r11
mulx rbp, rcx, r15
adox rcx, r13
mov rdx, 0x0 
adox rbp, rdx
adc rbx, 0x0
add r8b, 0xFF
adcx rcx, [ rsp + 0x1f0 ]
adcx rbp, [ rsp + 0x1b8 ]
movzx r13, byte [ rsp + 0x1e8 ]
adc r13, 0x0
add r12, r11
adcx rdi, [ rsp + 0x220 ]
mov r12, [ rsp + 0x218 ]
adcx r12, [ rsp + 0x210 ]
movzx r8, byte [ rsp + 0x208 ]
dec rdx
adox r8, rdx
adox rcx, [ rsp + 0x18 ]
adox rbp, [ rsp + 0x10 ]
adox r13, [ rsp + 0x60 ]
adcx rax, [ rsp + 0x200 ]
adcx r9, [ rsp + 0x1f8 ]
adcx r10, rcx
adcx r14, rbp
adcx rbx, r13
setc r11b
clc
adcx rdi, [ rsp + 0x90 ]
adcx r12, [ rsp + 0xc8 ]
movzx r8, r11b
mov rcx, 0x0 
adox r8, rcx
mov rbp, 0xfdc1767ae2ffffff 
mov rdx, rdi
mulx r13, rdi, rbp
mov r11, 0xffffffffffffffff 
mulx rbp, rcx, r11
mov r11, rcx
mov r15, -0x2 
inc r15
adox r11, rbp
adcx rax, [ rsp + 0xc0 ]
mov r15, rcx
adox r15, rbp
adcx r9, [ rsp + 0xd8 ]
adcx r10, [ rsp + 0x1e0 ]
mov [ rsp + 0x228 ], r10
movzx r10, byte [ rsp + 0x1d8 ]
mov [ rsp + 0x230 ], r13
mov r13, [ rsp - 0x48 ]
lea r10, [ r10 + r13 ]
adcx r14, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x1c0 ]
adcx r10, r8
setc r13b
clc
adcx rcx, rdx
adcx r11, r12
adox rdi, rbp
adcx r15, rax
adcx rdi, r9
mov rcx, 0x7bc65c783158aea3 
mulx r8, r12, rcx
adox r12, [ rsp + 0x230 ]
adcx r12, [ rsp + 0x228 ]
mov rbp, 0x6cfc5fd681c52056 
mulx r9, rax, rbp
adox rax, r8
adcx rax, r14
mov r14, 0x2341f27177344 
mulx rbp, r8, r14
adox r8, r9
seto dl
mov r9, -0x2 
inc r9
adox r11, [ rsp + 0x170 ]
movzx r9, dl
lea r9, [ r9 + rbp ]
adcx r8, rbx
adox r15, [ rsp + 0x178 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r11
mulx rbp, r11, rbx
adox rdi, [ rsp + 0x180 ]
adcx r9, r10
adox r12, [ rsp + 0x188 ]
adox rax, [ rsp + 0x1a8 ]
adox r8, [ rsp + 0x1a0 ]
adox r9, [ rsp + 0x1b0 ]
movzx r10, r13b
mov rbx, 0x0 
adcx r10, rbx
mov r13, r11
clc
adcx r13, rbp
adox r10, [ rsp + 0x1d0 ]
mov rbx, r11
adcx rbx, rbp
seto cl
mov r14, -0x2 
inc r14
adox r11, rdx
adox r13, r15
adox rbx, rdi
mov r11, 0xfdc1767ae2ffffff 
mulx rdi, r15, r11
adcx r15, rbp
mov rbp, 0x7bc65c783158aea3 
mulx r11, r14, rbp
adcx r14, rdi
adox r15, r12
adox r14, rax
mov r12, 0x6cfc5fd681c52056 
mulx rdi, rax, r12
adcx rax, r11
adox rax, r8
mov r8, 0x2341f27177344 
mulx r12, r11, r8
adcx r11, rdi
mov rdx, 0x0 
adcx r12, rdx
adox r11, r9
adox r12, r10
movzx r9, cl
adox r9, rdx
xor rcx, rcx
adox r13, [ rsp + 0xf0 ]
adox rbx, [ rsp + 0x100 ]
adox r15, [ rsp + 0xf8 ]
adox r14, [ rsp + 0x128 ]
adox rax, [ rsp + 0x120 ]
adox r11, [ rsp + 0x118 ]
adox r12, [ rsp + 0x130 ]
mov rdx, r13
mulx r10, r13, r8
mulx rcx, rdi, rbp
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x238 ], r12
mulx r12, r8, rbp
adox r9, [ rsp + 0x138 ]
mov rbp, r8
adcx rbp, rdx
mov rbp, r8
mov [ rsp + 0x240 ], r9
seto r9b
mov [ rsp + 0x248 ], r10
mov r10, -0x2 
inc r10
adox rbp, r12
adcx rbp, rbx
adox r8, r12
adcx r8, r15
mov rbx, 0xfdc1767ae2ffffff 
mulx r10, r15, rbx
adox r15, r12
adcx r15, r14
adox rdi, r10
adcx rdi, rax
mov r14, 0x6cfc5fd681c52056 
mulx r12, rax, r14
adox rax, rcx
adcx rax, r11
adox r13, r12
mov rdx, [ rsp + 0x248 ]
mov r11, 0x0 
adox rdx, r11
adcx r13, [ rsp + 0x238 ]
adcx rdx, [ rsp + 0x240 ]
movzx rcx, r9b
adc rcx, 0x0
mov r9, rbp
mov r10, 0xffffffffffffffff 
sub r9, r10
mov r12, r8
sbb r12, r10
mov r11, r15
sbb r11, r10
mov r14, rdi
sbb r14, rbx
mov rbx, rax
mov r10, 0x7bc65c783158aea3 
sbb rbx, r10
mov r10, r13
mov [ rsp + 0x250 ], r12
mov r12, 0x6cfc5fd681c52056 
sbb r10, r12
mov r12, rdx
mov [ rsp + 0x258 ], r10
mov r10, 0x2341f27177344 
sbb r12, r10
sbb rcx, 0x00000000
cmovc rbx, rax
cmovc r12, rdx
cmovc r14, rdi
cmovc r9, rbp
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], r9
mov [ rcx + 0x18 ], r14
cmovc r11, r15
mov [ rcx + 0x10 ], r11
mov rbp, [ rsp + 0x258 ]
cmovc rbp, r13
mov [ rcx + 0x28 ], rbp
mov r15, [ rsp + 0x250 ]
cmovc r15, r8
mov [ rcx + 0x8 ], r15
mov [ rcx + 0x20 ], rbx
mov [ rcx + 0x30 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 736
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7842
; seed 2603838727596525 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12339975 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=27, initial num_batches=31): 228338 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018503927277000155
; number reverted permutation / tried permutation: 71745 / 90316 =79.438%
; number reverted decision / tried decision: 63510 / 89683 =70.816%
; validated in 374.741s
