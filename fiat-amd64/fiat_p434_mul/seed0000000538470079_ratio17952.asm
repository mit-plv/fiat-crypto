SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 720
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], rdi
mulx rdi, rcx, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r12
mulx r12, rdi, r10
test al, al
adox rcx, r11
mov r11, rdi
adcx r11, r10
mov r11, rdi
setc dl
clc
adcx r11, r12
adcx rdi, r12
mov [ rsp - 0x28 ], rdi
seto dil
mov [ rsp - 0x20 ], r14
mov r14, 0x0 
dec r14
movzx rdx, dl
adox rdx, r14
adox rcx, r11
setc dl
clc
adcx rbp, rcx
mov r11b, dl
mov rdx, [ rax + 0x0 ]
mulx r14, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], rcx
mov byte [ rsp - 0x10 ], dil
mulx rdi, rcx, [ rax + 0x8 ]
setc dl
clc
adcx rcx, r8
mov r8b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r13
mulx r13, rcx, [ rax + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x8 ], r8b
mov [ rsp + 0x10 ], r13
mulx r13, r8, [ rax + 0x20 ]
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x18 ], rcx
mov [ rsp + 0x20 ], r14
mulx r14, rcx, rbp
adcx r9, rdi
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r9
mulx r9, rdi, [ rsi + 0x20 ]
adcx rdi, rbx
adcx r8, r9
mov rdx, [ rax + 0x28 ]
mulx r9, rbx, [ rsi + 0x20 ]
adcx rbx, r13
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r13, [ rsi + 0x20 ]
adcx r13, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x38 ], r13
mulx r13, r9, r10
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], rdi
mulx rdi, r8, r10
seto dl
mov [ rsp + 0x50 ], r14
mov r14, 0x0 
dec r14
movzx r11, r11b
adox r11, r14
adox r12, r9
adox r8, r13
mov r11, 0x0 
adcx rbx, r11
mov r9, 0x6cfc5fd681c52056 
xchg rdx, r9
mulx r11, r13, r10
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x58 ], rbx
mulx rbx, r14, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], r8
mov [ rsp + 0x68 ], r12
mulx r12, r8, [ rsi + 0x28 ]
adox r13, rdi
mov rdx, 0x2341f27177344 
mov [ rsp + 0x70 ], r13
mulx r13, rdi, r10
adox rdi, r11
mov rdx, [ rsi + 0x28 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x78 ], r10
mov [ rsp + 0x80 ], rdi
mulx rdi, r10, [ rax + 0x18 ]
mov rdx, r14
clc
adcx rdx, rbp
setc dl
clc
adcx r8, r11
mov r11b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x88 ], r8
mov byte [ rsp + 0x90 ], r9b
mulx r9, r8, [ rax + 0x10 ]
mov rdx, r14
mov byte [ rsp + 0x98 ], r11b
seto r11b
mov [ rsp + 0xa0 ], rcx
mov rcx, -0x2 
inc rcx
adox rdx, rbx
adcx r8, r12
adox r14, rbx
adcx r10, r9
adcx r15, rdi
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa8 ], r15
mulx r15, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xb0 ], r10
mov [ rsp + 0xb8 ], r8
mulx r8, r10, [ rsi + 0x18 ]
setc dl
clc
adcx r10, r15
movzx r15, r11b
lea r15, [ r15 + r13 ]
adcx rdi, r8
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], rdi
mov [ rsp + 0xc8 ], r10
mulx r10, rdi, [ rax + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0xd0 ], rcx
mov [ rsp + 0xd8 ], r14
mulx r14, rcx, rbp
adcx rdi, r9
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xe0 ], rdi
mulx rdi, r9, [ rsi + 0x18 ]
adox rbx, [ rsp + 0xa0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xe8 ], rbx
mov [ rsp + 0xf0 ], r12
mulx r12, rbx, [ rsi + 0x30 ]
adox rcx, [ rsp + 0x50 ]
adcx r9, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xf8 ], rbx
mulx rbx, r10, [ rsi + 0x30 ]
adcx r11, rdi
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x100 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x108 ], r9
mov [ rsp + 0x110 ], rcx
mulx rcx, r9, rbp
adcx rdi, r8
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x120 ], rcx
mov [ rsp + 0x128 ], r15
mulx r15, rcx, [ rax + 0x8 ]
setc dl
clc
adcx rcx, r12
adox r9, r14
mov r14b, dl
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x130 ], rcx
mulx rcx, r12, [ rsi + 0x10 ]
adcx r10, r15
adcx r8, rbx
mov rdx, [ rsi + 0x10 ]
mulx r15, rbx, [ rax + 0x18 ]
seto dl
mov [ rsp + 0x138 ], r8
mov r8, -0x2 
inc r8
adox r12, [ rsp + 0x20 ]
mov r8b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x140 ], r10
mov [ rsp + 0x148 ], r9
mulx r9, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x150 ], r12
mov byte [ rsp + 0x158 ], r8b
mulx r8, r12, [ rsi + 0x10 ]
adox r10, rcx
adox rbx, r9
adox r12, r15
adox r8, [ rsp + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, rcx, [ rax + 0x30 ]
movzx rdx, r14b
lea rdx, [ rdx + r11 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x160 ], r11
mov [ rsp + 0x168 ], r8
mulx r8, r11, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x170 ], r12
mov [ rsp + 0x178 ], rbx
mulx rbx, r12, [ rax + 0x28 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x180 ], r10
mov byte [ rsp + 0x188 ], r13b
mulx r13, r10, [ rsi + 0x8 ]
adcx r11, rdi
adcx r12, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rax + 0x30 ]
adox rdi, [ rsp - 0x20 ]
adcx rcx, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x190 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x198 ], r12
mov [ rsp + 0x1a0 ], r11
mulx r11, r12, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x1a8 ], rdi
mov rdi, -0x2 
inc rdi
adox r12, [ rsp - 0x30 ]
adox r14, r11
adox rbx, r9
mov r9b, dl
mov rdx, [ rax + 0x20 ]
mulx rdi, r11, [ rsi + 0x8 ]
movzx rdx, r9b
lea rdx, [ rdx + r8 ]
adox r11, rcx
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mulx rcx, r9, [ rax + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x1b0 ], r8
mov [ rsp + 0x1b8 ], r11
mulx r11, r8, [ rax + 0x28 ]
adox r10, rdi
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x1c0 ], r10
mulx r10, rdi, [ rsi + 0x8 ]
adox rdi, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x1c8 ], rdi
mulx rdi, r13, [ rax + 0x10 ]
mov rdx, 0x0 
adcx r15, rdx
adox r10, rdx
add byte [ rsp + 0x188 ], 0xFF
adcx r8, [ rsp - 0x40 ]
adcx r9, r11
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x1d0 ], r15
mulx r15, r11, [ rsi + 0x0 ]
adc rcx, 0x0
add byte [ rsp - 0x10 ], 0xFF
adcx r13, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x1d8 ], rcx
mov [ rsp + 0x1e0 ], r9
mulx r9, rcx, [ rsi + 0x0 ]
movzx rdx, byte [ rsp + 0x90 ]
mov [ rsp + 0x1e8 ], r8
mov r8, -0x1 
adox rdx, r8
adox r13, [ rsp - 0x28 ]
adcx rcx, rdi
adcx r11, r9
adcx r15, [ rsp + 0x18 ]
adox rcx, [ rsp + 0x68 ]
adox r11, [ rsp + 0x60 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, [ rax + 0x30 ]
adcx rdi, [ rsp + 0x10 ]
adox r15, [ rsp + 0x70 ]
adox rdi, [ rsp + 0x80 ]
mov rdx, 0x0 
adcx r9, rdx
adox r9, [ rsp + 0x128 ]
movzx rdx, byte [ rsp + 0x8 ]
clc
adcx rdx, r8
adcx r13, r12
adcx r14, rcx
adcx rbx, r11
adcx r15, [ rsp + 0x1b8 ]
adcx rdi, [ rsp + 0x1c0 ]
adcx r9, [ rsp + 0x1c8 ]
setc dl
movzx r12, byte [ rsp + 0x98 ]
clc
adcx r12, r8
adcx r13, [ rsp + 0xf0 ]
mov r12, 0x2341f27177344 
xchg rdx, r12
mulx r11, rcx, rbp
movzx rbp, r12b
adox rbp, r10
seto r10b
movzx r12, byte [ rsp + 0x158 ]
inc r8
mov r8, -0x1 
adox r12, r8
adox rcx, [ rsp + 0x120 ]
adcx r14, [ rsp + 0xd8 ]
adcx rbx, [ rsp + 0xe8 ]
adcx r15, [ rsp + 0x110 ]
seto r12b
inc r8
adox r13, [ rsp - 0x18 ]
adox r14, [ rsp + 0x150 ]
adcx rdi, [ rsp + 0x148 ]
adcx rcx, r9
adox rbx, [ rsp + 0x180 ]
adox r15, [ rsp + 0x178 ]
adox rdi, [ rsp + 0x170 ]
adox rcx, [ rsp + 0x168 ]
movzx r9, r12b
lea r9, [ r9 + r11 ]
adcx r9, rbp
movzx r11, r10b
adcx r11, r8
adox r9, [ rsp + 0x1a8 ]
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx rbp, r10, r13
mov r12, r10
clc
adcx r12, rbp
adox r11, [ rsp + 0x1b0 ]
mov rdx, r10
mov [ rsp + 0x1f0 ], r11
seto r11b
mov [ rsp + 0x1f8 ], r9
mov r9, -0x3 
inc r9
adox rdx, r13
adox r12, r14
adcx r10, rbp
adox r10, rbx
mov rdx, 0xfdc1767ae2ffffff 
mulx rbx, r14, r13
adcx r14, rbp
adox r14, r15
mov r15, 0x7bc65c783158aea3 
mov rdx, r15
mulx rbp, r15, r13
adcx r15, rbx
mov rbx, 0x6cfc5fd681c52056 
mov rdx, rbx
mulx r8, rbx, r13
adox r15, rdi
adcx rbx, rbp
adox rbx, rcx
mov rdi, 0x2341f27177344 
mov rdx, r13
mulx rcx, r13, rdi
adcx r13, r8
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r12, [ rsp + 0xd0 ]
adox r13, [ rsp + 0x1f8 ]
adcx r10, [ rsp + 0xc8 ]
adox rcx, [ rsp + 0x1f0 ]
adcx r14, [ rsp + 0xc0 ]
adcx r15, [ rsp + 0xe0 ]
adcx rbx, [ rsp + 0x108 ]
adcx r13, [ rsp + 0x100 ]
mov rdx, r12
mulx rbp, r12, rdi
movzx r8, r11b
mov r9, 0x0 
adox r8, r9
adcx rcx, [ rsp + 0x118 ]
mov r11, 0xffffffffffffffff 
mulx rdi, r9, r11
adcx r8, [ rsp + 0x160 ]
mov r11, r9
mov [ rsp + 0x200 ], r8
mov r8, -0x2 
inc r8
adox r11, rdx
mov r11, r9
setc r8b
clc
adcx r11, rdi
adox r11, r10
mov r10, 0xfdc1767ae2ffffff 
mov byte [ rsp + 0x208 ], r8b
mov [ rsp + 0x210 ], r11
mulx r11, r8, r10
adcx r9, rdi
adcx r8, rdi
adox r9, r14
adox r8, r15
mov r14, 0x7bc65c783158aea3 
mulx rdi, r15, r14
adcx r15, r11
adox r15, rbx
mov rbx, 0x6cfc5fd681c52056 
mulx r14, r11, rbx
adcx r11, rdi
adox r11, r13
adcx r12, r14
adox r12, rcx
mov rdx, 0x0 
adcx rbp, rdx
adox rbp, [ rsp + 0x200 ]
mov r13, [ rsp + 0x210 ]
clc
adcx r13, [ rsp - 0x48 ]
mov rcx, 0xffffffffffffffff 
mov rdx, r13
mulx rdi, r13, rcx
adcx r9, [ rsp - 0x8 ]
adcx r8, [ rsp + 0x28 ]
adcx r15, [ rsp + 0x48 ]
mulx r10, r14, rbx
adcx r11, [ rsp + 0x40 ]
adcx r12, [ rsp + 0x30 ]
movzx rcx, byte [ rsp + 0x208 ]
mov rbx, 0x0 
adox rcx, rbx
adcx rbp, [ rsp + 0x38 ]
mov [ rsp + 0x218 ], rbp
mov rbp, r13
mov [ rsp + 0x220 ], r10
mov r10, -0x3 
inc r10
adox rbp, rdi
mov rbx, r13
adox rbx, rdi
adcx rcx, [ rsp + 0x58 ]
setc r10b
clc
adcx r13, rdx
adcx rbp, r9
adcx rbx, r8
mov r13, 0xfdc1767ae2ffffff 
mulx r8, r9, r13
adox r9, rdi
adcx r9, r15
mov rdi, 0x7bc65c783158aea3 
mulx r13, r15, rdi
adox r15, r8
adcx r15, r11
mov r11, 0x2341f27177344 
mulx rdi, r8, r11
adox r14, r13
adcx r14, r12
adox r8, [ rsp + 0x220 ]
mov rdx, 0x0 
adox rdi, rdx
mov r12, -0x3 
inc r12
adox rbp, [ rsp + 0x78 ]
adox rbx, [ rsp + 0x88 ]
adox r9, [ rsp + 0xb8 ]
mov r13, 0xfdc1767ae2ffffff 
mov rdx, r13
mulx r12, r13, rbp
adox r15, [ rsp + 0xb0 ]
adcx r8, [ rsp + 0x218 ]
adox r14, [ rsp + 0xa8 ]
adox r8, [ rsp + 0x1e8 ]
adcx rdi, rcx
movzx rcx, r10b
mov rdx, 0x0 
adcx rcx, rdx
adox rdi, [ rsp + 0x1e0 ]
mov r10, 0xffffffffffffffff 
mov rdx, rbp
mulx r11, rbp, r10
adox rcx, [ rsp + 0x1d8 ]
mov r10, rbp
clc
adcx r10, rdx
mov r10, rbp
mov [ rsp + 0x228 ], rcx
setc cl
clc
adcx r10, r11
adcx rbp, r11
adcx r13, r11
seto r11b
mov [ rsp + 0x230 ], rdi
mov rdi, 0x0 
dec rdi
movzx rcx, cl
adox rcx, rdi
adox rbx, r10
adox rbp, r9
adox r13, r15
mov r9, 0x6cfc5fd681c52056 
mulx rcx, r15, r9
mov r10, 0x7bc65c783158aea3 
mulx r9, rdi, r10
adcx rdi, r12
adcx r15, r9
adox rdi, r14
adox r15, r8
mov r12, 0x2341f27177344 
mulx r8, r14, r12
adcx r14, rcx
adox r14, [ rsp + 0x230 ]
setc dl
clc
adcx rbx, [ rsp + 0xf8 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, rbx
mulx r10, r9, rcx
adcx rbp, [ rsp + 0x130 ]
adcx r13, [ rsp + 0x140 ]
adcx rdi, [ rsp + 0x138 ]
movzx rcx, bl
lea rcx, [ rcx + r8 ]
adox rcx, [ rsp + 0x228 ]
mov r8, r9
seto bl
mov r12, -0x2 
inc r12
adox r8, rdx
movzx r8, bl
movzx r11, r11b
lea r8, [ r8 + r11 ]
adcx r15, [ rsp + 0x1a0 ]
adcx r14, [ rsp + 0x198 ]
adcx rcx, [ rsp + 0x190 ]
adcx r8, [ rsp + 0x1d0 ]
mov r11, r9
setc bl
clc
adcx r11, r10
adcx r9, r10
adox r11, rbp
adox r9, r13
mov rbp, 0xfdc1767ae2ffffff 
mulx r12, r13, rbp
adcx r13, r10
adox r13, rdi
mov r10, 0x7bc65c783158aea3 
mulx rbp, rdi, r10
adcx rdi, r12
mov r12, 0x2341f27177344 
mov [ rsp + 0x238 ], r13
mulx r13, r10, r12
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x240 ], r9
mov [ rsp + 0x248 ], r11
mulx r11, r9, r12
adcx r9, rbp
adox rdi, r15
adcx r10, r11
adox r9, r14
adox r10, rcx
mov rdx, 0x0 
adcx r13, rdx
adox r13, r8
movzx r15, bl
adox r15, rdx
mov r14, [ rsp + 0x248 ]
mov rcx, 0xffffffffffffffff 
sub r14, rcx
mov rbx, [ rsp + 0x240 ]
sbb rbx, rcx
mov r8, [ rsp + 0x238 ]
sbb r8, rcx
mov rbp, rdi
mov r11, 0xfdc1767ae2ffffff 
sbb rbp, r11
mov rdx, r9
mov r11, 0x7bc65c783158aea3 
sbb rdx, r11
mov rcx, r10
sbb rcx, r12
mov r12, r13
mov r11, 0x2341f27177344 
sbb r12, r11
sbb r15, 0x00000000
cmovc rcx, r10
cmovc r8, [ rsp + 0x238 ]
cmovc rbx, [ rsp + 0x240 ]
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], rbx
cmovc r14, [ rsp + 0x248 ]
mov [ r15 + 0x0 ], r14
cmovc rdx, r9
cmovc r12, r13
mov [ r15 + 0x30 ], r12
mov [ r15 + 0x10 ], r8
mov [ r15 + 0x20 ], rdx
cmovc rbp, rdi
mov [ r15 + 0x28 ], rcx
mov [ r15 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 720
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7952
; seed 2371968699859548 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13231907 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=23, initial num_batches=31): 234513 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.01772329566705691
; number reverted permutation / tried permutation: 66711 / 90010 =74.115%
; number reverted decision / tried decision: 60850 / 89989 =67.619%
; validated in 440.154s
