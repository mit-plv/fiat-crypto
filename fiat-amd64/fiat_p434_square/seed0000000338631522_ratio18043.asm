SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 672
mov rdx, [ rsi + 0x30 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rbx
mulx rbx, r14, rdx
xor rdx, rdx
adox r14, rbp
adox r8, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rsi + 0x8 ]
adox rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rbp
mulx rbp, r9, rdx
adcx rax, r13
adcx rdi, r10
mov rdx, [ rsi + 0x20 ]
mulx r13, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], rax
mulx rax, rdi, [ rsi + 0x10 ]
adox r10, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x10 ], rbx
mov rbx, -0x2 
inc rbx
adox r11, r10
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r11
mulx r11, rbx, [ rsi + 0x30 ]
adox rdi, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rdi
mulx rdi, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r14
mulx r14, r8, rdx
adcx rbx, r12
adox r9, rax
seto dl
mov r12, -0x2 
inc r12
adox rcx, r15
mov r15b, dl
mov rdx, [ rsi + 0x30 ]
mulx r12, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
adcx rax, r11
adox r8, rdi
adox rbx, r14
mov rdx, [ rsi + 0x10 ]
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rax
mulx rax, r14, [ rsi + 0x28 ]
adox r11, r9
adox r14, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r14
mov [ rsp + 0x38 ], r11
mulx r11, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x50 ], rcx
mov rcx, -0x2 
inc rcx
adox rbx, rdi
mov dil, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rax
mulx rax, rcx, [ rsi + 0x10 ]
adox rcx, r8
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x60 ], dil
mulx rdi, r8, [ rsi + 0x28 ]
adox r14, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r14
mulx r14, rax, [ rsi + 0x20 ]
adox rax, r11
adox r8, r14
mov rdx, [ rsi + 0x30 ]
mulx r14, r11, [ rsi + 0x0 ]
adox r11, rdi
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x70 ], r11
mulx r11, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], rax
mulx rax, r8, [ rsi + 0x20 ]
mov rdx, 0x0 
adox r14, rdx
adcx rdi, r12
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x88 ], rdi
mulx rdi, r12, rdx
adcx r12, r11
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x90 ], r12
mulx r12, r11, [ rsi + 0x18 ]
adc rdi, 0x0
add r15b, 0xFF
adcx rbp, r8
adcx r11, rax
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], rdi
mulx rdi, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], r11
mulx r11, r15, [ rsi + 0x30 ]
adcx r15, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb0 ], r15
mulx r15, r12, [ rsi + 0x30 ]
adc r11, 0x0
add r10b, 0xFF
adcx r13, rax
mov rdx, [ rsi + 0x20 ]
mulx rax, r10, [ rsi + 0x8 ]
adox r10, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r10
mulx r10, r8, [ rsi + 0x20 ]
adcx r12, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], rbp
mov [ rsp + 0xd0 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
adox r8, rax
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r8
mulx r8, rax, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xe0 ], r15
mov [ rsp + 0xe8 ], r13
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf0 ], r15
mov [ rsp + 0xf8 ], r11
mulx r11, r15, [ rsi + 0x28 ]
clc
adcx r15, r13
adcx rbp, r11
adcx rax, r12
mov rdx, 0xffffffffffffffff 
mulx r13, r12, r9
adox rdi, r10
mov r10, r12
setc r11b
clc
adcx r10, r9
mov r10, 0x7bc65c783158aea3 
mov rdx, r9
mov [ rsp + 0x100 ], rax
mulx rax, r9, r10
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x108 ], rbp
mov [ rsp + 0x110 ], r15
mulx r15, rbp, r10
mov r10, r12
mov [ rsp + 0x118 ], rdi
seto dil
mov [ rsp + 0x120 ], r14
mov r14, -0x2 
inc r14
adox r10, r13
adox r12, r13
adox rbp, r13
adcx r10, rbx
adcx r12, rcx
adcx rbp, [ rsp + 0x68 ]
adox r9, r15
mov rbx, 0x6cfc5fd681c52056 
mulx r13, rcx, rbx
adox rcx, rax
adcx r9, [ rsp + 0x80 ]
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r15, [ rsi + 0x28 ]
adcx rcx, [ rsp + 0x78 ]
mov rdx, 0x2341f27177344 
mov byte [ rsp + 0x128 ], dil
mulx rdi, rbx, rax
adox rbx, r13
mov rax, 0x0 
adox rdi, rax
adcx rbx, [ rsp + 0x70 ]
dec rax
movzx r11, r11b
adox r11, rax
adox r8, r15
adcx rdi, [ rsp + 0x120 ]
setc r11b
clc
adcx r10, [ rsp - 0x38 ]
adcx r12, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x8 ]
adcx r9, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, r13, rdx
adox r13, r14
mov rdx, [ rsi + 0x30 ]
mulx rax, r14, [ rsi + 0x28 ]
adox r14, r15
adcx rcx, [ rsp - 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x130 ], r14
mulx r14, r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x138 ], r13
mov [ rsp + 0x140 ], r8
mulx r8, r13, [ rsi + 0x30 ]
mov rdx, r15
mov byte [ rsp + 0x148 ], r11b
seto r11b
mov [ rsp + 0x150 ], rdi
mov rdi, -0x2 
inc rdi
adox rdx, r14
mov rdi, r15
adox rdi, r14
mov [ rsp + 0x158 ], rbx
movzx rbx, r11b
lea rbx, [ rbx + rax ]
mov rax, 0xfdc1767ae2ffffff 
xchg rdx, rax
mov [ rsp + 0x160 ], rbx
mulx rbx, r11, r10
adox r11, r14
setc r14b
clc
adcx r15, r10
adcx rax, r12
adcx rdi, rbp
adcx r11, r9
setc r15b
movzx r12, byte [ rsp + 0x60 ]
clc
mov rbp, -0x1 
adcx r12, rbp
adcx r13, [ rsp + 0x58 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r12, rdx
mov rdx, 0x0 
adcx r8, rdx
movzx rdx, byte [ rsp + 0x128 ]
clc
adcx rdx, rbp
adcx r12, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x168 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
adcx rbp, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], rbp
mulx rbp, r9, [ rsi + 0x30 ]
adcx r9, r12
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x178 ], rbp
mulx rbp, r12, r10
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x180 ], r9
mov [ rsp + 0x188 ], r8
mulx r8, r9, r10
adox r12, rbx
adox r9, rbp
setc bl
clc
adcx rax, [ rsp - 0x40 ]
mov rbp, 0x7bc65c783158aea3 
mov rdx, rax
mov byte [ rsp + 0x190 ], bl
mulx rbx, rax, rbp
mov rbp, 0x2341f27177344 
xchg rdx, rbp
mov [ rsp + 0x198 ], r13
mov [ rsp + 0x1a0 ], r9
mulx r9, r13, r10
adox r13, r8
mov r10, 0x0 
adox r9, r10
adcx rdi, [ rsp + 0x50 ]
mov r8, 0xffffffffffffffff 
mov rdx, rbp
mulx r10, rbp, r8
mov r8, 0x0 
dec r8
movzx r15, r15b
adox r15, r8
adox rcx, r12
adcx r11, [ rsp + 0x48 ]
adcx rcx, [ rsp + 0x40 ]
mov r15, rbp
seto r12b
inc r8
adox r15, r10
mov r8, rbp
adox r8, r10
mov [ rsp + 0x1a8 ], r9
setc r9b
clc
adcx rbp, rdx
adcx r15, rdi
adcx r8, r11
mov rbp, 0xfdc1767ae2ffffff 
mulx r11, rdi, rbp
adox rdi, r10
adox rax, r11
mov r10, 0x6cfc5fd681c52056 
mulx rbp, r11, r10
adox r11, rbx
adcx rdi, rcx
mov rbx, 0x2341f27177344 
mulx r10, rcx, rbx
adox rcx, rbp
mov rdx, 0x0 
adox r10, rdx
mov rbp, [ rsp + 0x158 ]
dec rdx
movzx r14, r14b
adox r14, rdx
adox rbp, [ rsp + 0xe8 ]
setc r14b
clc
movzx r12, r12b
adcx r12, rdx
adcx rbp, [ rsp + 0x1a0 ]
mov r12, [ rsp + 0x150 ]
adox r12, [ rsp + 0xd0 ]
mov rdx, [ rsp + 0xe0 ]
movzx rbx, byte [ rsp + 0x148 ]
adox rbx, rdx
adcx r13, r12
adcx rbx, [ rsp + 0x1a8 ]
seto dl
adc dl, 0x0
movzx rdx, dl
add r9b, 0xFF
adcx rbp, [ rsp + 0x38 ]
mov r9, -0x1 
movzx r14, r14b
adox r14, r9
adox rbp, rax
adcx r13, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x198 ]
movzx rdx, dl
movzx rax, dl
adcx rax, [ rsp + 0x188 ]
adox r11, r13
adox rcx, rbx
setc r14b
clc
adcx r15, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x8 ]
mov r12, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, r12
adcx rdi, [ rsp + 0x0 ]
adcx rbp, [ rsp + 0x20 ]
adcx r11, [ rsp + 0xc8 ]
adcx rcx, [ rsp + 0xa8 ]
adox r10, rax
mov rbx, r15
seto al
inc r9
adox rbx, r13
adcx r10, [ rsp + 0xb0 ]
movzx r9, al
movzx r14, r14b
lea r9, [ r9 + r14 ]
adcx r9, [ rsp + 0xc0 ]
mov r14, 0xfdc1767ae2ffffff 
mulx r12, rax, r14
mov r14, r15
adox r14, r13
adox rax, r13
setc r13b
clc
adcx r15, rdx
adcx rbx, r8
adcx r14, rdi
adcx rax, rbp
mov r15, 0x7bc65c783158aea3 
mulx rdi, r8, r15
adox r8, r12
adcx r8, r11
mov rbp, 0x6cfc5fd681c52056 
mulx r12, r11, rbp
adox r11, rdi
adcx r11, rcx
mov rcx, 0x2341f27177344 
mulx rbp, rdi, rcx
adox rdi, r12
adcx rdi, r10
mov rdx, 0x0 
adox rbp, rdx
adcx rbp, r9
movzx r10, r13b
adc r10, 0x0
test al, al
adox rbx, [ rsp + 0xa0 ]
adox r14, [ rsp + 0xb8 ]
adox rax, [ rsp + 0xd8 ]
adox r8, [ rsp + 0x118 ]
adox r11, [ rsp + 0x168 ]
adox rdi, [ rsp + 0x170 ]
adox rbp, [ rsp + 0x180 ]
mov r13, 0xffffffffffffffff 
mov rdx, rbx
mulx r9, rbx, r13
mov r12, rbx
adcx r12, r9
movzx rcx, byte [ rsp + 0x190 ]
mov r15, [ rsp + 0x178 ]
lea rcx, [ rcx + r15 ]
adox rcx, r10
mov r15, rbx
adcx r15, r9
seto r10b
mov r13, -0x2 
inc r13
adox rbx, rdx
adox r12, r14
adox r15, rax
mov rbx, 0xfdc1767ae2ffffff 
mulx rax, r14, rbx
adcx r14, r9
mov r9, 0x7bc65c783158aea3 
mulx rbx, r13, r9
adcx r13, rax
adox r14, r8
adox r13, r11
mov r8, 0x6cfc5fd681c52056 
mulx rax, r11, r8
adcx r11, rbx
mov rbx, 0x2341f27177344 
mulx r9, r8, rbx
adcx r8, rax
adox r11, rdi
adox r8, rbp
mov rdx, 0x0 
adcx r9, rdx
adox r9, rcx
clc
adcx r12, [ rsp + 0xf0 ]
movzx rdi, r10b
adox rdi, rdx
adcx r15, [ rsp + 0x110 ]
mov rbp, 0xffffffffffffffff 
mov rdx, r12
mulx r10, r12, rbp
mov rcx, r12
mov rax, -0x2 
inc rax
adox rcx, rdx
adcx r14, [ rsp + 0x108 ]
mov rcx, 0x7bc65c783158aea3 
mulx rbx, rax, rcx
adcx r13, [ rsp + 0x100 ]
adcx r11, [ rsp + 0x140 ]
adcx r8, [ rsp + 0x138 ]
adcx r9, [ rsp + 0x130 ]
adcx rdi, [ rsp + 0x160 ]
mov rcx, r12
setc bpl
clc
adcx rcx, r10
adcx r12, r10
adox rcx, r15
setc r15b
clc
adcx rcx, [ rsp - 0x48 ]
mov byte [ rsp + 0x1b0 ], bpl
mov rbp, 0x6cfc5fd681c52056 
xchg rdx, rbp
mov [ rsp + 0x1b8 ], rdi
mov [ rsp + 0x1c0 ], r9
mulx r9, rdi, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x1c8 ], r8
mov [ rsp + 0x1d0 ], r11
mulx r11, r8, rcx
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x1d8 ], r13
mov [ rsp + 0x1e0 ], r9
mulx r9, r13, rcx
mov rdx, r8
mov [ rsp + 0x1e8 ], rdi
setc dil
clc
adcx rdx, r11
adox r12, r14
mov r14, r8
adcx r14, r11
mov [ rsp + 0x1f0 ], r14
mov r14, 0xfdc1767ae2ffffff 
xchg rdx, r14
mov [ rsp + 0x1f8 ], r14
mov [ rsp + 0x200 ], r12
mulx r12, r14, rcx
adcx r14, r11
mov [ rsp + 0x208 ], r14
mulx r14, r11, rbp
adcx r13, r12
seto r12b
mov rdx, 0x0 
dec rdx
movzx r15, r15b
adox r15, rdx
adox r10, r11
adox rax, r14
mov r15, 0x6cfc5fd681c52056 
mov rdx, r15
mulx r11, r15, rbp
adox r15, rbx
mov rbx, 0x2341f27177344 
mov rdx, rbx
mulx r14, rbx, rbp
adox rbx, r11
mulx r11, rbp, rcx
adcx r9, [ rsp + 0x1e8 ]
mov rdx, 0x0 
adox r14, rdx
adcx rbp, [ rsp + 0x1e0 ]
adc r11, 0x0
add r12b, 0xFF
adcx r10, [ rsp + 0x1d8 ]
adcx rax, [ rsp + 0x1d0 ]
mov r12, [ rsp + 0x200 ]
mov rdx, -0x1 
movzx rdi, dil
adox rdi, rdx
adox r12, [ rsp - 0x20 ]
adcx r15, [ rsp + 0x1c8 ]
adcx rbx, [ rsp + 0x1c0 ]
adox r10, [ rsp - 0x28 ]
adox rax, [ rsp + 0x18 ]
adcx r14, [ rsp + 0x1b8 ]
adox r15, [ rsp + 0x28 ]
setc dil
clc
adcx r8, rcx
adox rbx, [ rsp + 0x88 ]
adox r14, [ rsp + 0x90 ]
adcx r12, [ rsp + 0x1f8 ]
adcx r10, [ rsp + 0x1f0 ]
adcx rax, [ rsp + 0x208 ]
adcx r13, r15
adcx r9, rbx
adcx rbp, r14
movzx r8, dil
movzx rcx, byte [ rsp + 0x1b0 ]
lea r8, [ r8 + rcx ]
adox r8, [ rsp + 0x98 ]
adcx r11, r8
seto cl
adc cl, 0x0
movzx rcx, cl
mov rdi, r12
mov r15, 0xffffffffffffffff 
sub rdi, r15
mov rbx, r10
sbb rbx, r15
mov r14, rax
sbb r14, r15
mov r8, r13
mov rdx, 0xfdc1767ae2ffffff 
sbb r8, rdx
mov rdx, r9
mov r15, 0x7bc65c783158aea3 
sbb rdx, r15
mov r15, rbp
mov [ rsp + 0x210 ], r8
mov r8, 0x6cfc5fd681c52056 
sbb r15, r8
mov r8, r11
mov [ rsp + 0x218 ], r14
mov r14, 0x2341f27177344 
sbb r8, r14
movzx r14, cl
sbb r14, 0x00000000
cmovc rdi, r12
cmovc rbx, r10
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rdi
cmovc rdx, r9
mov [ r14 + 0x20 ], rdx
cmovc r15, rbp
mov r12, [ rsp + 0x218 ]
cmovc r12, rax
mov [ r14 + 0x28 ], r15
cmovc r8, r11
mov [ r14 + 0x30 ], r8
mov r10, [ rsp + 0x210 ]
cmovc r10, r13
mov [ r14 + 0x18 ], r10
mov [ r14 + 0x8 ], rbx
mov [ r14 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 672
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.8043
; seed 3067213906420741 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7768656 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=27, initial num_batches=31): 151975 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019562585857836927
; number reverted permutation / tried permutation: 74258 / 90466 =82.084%
; number reverted decision / tried decision: 63839 / 89533 =71.302%
; validated in 377.254s
