SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 600
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx rcx, r11, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
add rdi, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], rbx
mulx rbx, r15, rax
mov rdx, r15
mov [ rsp - 0x38 ], r8
mov r8, -0x2 
inc r8
adox rdx, rbx
mov r8, r15
adox r8, rbx
adox r11, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r14
mulx r14, rdi, [ rsi + 0x18 ]
mov rdx, 0x7bc65c783158aea3 
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r8
mulx r8, r11, rax
adox r11, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r11
mulx r11, rcx, rdx
adcx rcx, r12
adcx rdi, r11
mov rdx, [ rsi + 0x20 ]
mulx r11, r12, [ rsi + 0x10 ]
adcx r12, r14
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp - 0x8 ], r12
mulx r12, r14, rax
mov rdx, 0x2341f27177344 
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], rcx
mulx rcx, rdi, rax
adox r14, r8
adox rdi, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, r8, [ rsi + 0x10 ]
adcx r8, r11
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r8
mulx r8, r11, [ rsi + 0x10 ]
adcx r11, r12
adc r8, 0x0
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r8
mulx r8, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], rcx
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rdi
mov [ rsp + 0x38 ], r14
mulx r14, rdi, [ rsi + 0x30 ]
test al, al
adox r12, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], rdi
mulx rdi, r13, [ rsi + 0x30 ]
adox r11, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], r11
mulx r11, r8, [ rsi + 0x18 ]
adox r8, rcx
adcx r13, r14
mov rdx, [ rsi + 0x28 ]
mulx r14, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], r8
mulx r8, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], r14
mulx r14, r12, [ rsi + 0x10 ]
adox rcx, r11
seto dl
mov r11, -0x2 
inc r11
adox r13, rbp
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x70 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], r13
mov byte [ rsp + 0x80 ], bpl
mulx rbp, r13, [ rsi + 0x18 ]
adox r11, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r11
mulx r11, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], r11
mov [ rsp + 0x98 ], r14
mulx r14, r11, [ rsi + 0x10 ]
adox r13, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], r13
mulx r13, rcx, rdx
adox rcx, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rcx
mulx rcx, rbp, rdx
adcx r11, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r11
mulx r11, rdi, [ rsi + 0x10 ]
adcx r8, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xb8 ], r8
mulx r8, r14, [ rsi + 0x0 ]
setc dl
clc
adcx rbp, r8
mov r8b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xc0 ], r11
mov [ rsp + 0xc8 ], r13
mulx r13, r11, [ rsi + 0x18 ]
adcx r12, rcx
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0xd0 ], r8b
mulx r8, rcx, [ rsi + 0x0 ]
setc dl
clc
adcx r11, r9
adcx rdi, r13
setc r9b
clc
adcx r15, rax
seto r15b
mov rax, -0x2 
inc rax
adox rcx, r10
adcx rbx, rcx
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mulx rcx, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rdi
mulx rdi, rax, [ rsi + 0x18 ]
adox r13, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], r11
mulx r11, r8, [ rsi + 0x20 ]
adox rax, rcx
adox r8, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rsi + 0x18 ]
adcx r13, [ rsp - 0x18 ]
adcx rax, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0xe8 ], r9b
mov byte [ rsp + 0xf0 ], r15b
mulx r15, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], r15
mov [ rsp + 0x100 ], r12
mulx r12, r15, [ rsi + 0x20 ]
adcx r8, [ rsp - 0x10 ]
adox r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], r9
mulx r9, r11, [ rsi + 0x30 ]
setc dl
clc
mov [ rsp + 0x110 ], r8
mov r8, -0x1 
movzx r10, r10b
adcx r10, r8
adcx rcx, [ rsp + 0x98 ]
adcx r15, rdi
mov r10b, dl
mov rdx, [ rsi + 0x8 ]
mulx r8, rdi, [ rsi + 0x28 ]
adcx rdi, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, r12, [ rsi + 0x30 ]
adcx r11, r8
setc dl
clc
adcx r14, rbx
adcx rbp, r13
adcx rax, [ rsp + 0x100 ]
movzx rbx, dl
lea rbx, [ rbx + r9 ]
adox r12, [ rsp + 0xf8 ]
mov rdx, [ rsi + 0x30 ]
mulx r9, r13, [ rsi + 0x28 ]
adcx rcx, [ rsp + 0x110 ]
mov rdx, 0x0 
adox rdi, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x120 ], rcx
mulx rcx, r8, rdx
movzx rdx, byte [ rsp + 0x80 ]
mov [ rsp + 0x128 ], rax
mov rax, 0x0 
dec rax
adox rdx, rax
adox r8, [ rsp + 0x68 ]
adox r13, rcx
mov rdx, [ rsp + 0x108 ]
seto cl
inc rax
mov rax, -0x1 
movzx r10, r10b
adox r10, rax
adox rdx, [ rsp + 0x38 ]
adox r12, [ rsp + 0x30 ]
movzx r10, cl
lea r10, [ r10 + r9 ]
adcx r15, rdx
adcx r12, [ rsp + 0x118 ]
adox rdi, [ rsp + 0x28 ]
adcx r11, rdi
setc r9b
movzx r9, r9b
adox r9, rbx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbx, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mulx rax, rdi, [ rsi + 0x28 ]
movzx rdx, byte [ rsp + 0xf0 ]
clc
mov [ rsp + 0x130 ], r10
mov r10, -0x1 
adcx rdx, r10
adcx rdi, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], r13
mulx r13, r10, [ rsi + 0x20 ]
adcx r10, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], r8
mulx r8, rax, rdx
setc dl
mov [ rsp + 0x148 ], r10
movzx r10, byte [ rsp + 0xe8 ]
clc
mov [ rsp + 0x150 ], rdi
mov rdi, -0x1 
adcx r10, rdi
adcx rax, [ rsp + 0xc0 ]
mov r10b, dl
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x158 ], rax
mulx rax, rdi, [ rsi + 0x30 ]
movzx rdx, r10b
lea rdx, [ rdx + r13 ]
seto r13b
movzx r10, byte [ rsp + 0xd0 ]
mov [ rsp + 0x160 ], rdx
mov rdx, 0x0 
dec rdx
adox r10, rdx
adox rbx, [ rsp + 0x90 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x168 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
adcx r10, r8
adox rdi, rcx
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rsi + 0x18 ]
adcx rcx, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x170 ], rdi
mulx rdi, rbx, [ rsi + 0x30 ]
adcx rbx, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x178 ], rbx
mulx rbx, r8, rdx
adox r8, rax
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x180 ], r8
mulx r8, rax, r14
mov rdx, 0x0 
adcx rdi, rdx
mov [ rsp + 0x188 ], rdi
mov rdi, rax
clc
adcx rdi, r14
mov rdi, rax
mov [ rsp + 0x190 ], rcx
seto cl
mov [ rsp + 0x198 ], r10
mov r10, -0x3 
inc r10
adox rdi, r8
adox rax, r8
movzx rdx, cl
lea rdx, [ rdx + rbx ]
mov rbx, 0x7bc65c783158aea3 
xchg rdx, rbx
mulx r10, rcx, r14
adcx rdi, rbp
adcx rax, [ rsp + 0x128 ]
mov rbp, 0xfdc1767ae2ffffff 
mov rdx, r14
mov [ rsp + 0x1a0 ], rbx
mulx rbx, r14, rbp
adox r14, r8
adox rcx, rbx
adcx r14, [ rsp + 0x120 ]
adcx rcx, r15
mov r15, 0x6cfc5fd681c52056 
mulx rbx, r8, r15
adox r8, r10
adcx r8, r12
mov r12, 0x2341f27177344 
mulx rbp, r10, r12
adox r10, rbx
mov rdx, 0x0 
adox rbp, rdx
adcx r10, r11
mov r11, -0x3 
inc r11
adox rdi, [ rsp - 0x28 ]
mov rbx, 0xffffffffffffffff 
mov rdx, rdi
mulx r11, rdi, rbx
adox rax, [ rsp - 0x30 ]
adox r14, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x0 ]
adox r8, [ rsp - 0x8 ]
adox r10, [ rsp + 0x10 ]
adcx rbp, r9
adox rbp, [ rsp + 0x20 ]
movzx r9, r13b
mov r12, 0x0 
adcx r9, r12
adox r9, [ rsp + 0x18 ]
mov r13, rdi
clc
adcx r13, r11
mov r12, 0xfdc1767ae2ffffff 
mulx rbx, r15, r12
mov r12, 0x7bc65c783158aea3 
mov [ rsp + 0x1a8 ], r9
mov [ rsp + 0x1b0 ], rbp
mulx rbp, r9, r12
mov r12, rdi
adcx r12, r11
adcx r15, r11
adcx r9, rbx
mov r11, 0x6cfc5fd681c52056 
mov [ rsp + 0x1b8 ], r10
mulx r10, rbx, r11
adcx rbx, rbp
seto bpl
mov r11, -0x2 
inc r11
adox rdi, rdx
adox r13, rax
adox r12, r14
mov rdi, 0x2341f27177344 
mulx r14, rax, rdi
adox r15, rcx
adox r9, r8
adcx rax, r10
adox rbx, [ rsp + 0x1b8 ]
adox rax, [ rsp + 0x1b0 ]
setc dl
clc
adcx r13, [ rsp - 0x38 ]
adcx r12, [ rsp + 0xe0 ]
mov rcx, 0xffffffffffffffff 
xchg rdx, r13
mulx r10, r8, rcx
movzx r11, r13b
lea r11, [ r11 + r14 ]
adcx r15, [ rsp + 0xd8 ]
adcx r9, [ rsp + 0x158 ]
adox r11, [ rsp + 0x1a8 ]
adcx rbx, [ rsp + 0x198 ]
adcx rax, [ rsp + 0x190 ]
adcx r11, [ rsp + 0x178 ]
movzx r14, bpl
mov r13, 0x0 
adox r14, r13
mov rbp, r8
mov rdi, -0x3 
inc rdi
adox rbp, r10
mov r13, r8
adox r13, r10
adcx r14, [ rsp + 0x188 ]
setc dil
clc
adcx r8, rdx
adcx rbp, r12
adcx r13, r15
mov r8, 0xfdc1767ae2ffffff 
mulx r15, r12, r8
adox r12, r10
adcx r12, r9
mov r10, 0x7bc65c783158aea3 
mulx r8, r9, r10
adox r9, r15
adcx r9, rbx
mov rbx, 0x6cfc5fd681c52056 
mulx r10, r15, rbx
adox r15, r8
mov r8, 0x2341f27177344 
mulx rcx, rbx, r8
adox rbx, r10
mov rdx, 0x0 
adox rcx, rdx
mov r10, -0x3 
inc r10
adox rbp, [ rsp - 0x40 ]
adox r13, [ rsp + 0x78 ]
adox r12, [ rsp + 0x88 ]
adcx r15, rax
adox r9, [ rsp + 0xa0 ]
adcx rbx, r11
adox r15, [ rsp + 0xa8 ]
adox rbx, [ rsp + 0x150 ]
adcx rcx, r14
movzx rax, dil
adcx rax, rdx
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rdi, r11, rbp
mov r14, r11
clc
adcx r14, rdi
mov r10, r11
adcx r10, rdi
adox rcx, [ rsp + 0x148 ]
adox rax, [ rsp + 0x160 ]
seto r8b
mov rdx, -0x2 
inc rdx
adox r11, rbp
adox r14, r13
adox r10, r12
mov r11, 0xfdc1767ae2ffffff 
mov rdx, r11
mulx r13, r11, rbp
adcx r11, rdi
adox r11, r9
mov r12, 0x7bc65c783158aea3 
mov rdx, r12
mulx r9, r12, rbp
adcx r12, r13
adox r12, r15
mov r15, 0x6cfc5fd681c52056 
mov rdx, r15
mulx rdi, r15, rbp
adcx r15, r9
adox r15, rbx
mov rbx, 0x2341f27177344 
mov rdx, rbx
mulx r13, rbx, rbp
adcx rbx, rdi
mov rbp, 0x0 
adcx r13, rbp
adox rbx, rcx
adox r13, rax
movzx rcx, r8b
adox rcx, rbp
add r14, [ rsp - 0x48 ]
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx rax, r8, r14
mov r9, 0x7bc65c783158aea3 
mov rdx, r14
mulx rdi, r14, r9
adcx r10, [ rsp + 0x60 ]
adcx r11, [ rsp + 0x48 ]
adcx r12, [ rsp + 0x58 ]
adcx r15, [ rsp + 0x70 ]
adcx rbx, [ rsp + 0x140 ]
mov r9, r8
mov [ rsp + 0x1c0 ], rbx
mov rbx, -0x3 
inc rbx
adox r9, rax
adcx r13, [ rsp + 0x138 ]
mov rbp, r8
adox rbp, rax
adcx rcx, [ rsp + 0x130 ]
setc bl
clc
adcx r8, rdx
adcx r9, r10
adcx rbp, r11
mov r8, 0xfdc1767ae2ffffff 
mulx r11, r10, r8
adox r10, rax
adcx r10, r12
adox r14, r11
adcx r14, r15
mov rax, 0x6cfc5fd681c52056 
mulx r15, r12, rax
adox r12, rdi
adcx r12, [ rsp + 0x1c0 ]
mov rdi, 0x2341f27177344 
mulx rax, r11, rdi
adox r11, r15
mov rdx, 0x0 
adox rax, rdx
adcx r11, r13
mov r13, -0x3 
inc r13
adox r9, [ rsp + 0x40 ]
adox rbp, [ rsp + 0x50 ]
adox r10, [ rsp + 0xb0 ]
adox r14, [ rsp + 0xb8 ]
adcx rax, rcx
adox r12, [ rsp + 0x168 ]
movzx rcx, bl
adcx rcx, rdx
mov rbx, 0xffffffffffffffff 
mov rdx, r9
mulx r15, r9, rbx
mov r13, r9
clc
adcx r13, r15
mov rdi, r9
adcx rdi, r15
setc r8b
clc
adcx r9, rdx
adcx r13, rbp
mov r9, 0xfdc1767ae2ffffff 
mulx rbx, rbp, r9
adox r11, [ rsp + 0x170 ]
adox rax, [ rsp + 0x180 ]
adcx rdi, r10
adox rcx, [ rsp + 0x1a0 ]
seto r10b
mov r9, 0x0 
dec r9
movzx r8, r8b
adox r8, r9
adox r15, rbp
mov r8, 0x6cfc5fd681c52056 
mulx r9, rbp, r8
mov r8, 0x7bc65c783158aea3 
mov [ rsp + 0x1c8 ], rdi
mov [ rsp + 0x1d0 ], r13
mulx r13, rdi, r8
adox rdi, rbx
adcx r15, r14
adox rbp, r13
adcx rdi, r12
adcx rbp, r11
mov r14, 0x2341f27177344 
mulx rbx, r12, r14
adox r12, r9
mov rdx, 0x0 
adox rbx, rdx
adcx r12, rax
adcx rbx, rcx
movzx r11, r10b
adc r11, 0x0
mov rax, [ rsp + 0x1d0 ]
mov r10, 0xffffffffffffffff 
sub rax, r10
mov rcx, [ rsp + 0x1c8 ]
sbb rcx, r10
mov r9, r15
sbb r9, r10
mov r13, rdi
mov rdx, 0xfdc1767ae2ffffff 
sbb r13, rdx
mov r14, rbp
sbb r14, r8
mov rdx, r12
mov r8, 0x6cfc5fd681c52056 
sbb rdx, r8
mov r8, rbx
mov r10, 0x2341f27177344 
sbb r8, r10
sbb r11, 0x00000000
cmovc rax, [ rsp + 0x1d0 ]
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], rax
cmovc r14, rbp
cmovc r13, rdi
cmovc r9, r15
mov [ r11 + 0x18 ], r13
cmovc r8, rbx
mov [ r11 + 0x30 ], r8
cmovc rdx, r12
mov [ r11 + 0x28 ], rdx
cmovc rcx, [ rsp + 0x1c8 ]
mov [ r11 + 0x10 ], r9
mov [ r11 + 0x8 ], rcx
mov [ r11 + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.8491
; seed 0642340246791781 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7819735 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=27, initial num_batches=31): 146822 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.018775828081130628
; number reverted permutation / tried permutation: 73050 / 89970 =81.194%
; number reverted decision / tried decision: 63969 / 90029 =71.054%
; validated in 392.55s
