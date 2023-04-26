SECTION .text
	GLOBAL fiat_p434_mul
fiat_p434_mul:
sub rsp, 600
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rbx
mulx rbx, r13, [ rax + 0x10 ]
test al, al
adox rcx, r11
adox r13, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, [ rax + 0x8 ]
mov rdx, rbp
adcx rdx, r10
mov rdx, rbp
mov [ rsp - 0x38 ], rbx
seto bl
mov [ rsp - 0x30 ], r9
mov r9, -0x2 
inc r9
adox rdx, r12
adcx rdx, rcx
adox rbp, r12
adcx rbp, r13
seto cl
inc r9
adox r11, rdi
setc dil
clc
adcx r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, r13, [ rsi + 0x8 ]
adcx r11, rbp
adox r13, r8
mov rdx, [ rax + 0x0 ]
mulx rbp, r8, [ rsi + 0x18 ]
setc dl
clc
adcx r14, [ rsp - 0x30 ]
mov [ rsp - 0x28 ], r14
mov r14b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r11
mulx r11, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp - 0x10 ], r13
mov byte [ rsp - 0x8 ], r14b
mulx r14, r13, [ rax + 0x10 ]
adcx r13, [ rsp - 0x40 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x0 ], r13
mov byte [ rsp + 0x8 ], dil
mulx rdi, r13, [ rsi + 0x30 ]
adcx r8, r14
adcx r13, r11
mov rdx, [ rax + 0x28 ]
mulx r14, r11, [ rsi + 0x30 ]
adcx r11, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r11
mulx r11, rdi, [ rax + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r8
mulx r8, r13, [ rax + 0x18 ]
adox r13, r9
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x28 ], r13
mulx r13, r9, r10
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x30 ], rbp
mov [ rsp + 0x38 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
adox rbp, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x40 ], rbp
mulx rbp, r8, [ rax + 0x28 ]
adox r8, r15
seto dl
mov r15, 0x0 
dec r15
movzx rcx, cl
adox rcx, r15
adox r12, r9
mov rcx, 0x7bc65c783158aea3 
xchg rdx, r10
mulx r15, r9, rcx
adox r9, r13
mov r13, 0x6cfc5fd681c52056 
mov [ rsp + 0x48 ], r8
mulx r8, rcx, r13
adox rcx, r15
mov r15, 0x2341f27177344 
mov [ rsp + 0x50 ], rcx
mulx rcx, r13, r15
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x58 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], r12
mov [ rsp + 0x68 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
adcx rdi, r14
adox r13, r8
mov rdx, 0x0 
adcx r11, rdx
adox rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r14, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x70 ], r11
mov [ rsp + 0x78 ], rdi
mulx rdi, r11, [ rax + 0x30 ]
add bl, 0xFF
adcx r12, [ rsp - 0x38 ]
adcx r14, rbp
adcx r15, r8
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x80 ], rcx
mulx rcx, r8, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], r15
mulx r15, r13, [ rsi + 0x28 ]
adcx r11, r9
adc rdi, 0x0
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x98 ], r13
mulx r13, r9, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], rdi
mov [ rsp + 0xa8 ], r11
mulx r11, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xb0 ], r14
mov [ rsp + 0xb8 ], r12
mulx r12, r14, [ rsi + 0x20 ]
test al, al
adox r9, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xc0 ], r9
mulx r9, r15, [ rsi + 0x20 ]
adox r8, r13
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xc8 ], r8
mulx r8, r13, [ rsi + 0x20 ]
adcx r15, r8
adcx rbx, r9
mov rdx, [ rsi + 0x20 ]
mulx r8, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], rbx
mov [ rsp + 0xd8 ], r15
mulx r15, rbx, [ rax + 0x20 ]
adcx r9, rbp
adcx r14, r8
mov rdx, [ rax + 0x28 ]
mulx r8, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], r14
mov [ rsp + 0xe8 ], r9
mulx r9, r14, [ rax + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf0 ], r13
mov byte [ rsp + 0xf8 ], r10b
mulx r10, r13, [ rax + 0x28 ]
adcx r13, r12
adcx r14, r10
adox rdi, rcx
mov rdx, 0xffffffffffffffff 
mulx r12, rcx, [ rsp + 0x38 ]
adox rbx, r11
mov r11, 0xfdc1767ae2ffffff 
mov rdx, [ rsp + 0x38 ]
mov [ rsp + 0x100 ], rbx
mulx rbx, r10, r11
mov r11, 0x7bc65c783158aea3 
mov [ rsp + 0x108 ], rdi
mov [ rsp + 0x110 ], r14
mulx r14, rdi, r11
mov r11, 0x0 
adcx r9, r11
mov [ rsp + 0x118 ], r9
mov r9, rcx
clc
adcx r9, r12
mov r11, rcx
adcx r11, r12
adcx r10, r12
adcx rdi, rbx
mov r12, 0x6cfc5fd681c52056 
mov [ rsp + 0x120 ], r13
mulx r13, rbx, r12
adcx rbx, r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], rbx
mulx rbx, r12, [ rax + 0x30 ]
mov rdx, 0x2341f27177344 
mov [ rsp + 0x130 ], rdi
mov [ rsp + 0x138 ], r10
mulx r10, rdi, r14
adcx rdi, r13
adox rbp, r15
mov rdx, [ rsi + 0x28 ]
mulx r13, r15, [ rax + 0x30 ]
adox r15, r8
mov rdx, 0x0 
adcx r10, rdx
adox r13, rdx
add byte [ rsp + 0xf8 ], 0x7F
adox r12, [ rsp + 0x68 ]
adox rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x140 ], r13
mulx r13, r8, [ rax + 0x8 ]
adcx r8, [ rsp + 0x30 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x148 ], r15
mov [ rsp + 0x150 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
adcx r15, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x158 ], r15
mulx r15, r13, [ rsi + 0x18 ]
adcx r13, rbp
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x160 ], r13
mulx r13, rbp, [ rsi + 0x18 ]
adcx rbp, r15
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x168 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
adcx r15, r13
mov rdx, [ rax + 0x30 ]
mov [ rsp + 0x170 ], r15
mulx r15, r13, [ rsi + 0x18 ]
adcx r13, rbp
adc r15, 0x0
mov rdx, [ rsp + 0xb8 ]
add byte [ rsp + 0x8 ], 0xFF
adcx rdx, [ rsp + 0x60 ]
movzx rbp, byte [ rsp - 0x8 ]
mov [ rsp + 0x178 ], r15
mov r15, -0x1 
adox rbp, r15
adox rdx, [ rsp - 0x10 ]
mov rbp, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0xb0 ]
mov r15, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x90 ]
mov [ rsp + 0x180 ], r13
mov r13, [ rsp + 0xa8 ]
adcx r13, [ rsp + 0x88 ]
mov [ rsp + 0x188 ], r8
mov r8, [ rsp + 0xa0 ]
adcx r8, [ rsp + 0x80 ]
mov [ rsp + 0x190 ], r10
setc r10b
clc
adcx rcx, r14
adox rbp, [ rsp + 0x28 ]
adcx r9, [ rsp - 0x18 ]
adox r15, [ rsp + 0x40 ]
adox r13, [ rsp + 0x48 ]
adox r12, r8
movzx rcx, r10b
adox rcx, rbx
adcx r11, rdx
adcx rbp, [ rsp + 0x138 ]
adcx r15, [ rsp + 0x130 ]
adcx r13, [ rsp + 0x128 ]
adcx rdi, r12
mov rdx, [ rax + 0x0 ]
mulx rbx, r14, [ rsi + 0x10 ]
adcx rcx, [ rsp + 0x190 ]
mov rdx, [ rax + 0x10 ]
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x198 ], rcx
mulx rcx, r12, [ rax + 0x8 ]
setc dl
clc
adcx r12, rbx
adcx r10, rcx
movzx rbx, dl
mov rcx, 0x0 
adox rbx, rcx
mov rdx, -0x3 
inc rdx
adox r14, r9
adox r12, r11
mov rdx, [ rax + 0x20 ]
mulx r11, r9, [ rsi + 0x10 ]
adox r10, rbp
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ rax + 0x18 ]
adcx rbp, r8
adox rbp, r15
adcx r9, rcx
adox r9, r13
mov rdx, [ rax + 0x28 ]
mulx r13, r15, [ rsi + 0x10 ]
adcx r15, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rax + 0x30 ]
adcx r8, r13
mov rdx, 0x0 
adcx r11, rdx
adox r15, rdi
adox r8, [ rsp + 0x198 ]
mov rdi, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, rdi
mov r13, r14
clc
adcx r13, rcx
adox r11, rbx
mov rbx, r14
seto dil
mov [ rsp + 0x1a0 ], r11
mov r11, -0x2 
inc r11
adox rbx, rdx
adox r13, r12
adcx r14, rcx
adox r14, r10
mov rbx, 0xfdc1767ae2ffffff 
mulx r10, r12, rbx
adcx r12, rcx
adox r12, rbp
mov rbp, 0x7bc65c783158aea3 
mulx r11, rcx, rbp
adcx rcx, r10
adox rcx, r9
mov r9, 0x6cfc5fd681c52056 
mulx rbp, r10, r9
adcx r10, r11
mov r11, 0x2341f27177344 
mulx rbx, r9, r11
adox r10, r15
adcx r9, rbp
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r13, [ rsp - 0x20 ]
adcx r14, [ rsp + 0x188 ]
adcx r12, [ rsp + 0x158 ]
adcx rcx, [ rsp + 0x160 ]
adcx r10, [ rsp + 0x168 ]
adox r9, r8
adcx r9, [ rsp + 0x170 ]
adox rbx, [ rsp + 0x1a0 ]
movzx r15, dil
adox r15, rdx
adcx rbx, [ rsp + 0x180 ]
adcx r15, [ rsp + 0x178 ]
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx rdi, r8, r13
mov rbp, r8
mov rdx, -0x2 
inc rdx
adox rbp, rdi
mov rdx, r8
adox rdx, rdi
setc r11b
clc
adcx r8, r13
adcx rbp, r14
adcx rdx, r12
mov r8, 0xfdc1767ae2ffffff 
xchg rdx, r8
mulx r12, r14, r13
adox r14, rdi
adcx r14, rcx
mov rcx, 0x7bc65c783158aea3 
mov rdx, rcx
mulx rdi, rcx, r13
adox rcx, r12
adcx rcx, r10
mov r10, 0x6cfc5fd681c52056 
mov rdx, r10
mulx r12, r10, r13
adox r10, rdi
adcx r10, r9
mov r9, 0x2341f27177344 
mov rdx, r9
mulx rdi, r9, r13
adox r9, r12
mov r13, 0x0 
adox rdi, r13
adcx r9, rbx
adcx rdi, r15
movzx rbx, r11b
adc rbx, 0x0
test al, al
adox rbp, [ rsp + 0xf0 ]
mov r11, 0xffffffffffffffff 
mov rdx, rbp
mulx r15, rbp, r11
adox r8, [ rsp + 0xd8 ]
adox r14, [ rsp + 0xd0 ]
mov r12, rbp
adcx r12, rdx
adox rcx, [ rsp + 0xe8 ]
adox r10, [ rsp + 0xe0 ]
adox r9, [ rsp + 0x120 ]
adox rdi, [ rsp + 0x110 ]
adox rbx, [ rsp + 0x118 ]
mov r12, rbp
seto r11b
mov [ rsp + 0x1a8 ], rbx
mov rbx, -0x3 
inc rbx
adox r12, r15
adox rbp, r15
adcx r12, r8
mov r8, 0xfdc1767ae2ffffff 
mulx rbx, r13, r8
adcx rbp, r14
adox r13, r15
adcx r13, rcx
mov r15, 0x7bc65c783158aea3 
mulx rcx, r14, r15
adox r14, rbx
adcx r14, r10
mov r10, 0x6cfc5fd681c52056 
mulx r15, rbx, r10
adox rbx, rcx
adcx rbx, r9
mov r9, 0x2341f27177344 
mulx r10, rcx, r9
adox rcx, r15
mov rdx, 0x0 
adox r10, rdx
adcx rcx, rdi
adcx r10, [ rsp + 0x1a8 ]
movzx rdi, r11b
adc rdi, 0x0
test al, al
adox r12, [ rsp + 0x98 ]
mov rdx, r12
mulx r11, r12, r8
mov r15, 0xffffffffffffffff 
mulx r8, r9, r15
mov r15, r9
adcx r15, r8
adox rbp, [ rsp + 0xc0 ]
adox r13, [ rsp + 0xc8 ]
adox r14, [ rsp + 0x108 ]
adox rbx, [ rsp + 0x100 ]
adox rcx, [ rsp + 0x150 ]
adox r10, [ rsp + 0x148 ]
mov [ rsp + 0x1b0 ], rdi
mov rdi, r9
adcx rdi, r8
adcx r12, r8
seto r8b
mov [ rsp + 0x1b8 ], r10
mov r10, -0x2 
inc r10
adox r9, rdx
adox r15, rbp
adox rdi, r13
adox r12, r14
mov r9, 0x7bc65c783158aea3 
mulx r13, rbp, r9
adcx rbp, r11
mov r11, 0x6cfc5fd681c52056 
mulx r10, r14, r11
adox rbp, rbx
adcx r14, r13
mov rbx, 0x2341f27177344 
mulx r11, r13, rbx
adcx r13, r10
adox r14, rcx
adox r13, [ rsp + 0x1b8 ]
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r15, [ rsp - 0x48 ]
adcx rdi, [ rsp - 0x28 ]
adcx r12, [ rsp + 0x0 ]
adcx rbp, [ rsp + 0x20 ]
adcx r14, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x10 ]
mov rcx, [ rsp + 0x140 ]
seto r10b
dec rdx
movzx r8, r8b
adox r8, rdx
adox rcx, [ rsp + 0x1b0 ]
setc r8b
clc
movzx r10, r10b
adcx r10, rdx
adcx rcx, r11
mov r10, 0xffffffffffffffff 
mov rdx, r15
mulx r11, r15, r10
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov rbx, r15
adox rbx, r11
mov r9, r15
adcx r9, rdx
adcx rbx, rdi
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1c0 ], rbx
mulx rbx, rdi, r9
adox r15, r11
adox rdi, r11
adcx r15, r12
adcx rdi, rbp
mov r12, 0x7bc65c783158aea3 
mulx r11, rbp, r12
adox rbp, rbx
adcx rbp, r14
mov r14, 0x2341f27177344 
mulx r9, rbx, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x1c8 ], rbp
mulx rbp, r12, r14
adox r12, r11
adox rbx, rbp
mov rdx, 0x0 
adox r9, rdx
adcx r12, r13
dec rdx
movzx r8, r8b
adox r8, rdx
adox rcx, [ rsp + 0x78 ]
adcx rbx, rcx
movzx r10, r10b
movzx r8, r10b
adox r8, [ rsp + 0x70 ]
adcx r9, r8
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov r10, [ rsp + 0x1c0 ]
mov r11, 0xffffffffffffffff 
sub r10, r11
mov rbp, r15
sbb rbp, r11
mov rcx, rdi
sbb rcx, r11
mov r8, [ rsp + 0x1c8 ]
mov rdx, 0xfdc1767ae2ffffff 
sbb r8, rdx
mov rdx, r12
mov r11, 0x7bc65c783158aea3 
sbb rdx, r11
mov r11, rbx
sbb r11, r14
mov r14, r9
mov [ rsp + 0x1d0 ], rbp
mov rbp, 0x2341f27177344 
sbb r14, rbp
movzx rbp, r13b
sbb rbp, 0x00000000
cmovc r10, [ rsp + 0x1c0 ]
cmovc r8, [ rsp + 0x1c8 ]
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r8
cmovc r14, r9
cmovc rcx, rdi
cmovc rdx, r12
mov [ rbp + 0x20 ], rdx
mov [ rbp + 0x30 ], r14
cmovc r11, rbx
mov [ rbp + 0x28 ], r11
mov rdi, [ rsp + 0x1d0 ]
cmovc rdi, r15
mov [ rbp + 0x8 ], rdi
mov [ rbp + 0x0 ], r10
mov [ rbp + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.9658
; seed 0086788876598298 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7455294 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=26, initial num_batches=31): 147455 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019778562723348
; number reverted permutation / tried permutation: 71034 / 89841 =79.066%
; number reverted decision / tried decision: 60775 / 90158 =67.409%
; validated in 421.296s
