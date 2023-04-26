SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 464
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x30 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x30 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x30 ]
test al, al
adox r12, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbx
mulx rbx, r12, [ rsi + 0x30 ]
adcx r8, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r8
mulx r8, rbx, [ rsi + 0x30 ]
adcx rbp, r9
adcx rbx, rdi
adcx r14, r8
mov rdx, [ rsi + 0x30 ]
mulx rdi, r9, [ rsi + 0x28 ]
adcx r9, r15
adcx r11, rdi
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r14
mulx r14, r9, [ rsi + 0x10 ]
setc dl
clc
adcx rdi, r8
adcx r9, r11
movzx r8, dl
lea r8, [ r8 + rcx ]
adcx rax, r14
mov rdx, [ rsi + 0x8 ]
mulx r11, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r8
mulx r8, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], rax
mulx rax, r12, [ rsi + 0x10 ]
adox r12, r13
setc dl
clc
adcx rcx, r8
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r12
mulx r12, r8, rdx
adcx r8, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], r9
mulx r9, r11, [ rsi + 0x10 ]
adcx r11, r12
adcx rbx, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r12, [ rsi + 0x18 ]
adox r12, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x20 ], r12
mulx r12, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], r12
mov [ rsp + 0x30 ], rdi
mulx rdi, r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], rbx
mulx rbx, r15, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r8
mulx r8, r11, [ rsi + 0x28 ]
adox r15, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x58 ], r15
mulx r15, r9, [ rsi + 0x10 ]
adcx r11, rbp
adcx r9, r8
mov rdx, 0xffffffffffffffff 
mulx r8, rbp, r12
adox rax, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x60 ], rax
mulx rax, rbx, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x68 ], r9
mov r9, -0x2 
inc r9
adox rbx, rdi
mov dil, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r11
mulx r11, r9, [ rsi + 0x0 ]
adox r9, rax
mov rdx, [ rsi + 0x20 ]
mov byte [ rsp + 0x78 ], dil
mulx rdi, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
adox rcx, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x90 ], rcx
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r15, rdx
clc
mov rdx, -0x1 
movzx r13, r13b
adcx r13, rdx
adcx r10, rax
mov rdx, [ rsi + 0x28 ]
mulx rax, r13, [ rsi + 0x18 ]
adcx r13, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
adcx rdi, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa0 ], rdi
mulx rdi, rax, [ rsi + 0x20 ]
adox rax, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xa8 ], r10
mulx r10, r14, [ rsi + 0x28 ]
adox r14, rdi
adox r11, r10
mov rdx, 0x0 
adcx r13, rdx
adox rcx, rdx
mov rdi, 0xfdc1767ae2ffffff 
mov rdx, r12
mulx r10, r12, rdi
mov rdi, rbp
mov [ rsp + 0xb0 ], r13
xor r13, r13
adox rdi, rdx
mov rdi, rbp
adcx rdi, r8
adcx rbp, r8
adox rdi, rbx
mov rbx, 0x7bc65c783158aea3 
mov [ rsp + 0xb8 ], r15
mulx r15, r13, rbx
adox rbp, r9
adcx r12, r8
adox r12, [ rsp + 0x90 ]
adcx r13, r10
mov r8, 0x6cfc5fd681c52056 
mulx r10, r9, r8
adcx r9, r15
mov r15, 0x2341f27177344 
mulx rbx, r8, r15
adcx r8, r10
mov rdx, 0x0 
adcx rbx, rdx
adox r13, rax
adox r9, r14
adox r8, r11
mov rdx, [ rsi + 0x28 ]
mulx r14, rax, rdx
adox rbx, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r11
mov [ rsp + 0xc8 ], rbx
mulx rbx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], r9
mulx r9, r8, [ rsi + 0x8 ]
clc
adcx r8, rcx
adcx r10, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0xe0 ], r10
mov r10, -0x2 
inc r10
adox rcx, rdi
adcx r11, r15
mov rdi, 0xfdc1767ae2ffffff 
xchg rdx, rdi
mulx r10, r15, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], r11
mov [ rsp + 0xf0 ], r8
mulx r8, r11, [ rsi + 0x28 ]
adcx r11, rbx
adcx rax, r8
mov rdx, [ rsi + 0x30 ]
mulx r8, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], rax
mov [ rsp + 0x100 ], r11
mulx r11, rax, [ rsi + 0x20 ]
adcx rbx, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, r14, rdx
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x110 ], r8
mov byte [ rsp + 0x118 ], dil
mulx rdi, r8, [ rsi + 0x10 ]
clc
adcx r14, r9
adox r14, rbp
adcx r8, rbx
adox r8, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ rsi + 0x8 ]
adcx rbp, rdi
adox rbp, r13
adcx rax, r12
mov rdx, 0xffffffffffffffff 
mulx r9, r13, rcx
adox rax, [ rsp + 0xd8 ]
mov rbx, r13
seto dil
mov r12, -0x2 
inc r12
adox rbx, r9
mov r12, r13
adox r12, r9
adox r15, r9
mov r9, 0x7bc65c783158aea3 
mov rdx, r9
mov [ rsp + 0x120 ], rax
mulx rax, r9, rcx
adox r9, r10
mov r10, 0x6cfc5fd681c52056 
mov rdx, r10
mov [ rsp + 0x128 ], r9
mulx r9, r10, rcx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x130 ], dil
mov [ rsp + 0x138 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
adcx rdi, r11
adox r10, rax
mov rdx, [ rsi + 0x30 ]
mulx rax, r11, [ rsi + 0x8 ]
adcx r11, r15
mov rdx, 0x0 
adcx rax, rdx
clc
adcx r13, rcx
mov r13, 0x2341f27177344 
mov rdx, rcx
mulx r15, rcx, r13
adcx rbx, r14
adcx r12, r8
adox rcx, r9
adcx rbp, [ rsp + 0x138 ]
mov rdx, 0x0 
adox r15, rdx
movzx r14, byte [ rsp + 0x130 ]
dec rdx
adox r14, rdx
adox rdi, [ rsp + 0xd0 ]
adox r11, [ rsp + 0xc8 ]
movzx r8, byte [ rsp + 0x118 ]
adox r8, rax
seto r14b
inc rdx
adox rbx, [ rsp + 0x88 ]
mov r9, [ rsp + 0x120 ]
adcx r9, [ rsp + 0x128 ]
adcx r10, rdi
adox r12, [ rsp + 0x80 ]
adox rbp, [ rsp + 0x50 ]
mov rax, 0xffffffffffffffff 
mov rdx, rbx
mulx rdi, rbx, rax
adox r9, [ rsp + 0x48 ]
adcx rcx, r11
adox r10, [ rsp + 0x40 ]
adox rcx, [ rsp + 0x70 ]
adcx r15, r8
adox r15, [ rsp + 0x68 ]
movzx r11, r14b
mov r8, 0x0 
adcx r11, r8
mov r14, rbx
clc
adcx r14, rdx
adox r11, [ rsp + 0xb8 ]
mov r14, rbx
seto r13b
mov rax, -0x3 
inc rax
adox r14, rdi
adox rbx, rdi
adcx r14, r12
mov r12, 0xfdc1767ae2ffffff 
mulx rax, r8, r12
adox r8, rdi
adcx rbx, rbp
adcx r8, r9
mov rbp, 0x7bc65c783158aea3 
mulx r9, rdi, rbp
adox rdi, rax
mov rax, 0x6cfc5fd681c52056 
mulx r12, rbp, rax
adox rbp, r9
adcx rdi, r10
adcx rbp, rcx
mov r10, 0x2341f27177344 
mulx r9, rcx, r10
adox rcx, r12
adcx rcx, r15
mov rdx, 0x0 
adox r9, rdx
adcx r9, r11
mov r15, -0x3 
inc r15
adox r14, [ rsp + 0x38 ]
adox rbx, [ rsp + 0x30 ]
adox r8, [ rsp + 0x18 ]
movzx r11, r13b
adcx r11, rdx
mov r13, 0xffffffffffffffff 
mov rdx, r14
mulx r12, r14, r13
adox rdi, [ rsp + 0x8 ]
adox rbp, [ rsp + 0xa8 ]
adox rcx, [ rsp + 0x98 ]
mov r15, r14
clc
adcx r15, r12
mov r10, r14
adcx r10, r12
adox r9, [ rsp + 0xa0 ]
adox r11, [ rsp + 0xb0 ]
seto al
mov r13, -0x2 
inc r13
adox r14, rdx
adox r15, rbx
adox r10, r8
mov r14, 0xfdc1767ae2ffffff 
mulx r8, rbx, r14
adcx rbx, r12
adox rbx, rdi
mov r12, 0x7bc65c783158aea3 
mulx r13, rdi, r12
adcx rdi, r8
adox rdi, rbp
mov rbp, 0x6cfc5fd681c52056 
mulx r12, r8, rbp
adcx r8, r13
mov r13, 0x2341f27177344 
mulx r14, rbp, r13
adcx rbp, r12
adox r8, rcx
adox rbp, r9
setc dl
clc
adcx r15, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
adcx rbx, [ rsp + 0x10 ]
adcx rdi, [ rsp + 0x20 ]
adcx r8, [ rsp + 0x58 ]
movzx rcx, dl
lea rcx, [ rcx + r14 ]
adcx rbp, [ rsp + 0x60 ]
adox rcx, r11
movzx r9, al
mov r11, 0x0 
adox r9, r11
mov rdx, [ rsi + 0x20 ]
mulx r12, rax, [ rsi + 0x30 ]
movzx rdx, byte [ rsp + 0x78 ]
dec r11
adox rdx, r11
adox rax, [ rsp + 0x28 ]
mov rdx, 0x0 
adox r12, rdx
adcx rax, rcx
mov r14, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r14
adcx r12, r9
mov r9, r15
inc r11
adox r9, rcx
mov r11, r15
adox r11, rcx
setc r13b
clc
adcx r15, rdx
adcx r9, r10
mov r15, 0xfdc1767ae2ffffff 
mulx r14, r10, r15
adox r10, rcx
adcx r11, rbx
adcx r10, rdi
mov rbx, 0x7bc65c783158aea3 
mulx rcx, rdi, rbx
adox rdi, r14
adcx rdi, r8
mov r8, 0x6cfc5fd681c52056 
mulx rbx, r14, r8
adox r14, rcx
adcx r14, rbp
mov rbp, 0x2341f27177344 
mulx r8, rcx, rbp
adox rcx, rbx
mov rdx, 0x0 
adox r8, rdx
adcx rcx, rax
mov rax, -0x3 
inc rax
adox r9, [ rsp + 0xc0 ]
adcx r8, r12
movzx r12, r13b
adcx r12, rdx
adox r11, [ rsp + 0xf0 ]
adox r10, [ rsp + 0xe0 ]
mov r13, 0xffffffffffffffff 
mov rdx, r9
mulx rbx, r9, r13
adox rdi, [ rsp + 0xe8 ]
adox r14, [ rsp + 0x100 ]
adox rcx, [ rsp + 0xf8 ]
mov rax, r9
clc
adcx rax, rbx
mov rbp, r9
adcx rbp, rbx
adox r8, [ rsp + 0x108 ]
adox r12, [ rsp + 0x110 ]
seto r15b
mov r13, -0x2 
inc r13
adox r9, rdx
adox rax, r11
adox rbp, r10
mov r9, 0xfdc1767ae2ffffff 
mulx r10, r11, r9
adcx r11, rbx
adox r11, rdi
mov rbx, 0x7bc65c783158aea3 
mulx r13, rdi, rbx
adcx rdi, r10
adox rdi, r14
mov r14, 0x6cfc5fd681c52056 
mulx rbx, r10, r14
adcx r10, r13
adox r10, rcx
mov rcx, 0x2341f27177344 
mulx r14, r13, rcx
adcx r13, rbx
mov rdx, 0x0 
adcx r14, rdx
clc
adcx rax, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x38 ]
adcx r11, [ rsp - 0x8 ]
adox r13, r8
adox r14, r12
adcx rdi, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x28 ]
movzx r8, r15b
adox r8, rdx
mov r15, 0xffffffffffffffff 
mov rdx, rax
mulx r12, rax, r15
adcx r14, [ rsp - 0x30 ]
mov rbx, rax
mov rcx, -0x2 
inc rcx
adox rbx, r12
mov rcx, rax
adox rcx, r12
adcx r8, [ rsp - 0x18 ]
setc r9b
clc
adcx rax, rdx
adcx rbx, rbp
adcx rcx, r11
mov rax, 0xfdc1767ae2ffffff 
mulx r11, rbp, rax
adox rbp, r12
adcx rbp, rdi
mov rdi, 0x7bc65c783158aea3 
mulx rax, r12, rdi
adox r12, r11
adcx r12, r10
mov r10, 0x6cfc5fd681c52056 
mulx rdi, r11, r10
adox r11, rax
adcx r11, r13
mov r13, 0x2341f27177344 
mulx r10, rax, r13
adox rax, rdi
mov rdx, 0x0 
adox r10, rdx
adcx rax, r14
adcx r10, r8
movzx r14, r9b
adc r14, 0x0
mov r9, rbx
sub r9, r15
mov r8, rcx
sbb r8, r15
mov rdi, rbp
sbb rdi, r15
mov rdx, r12
mov r13, 0xfdc1767ae2ffffff 
sbb rdx, r13
mov r13, r11
mov r15, 0x7bc65c783158aea3 
sbb r13, r15
mov r15, rax
mov [ rsp + 0x140 ], rdi
mov rdi, 0x6cfc5fd681c52056 
sbb r15, rdi
mov rdi, r10
mov [ rsp + 0x148 ], r9
mov r9, 0x2341f27177344 
sbb rdi, r9
sbb r14, 0x00000000
cmovc r8, rcx
cmovc rdx, r12
cmovc r13, r11
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rdx
mov [ r14 + 0x20 ], r13
cmovc r15, rax
mov rcx, [ rsp + 0x148 ]
cmovc rcx, rbx
mov rbx, [ rsp + 0x140 ]
cmovc rbx, rbp
mov [ r14 + 0x0 ], rcx
mov [ r14 + 0x10 ], rbx
cmovc rdi, r10
mov [ r14 + 0x30 ], rdi
mov [ r14 + 0x28 ], r15
mov [ r14 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 464
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 2.1559
; seed 0373348878534753 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10122710 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=50, initial num_batches=31): 216047 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.021342802470879833
; number reverted permutation / tried permutation: 73279 / 89971 =81.447%
; number reverted decision / tried decision: 62659 / 90028 =69.599%
; validated in 531.691s
