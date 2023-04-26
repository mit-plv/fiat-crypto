SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 568
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, rcx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
adcx r13, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rsi + 0x28 ]
adox r12, r10
adcx rcx, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r11
mulx r11, rax, rdx
adox rdi, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], r13
mulx r13, rcx, [ rsi + 0x28 ]
adcx r15, rbx
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp - 0x18 ], r15
mulx r15, rbx, rax
mov rdx, 0x2341f27177344 
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r9
mulx r9, rbp, rax
adox rcx, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], rcx
mulx rcx, r12, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r14
mulx r14, rcx, rax
mov rdx, rcx
mov [ rsp + 0x18 ], r10
setc r10b
clc
adcx rdx, r14
adox r12, r13
mov r13, rcx
adcx r13, r14
mov [ rsp + 0x20 ], r12
seto r12b
mov [ rsp + 0x28 ], r13
mov r13, -0x2 
inc r13
adox r8, r11
adcx rbx, r14
seto r11b
inc r13
adox rcx, rax
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, [ rsi + 0x0 ]
adox rcx, r8
mov rdx, 0x7bc65c783158aea3 
mov [ rsp + 0x30 ], r14
mulx r14, r8, rax
adcx r8, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rcx
mulx rcx, r15, [ rsi + 0x18 ]
seto dl
mov byte [ rsp + 0x40 ], r12b
mov r12, -0x2 
inc r12
adox r15, r13
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x48 ], r15
mulx r15, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r8
mov [ rsp + 0x58 ], rbx
mulx rbx, r8, rdx
adox r12, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x60 ], r12
mulx r12, rcx, [ rsi + 0x18 ]
adox r8, r15
adox rcx, rbx
mov rdx, 0x6cfc5fd681c52056 
mulx rbx, r15, rax
adcx r15, r14
mov rdx, [ rsi + 0x30 ]
mulx r14, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r8
mulx r8, rcx, [ rsi + 0x28 ]
adox rcx, r12
adox rax, r8
mov rdx, [ rsi + 0x20 ]
mulx r8, r12, [ rsi + 0x8 ]
adcx rbp, rbx
mov rdx, 0x0 
adcx r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x78 ], rax
mulx rax, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x80 ], rcx
mov [ rsp + 0x88 ], r9
mulx r9, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x90 ], rcx
mov [ rsp + 0x98 ], rbp
mulx rbp, rcx, [ rsi + 0x20 ]
mov rdx, 0x0 
adox r14, rdx
test al, al
adox r12, r9
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], r12
mulx r12, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r14
mov [ rsp + 0xb0 ], r15
mulx r15, r14, [ rsi + 0x30 ]
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx rdi, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r10, rdx
adox rbx, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
adcx r8, rbp
adox r9, rax
adox r10, r12
mov rdx, [ rsi + 0x30 ]
mulx rbp, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc0 ], r10
mulx r10, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc8 ], r9
mov [ rsp + 0xd0 ], r8
mulx r8, r9, [ rsi + 0x20 ]
adox r9, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], r9
mulx r9, rcx, rdx
adox rax, r8
adcx r14, rbx
mov rdx, [ rsi + 0x0 ]
mulx r8, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xe0 ], rax
mov [ rsp + 0xe8 ], rbx
mulx rbx, rax, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r15, rdx
clc
adcx rax, r8
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xf0 ], rax
mulx rax, r8, [ rsi + 0x10 ]
adcx rcx, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xf8 ], rcx
mulx rcx, rbx, [ rsi + 0x30 ]
mov rdx, 0x0 
adox rbp, rdx
adcx r12, r9
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x100 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rbx, rbp
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x108 ], rbx
mulx rbx, rbp, [ rsi + 0x20 ]
adox r8, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x110 ], r8
mulx r8, rcx, [ rsi + 0x30 ]
adcx r10, [ rsp + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r9
mov [ rsp + 0x120 ], r10
mulx r10, r9, [ rsi + 0x10 ]
adcx r9, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x128 ], r9
mov [ rsp + 0x130 ], r12
mulx r12, r9, [ rsi + 0x18 ]
adox r9, rax
adox rbp, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, rax, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x138 ], rbp
mov [ rsp + 0x140 ], r9
mulx r9, rbp, rdx
adox rax, rbx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x148 ], rax
mulx rax, rbx, [ rsi + 0x0 ]
adox rbp, r12
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x150 ], r9
mulx r9, r12, [ rsi + 0x0 ]
adcx rcx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x158 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
adc r8, 0x0
add r11b, 0xFF
adcx r12, [ rsp - 0x8 ]
adcx r10, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, -0x1 
movzx r13, r13b
adox r13, rdx
adox r12, [ rsp + 0x28 ]
adcx r11, rbp
adcx rbx, r9
adox r10, [ rsp + 0x58 ]
adox r11, [ rsp + 0x50 ]
adox rbx, [ rsp + 0xb0 ]
mov rdx, [ rsi + 0x30 ]
mulx rbp, r13, [ rsi + 0x0 ]
adcx r13, rax
mov rdx, [ rsi + 0x30 ]
mulx r9, rax, [ rsi + 0x28 ]
mov rdx, 0x0 
adcx rbp, rdx
adox r13, [ rsp + 0x98 ]
adox rbp, [ rsp + 0x88 ]
movzx rdx, byte [ rsp + 0x40 ]
clc
mov [ rsp + 0x160 ], r8
mov r8, -0x1 
adcx rdx, r8
adcx rax, [ rsp + 0x8 ]
mov rdx, [ rsp + 0x38 ]
setc r8b
clc
adcx rdx, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
mov [ rsp + 0x168 ], rax
mov rax, 0xffffffffffffffff 
mov [ rsp + 0x170 ], rcx
mov [ rsp + 0x178 ], r10
mulx r10, rcx, rax
adcx r11, [ rsp - 0x18 ]
adcx rdi, rbx
movzx rbx, r8b
lea rbx, [ rbx + r9 ]
adcx r13, [ rsp + 0xd0 ]
adcx r14, rbp
setc r9b
movzx r9, r9b
adox r9, r15
mov r15, rcx
clc
adcx r15, r10
mov rbp, rcx
adcx rbp, r10
seto r8b
mov rax, -0x2 
inc rax
adox rcx, rdx
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x180 ], rbx
mulx rbx, rax, rcx
adox r15, r12
adcx rax, r10
adox rbp, [ rsp + 0x178 ]
mov r12, 0x6cfc5fd681c52056 
mulx rcx, r10, r12
adox rax, r11
mov r11, 0x7bc65c783158aea3 
mov byte [ rsp + 0x188 ], r8b
mulx r8, r12, r11
adcx r12, rbx
adox r12, rdi
adcx r10, r8
mov rdi, 0x2341f27177344 
mulx r8, rbx, rdi
adox r10, r13
adcx rbx, rcx
mov rdx, 0x0 
adcx r8, rdx
clc
adcx r15, [ rsp + 0xe8 ]
adcx rbp, [ rsp + 0xf0 ]
adcx rax, [ rsp + 0xf8 ]
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx rcx, r13, r15
adcx r12, [ rsp + 0x130 ]
adox rbx, r14
adox r8, r9
adcx r10, [ rsp + 0x120 ]
adcx rbx, [ rsp + 0x128 ]
movzx r14, byte [ rsp + 0x188 ]
mov r9, 0x0 
adox r14, r9
adcx r8, [ rsp + 0x170 ]
mov rdi, r13
mov rdx, -0x3 
inc rdx
adox rdi, rcx
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r15
mulx r11, r15, r9
mov r9, r13
adox r9, rcx
adcx r14, [ rsp + 0x160 ]
adox r15, rcx
setc cl
clc
adcx r13, rdx
adcx rdi, rbp
adcx r9, rax
adcx r15, r12
mov r13, 0x7bc65c783158aea3 
mulx rax, rbp, r13
adox rbp, r11
adcx rbp, r10
mov r12, 0x6cfc5fd681c52056 
mulx r11, r10, r12
adox r10, rax
adcx r10, rbx
mov rbx, 0x2341f27177344 
mulx r12, rax, rbx
adox rax, r11
adcx rax, r8
mov rdx, 0x0 
adox r12, rdx
mov r8, -0x3 
inc r8
adox rdi, [ rsp + 0x30 ]
adox r9, [ rsp + 0x48 ]
adox r15, [ rsp + 0x60 ]
adox rbp, [ rsp + 0x70 ]
mov rdx, rdi
mulx r11, rdi, r13
adox r10, [ rsp + 0x68 ]
adox rax, [ rsp + 0x80 ]
adcx r12, r14
adox r12, [ rsp + 0x78 ]
mov r14, 0xffffffffffffffff 
mulx rbx, r8, r14
movzx r14, cl
mov r13, 0x0 
adcx r14, r13
mov rcx, r8
clc
adcx rcx, rbx
adox r14, [ rsp + 0xa8 ]
mov r13, r8
adcx r13, rbx
mov [ rsp + 0x190 ], r14
seto r14b
mov [ rsp + 0x198 ], r12
mov r12, -0x2 
inc r12
adox r8, rdx
adox rcx, r9
mov r8, 0xfdc1767ae2ffffff 
mulx r12, r9, r8
adox r13, r15
adcx r9, rbx
adox r9, rbp
adcx rdi, r12
mov r15, 0x2341f27177344 
mulx rbx, rbp, r15
adox rdi, r10
mov r10, 0x6cfc5fd681c52056 
mulx r15, r12, r10
adcx r12, r11
adox r12, rax
adcx rbp, r15
adox rbp, [ rsp + 0x198 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rbx, [ rsp + 0x190 ]
clc
adcx rcx, [ rsp + 0x90 ]
adcx r13, [ rsp + 0xa0 ]
movzx r11, r14b
adox r11, rdx
adcx r9, [ rsp + 0xb8 ]
adcx rdi, [ rsp + 0xc8 ]
adcx r12, [ rsp + 0xc0 ]
adcx rbp, [ rsp + 0xd8 ]
adcx rbx, [ rsp + 0xe0 ]
mov rax, 0xffffffffffffffff 
mov rdx, rcx
mulx r14, rcx, rax
mov r15, rcx
mov r8, -0x2 
inc r8
adox r15, rdx
adcx r11, [ rsp + 0x100 ]
mov r15, rcx
setc r8b
clc
adcx r15, r14
adox r15, r13
adcx rcx, r14
adox rcx, r9
mov r13, 0xfdc1767ae2ffffff 
mulx rax, r9, r13
adcx r9, r14
adox r9, rdi
mov rdi, 0x7bc65c783158aea3 
mulx r13, r14, rdi
adcx r14, rax
mulx rdi, rax, r10
adcx rax, r13
mov r13, 0x2341f27177344 
mov byte [ rsp + 0x1a0 ], r8b
mulx r8, r10, r13
adox r14, r12
adox rax, rbp
adcx r10, rdi
setc dl
clc
adcx r15, [ rsp - 0x38 ]
adox r10, rbx
mov r12, 0xfdc1767ae2ffffff 
xchg rdx, r15
mulx rbx, rbp, r12
adcx rcx, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x48 ]
adcx r14, [ rsp - 0x30 ]
movzx rdi, r15b
lea rdi, [ rdi + r8 ]
adox rdi, r11
movzx r11, byte [ rsp + 0x1a0 ]
mov r8, 0x0 
adox r11, r8
adcx rax, [ rsp + 0x0 ]
adcx r10, [ rsp + 0x20 ]
mov r15, 0xffffffffffffffff 
mulx r13, r8, r15
adcx rdi, [ rsp + 0x168 ]
adcx r11, [ rsp + 0x180 ]
mov r12, r8
mov r15, -0x2 
inc r15
adox r12, rdx
mov r12, r8
setc r15b
clc
adcx r12, r13
adox r12, rcx
adcx r8, r13
adox r8, r9
adcx rbp, r13
mov rcx, 0x7bc65c783158aea3 
mulx r13, r9, rcx
adcx r9, rbx
adox rbp, r14
mov rbx, 0x6cfc5fd681c52056 
mulx rcx, r14, rbx
adcx r14, r13
adox r9, rax
mov rax, 0x2341f27177344 
mulx rbx, r13, rax
adox r14, r10
adcx r13, rcx
setc dl
clc
adcx r12, [ rsp + 0x118 ]
movzx r10, dl
lea r10, [ r10 + rbx ]
mov rcx, 0xfdc1767ae2ffffff 
mov rdx, r12
mulx rbx, r12, rcx
adcx r8, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x110 ]
adox r13, rdi
adcx r9, [ rsp + 0x140 ]
adox r10, r11
movzx rdi, r15b
mov r11, 0x0 
adox rdi, r11
adcx r14, [ rsp + 0x138 ]
adcx r13, [ rsp + 0x148 ]
mov r15, 0xffffffffffffffff 
mulx rax, r11, r15
mov rcx, r11
mov r15, -0x2 
inc r15
adox rcx, rax
adcx r10, [ rsp + 0x158 ]
mov r15, r11
adox r15, rax
adox r12, rax
adcx rdi, [ rsp + 0x150 ]
setc al
clc
adcx r11, rdx
adcx rcx, r8
adcx r15, rbp
mov r11, 0x7bc65c783158aea3 
mulx rbp, r8, r11
adox r8, rbx
adcx r12, r9
mov rbx, 0x2341f27177344 
mulx r11, r9, rbx
adcx r8, r14
mov r14, 0x6cfc5fd681c52056 
mov [ rsp + 0x1a8 ], r8
mulx r8, rbx, r14
adox rbx, rbp
adcx rbx, r13
adox r9, r8
mov rdx, 0x0 
adox r11, rdx
adcx r9, r10
adcx r11, rdi
movzx r13, al
adc r13, 0x0
mov r10, rcx
mov rax, 0xffffffffffffffff 
sub r10, rax
mov rdi, r15
sbb rdi, rax
mov rbp, r12
sbb rbp, rax
mov r8, [ rsp + 0x1a8 ]
mov rdx, 0xfdc1767ae2ffffff 
sbb r8, rdx
mov rdx, rbx
mov rax, 0x7bc65c783158aea3 
sbb rdx, rax
mov rax, r9
sbb rax, r14
mov r14, r11
mov [ rsp + 0x1b0 ], rdx
mov rdx, 0x2341f27177344 
sbb r14, rdx
sbb r13, 0x00000000
cmovc rdi, r15
cmovc r10, rcx
cmovc rbp, r12
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rbp
cmovc r14, r11
cmovc r8, [ rsp + 0x1a8 ]
mov [ r13 + 0x18 ], r8
mov [ r13 + 0x30 ], r14
mov [ r13 + 0x8 ], rdi
cmovc rax, r9
mov [ r13 + 0x28 ], rax
mov rcx, [ rsp + 0x1b0 ]
cmovc rcx, rbx
mov [ r13 + 0x20 ], rcx
mov [ r13 + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 568
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.9153
; seed 2635246268404113 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11654000 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=24, initial num_batches=31): 222782 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019116354899605285
; number reverted permutation / tried permutation: 69798 / 90195 =77.386%
; number reverted decision / tried decision: 61822 / 89804 =68.841%
; validated in 428.688s
