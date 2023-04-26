SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 616
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r12
mulx r12, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r9
mov [ rsp - 0x18 ], r11
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], r15
mulx r15, r9, [ rsi + 0x18 ]
add rdi, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rdi
mulx rdi, r11, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r11, rcx
adox r9, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, rdx
adox rcx, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rcx
mulx rcx, r15, [ rsi + 0x30 ]
adox rbx, rdi
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
setc dl
clc
adcx r15, rbx
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], rdi
mulx rdi, r15, [ rsi + 0x30 ]
adcx r15, rcx
adcx r8, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], r15
mulx r15, r8, [ rsi + 0x20 ]
setc dl
clc
adcx rcx, r12
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], r11
mov [ rsp + 0x50 ], r15
mulx r15, r11, rdx
adcx r8, rdi
setc dl
clc
adcx r11, r13
adcx rcx, r15
mov r13b, dl
mov rdx, [ rsi + 0x28 ]
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r8
mov byte [ rsp + 0x60 ], r13b
mulx r13, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x68 ], rcx
mov [ rsp + 0x70 ], r11
mulx r11, rcx, [ rsi + 0x18 ]
adox rdi, rbp
adcx r8, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, rbp, [ rsi + 0x20 ]
adcx rbp, r13
adcx rax, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rsi + 0x30 ]
adcx r13, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x78 ], rdi
mulx rdi, r10, rdx
setc dl
clc
adcx r14, rdi
adox rcx, r15
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x88 ], r13
mov [ rsp + 0x90 ], rax
mulx rax, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], rbp
mov [ rsp + 0xa0 ], r8
mulx r8, rbp, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r14
mulx r14, r11, [ rsi + 0x28 ]
adcx rdi, [ rsp - 0x8 ]
movzx rdx, r15b
lea rdx, [ rdx + r9 ]
adcx r13, rcx
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r15, [ rsi + 0x20 ]
adcx r15, rax
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xb8 ], r9
mulx r9, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r15
mov [ rsp + 0xc8 ], r13
mulx r13, r15, [ rsi + 0x18 ]
adcx rax, rcx
adcx rbp, r9
adc r8, 0x0
mov rdx, [ rsi + 0x30 ]
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], rbp
mulx rbp, r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rax
mov [ rsp + 0xe8 ], rdi
mulx rdi, rax, [ rsi + 0x10 ]
add bl, 0x7F
adox r8, [ rsp - 0x18 ]
adox r15, rbp
adox rax, r13
adox r11, rdi
adox rcx, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r13, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf0 ], rcx
mulx rcx, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xf8 ], rdi
mov [ rsp + 0x100 ], r11
mulx r11, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x108 ], rax
mov [ rsp + 0x110 ], r15
mulx r15, rax, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x118 ], r9
mov [ rsp + 0x120 ], r8
mulx r8, r9, [ rsi + 0x18 ]
add r12b, 0xFF
adcx r13, [ rsp - 0x38 ]
adox rbx, rcx
adox rax, r14
adox r9, r15
mov rdx, [ rsi + 0x30 ]
mulx r14, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, rcx, rdx
adox rdi, r8
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x128 ], r13
mulx r13, r8, rdx
adcx r12, rbp
adcx rcx, r14
mov rdx, 0xffffffffffffffff 
mulx r14, rbp, r10
mov rdx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x130 ], rcx
mov [ rsp + 0x138 ], r12
mulx r12, rcx, r10
mov rdx, 0x6cfc5fd681c52056 
mov [ rsp + 0x140 ], rdi
mov [ rsp + 0x148 ], r9
mulx r9, rdi, r10
mov rdx, rbp
mov [ rsp + 0x150 ], rax
setc al
clc
adcx rdx, r14
mov [ rsp + 0x158 ], rbx
movzx rbx, al
lea rbx, [ rbx + r15 ]
mov r15, 0x7bc65c783158aea3 
xchg rdx, r15
mov [ rsp + 0x160 ], rbx
mulx rbx, rax, r10
mov rdx, rbp
adcx rdx, r14
adcx rcx, r14
adcx rax, r12
adcx rdi, rbx
mov r14, 0x2341f27177344 
xchg rdx, r14
mulx rbx, r12, r10
adox r8, r11
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x168 ], r8
mulx r8, r11, [ rsi + 0x28 ]
adcx r12, r9
adox r11, r13
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx rbp, r10
adcx r15, [ rsp + 0xb0 ]
adcx r14, [ rsp + 0xe8 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r13, rdx
seto dl
mov [ rsp + 0x170 ], r11
mov r11, -0x2 
inc r11
adox r15, [ rsp - 0x40 ]
adcx rcx, [ rsp + 0xc8 ]
adcx rax, [ rsp + 0xc0 ]
adox r14, [ rsp + 0x70 ]
adcx rdi, [ rsp + 0xe0 ]
adox rcx, [ rsp + 0x68 ]
adcx r12, [ rsp + 0xd8 ]
adox rax, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0x98 ]
adcx rbx, [ rsp + 0xd0 ]
adox r12, [ rsp + 0x90 ]
adox rbx, [ rsp + 0x88 ]
movzx r11, dl
lea r11, [ r11 + r8 ]
setc r8b
movzx rdx, byte [ rsp + 0x60 ]
clc
mov [ rsp + 0x178 ], r11
mov r11, -0x1 
adcx rdx, r11
adcx rbp, [ rsp + 0x50 ]
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x180 ], rbp
mulx rbp, r11, [ rsi + 0x20 ]
adcx r13, r10
adcx r9, [ rsp - 0x28 ]
adcx r11, [ rsp - 0x30 ]
movzx r8, r8b
movzx rdx, r8b
adox rdx, [ rsp + 0xb8 ]
mov r10, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x188 ], r11
mulx r11, r8, r10
mov r10, r8
mov [ rsp + 0x190 ], r9
setc r9b
clc
adcx r10, r11
mov [ rsp + 0x198 ], r13
mov r13, r8
adcx r13, r11
mov [ rsp + 0x1a0 ], r15
seto r15b
mov [ rsp + 0x1a8 ], rbx
mov rbx, -0x2 
inc rbx
adox r8, rdx
movzx r8, r9b
lea r8, [ r8 + rbp ]
adox r10, r14
adox r13, rcx
mov r14, 0xfdc1767ae2ffffff 
mulx rbp, rcx, r14
adcx rcx, r11
adox rcx, rax
mov rax, 0x7bc65c783158aea3 
mulx r11, r9, rax
adcx r9, rbp
adox r9, rdi
mov rdi, 0x2341f27177344 
mulx rbx, rbp, rdi
mov rdi, 0x6cfc5fd681c52056 
mulx r14, rax, rdi
adcx rax, r11
adcx rbp, r14
mov rdx, 0x0 
adcx rbx, rdx
adox rax, r12
adox rbp, [ rsp + 0x1a8 ]
clc
adcx r10, [ rsp - 0x10 ]
adox rbx, [ rsp + 0x1a0 ]
adcx r13, [ rsp + 0x0 ]
movzx r12, r15b
adox r12, rdx
adcx rcx, [ rsp + 0x120 ]
adcx r9, [ rsp + 0x110 ]
adcx rax, [ rsp + 0x108 ]
adcx rbp, [ rsp + 0x100 ]
mov r15, 0xffffffffffffffff 
mov rdx, r10
mulx r11, r10, r15
mov r14, r10
mov rdi, -0x2 
inc rdi
adox r14, r11
adcx rbx, [ rsp + 0xf0 ]
mov rdi, r10
adox rdi, r11
adcx r12, [ rsp + 0x118 ]
setc r15b
clc
adcx r10, rdx
mov r10, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1b0 ], r8
mov byte [ rsp + 0x1b8 ], r15b
mulx r15, r8, r10
adcx r14, r13
adcx rdi, rcx
adox r8, r11
mov r13, 0x7bc65c783158aea3 
mulx r11, rcx, r13
adcx r8, r9
adox rcx, r15
mov r9, 0x6cfc5fd681c52056 
mulx r13, r15, r9
adcx rcx, rax
adox r15, r11
adcx r15, rbp
mov rax, 0x2341f27177344 
mulx r11, rbp, rax
adox rbp, r13
adcx rbp, rbx
mov rdx, 0x0 
adox r11, rdx
adcx r11, r12
movzx rbx, byte [ rsp + 0x1b8 ]
adc rbx, 0x0
add r14, [ rsp - 0x48 ]
adcx rdi, [ rsp + 0x48 ]
mov r12, 0x7bc65c783158aea3 
mov rdx, r14
mulx r13, r14, r12
adcx r8, [ rsp + 0x40 ]
mov rax, 0xffffffffffffffff 
mulx r9, r12, rax
mov [ rsp + 0x1c0 ], r13
mulx r13, rax, r10
adcx rcx, [ rsp + 0x8 ]
adcx r15, [ rsp + 0x10 ]
adcx rbp, [ rsp + 0x78 ]
adcx r11, [ rsp + 0x80 ]
mov r10, r12
mov [ rsp + 0x1c8 ], r11
mov r11, -0x2 
inc r11
adox r10, rdx
adcx rbx, [ rsp + 0xa8 ]
mov r10, r12
setc r11b
clc
adcx r10, r9
adcx r12, r9
adox r10, rdi
adcx rax, r9
adox r12, r8
adox rax, rcx
mov rdi, 0x6cfc5fd681c52056 
mulx r9, r8, rdi
adcx r14, r13
adox r14, r15
adcx r8, [ rsp + 0x1c0 ]
mov r13, 0x2341f27177344 
mulx r15, rcx, r13
adcx rcx, r9
mov rdx, 0x0 
adcx r15, rdx
adox r8, rbp
clc
adcx r10, [ rsp - 0x20 ]
mov rbp, 0x7bc65c783158aea3 
mov rdx, r10
mulx r9, r10, rbp
adcx r12, [ rsp + 0x38 ]
adox rcx, [ rsp + 0x1c8 ]
adox r15, rbx
adcx rax, [ rsp + 0x58 ]
mov rbx, 0xffffffffffffffff 
mulx rbp, r13, rbx
adcx r14, [ rsp + 0x180 ]
adcx r8, [ rsp + 0x198 ]
adcx rcx, [ rsp + 0x190 ]
adcx r15, [ rsp + 0x188 ]
movzx rdi, r11b
mov rbx, 0x0 
adox rdi, rbx
mov r11, r13
mov [ rsp + 0x1d0 ], r15
mov r15, -0x3 
inc r15
adox r11, rdx
adcx rdi, [ rsp + 0x1b0 ]
mov r11, r13
setc r15b
clc
adcx r11, rbp
adcx r13, rbp
adox r11, r12
adox r13, rax
mov r12, 0xfdc1767ae2ffffff 
mulx rbx, rax, r12
adcx rax, rbp
adox rax, r14
adcx r10, rbx
adox r10, r8
mov rbp, 0x6cfc5fd681c52056 
mulx r8, r14, rbp
adcx r14, r9
adox r14, rcx
mov r9, 0x2341f27177344 
mulx rbx, rcx, r9
adcx rcx, r8
adox rcx, [ rsp + 0x1d0 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rbx, rdi
clc
adcx r11, [ rsp + 0xf8 ]
adcx r13, [ rsp + 0x158 ]
adcx rax, [ rsp + 0x150 ]
adcx r10, [ rsp + 0x148 ]
movzx rdi, r15b
adox rdi, rdx
mov rdx, r11
mulx r15, r11, r12
adcx r14, [ rsp + 0x140 ]
adcx rcx, [ rsp + 0x168 ]
mov r8, 0xffffffffffffffff 
mulx rbp, r9, r8
adcx rbx, [ rsp + 0x170 ]
mov r12, r9
mov r8, -0x2 
inc r8
adox r12, rdx
adcx rdi, [ rsp + 0x178 ]
mov r12, r9
setc r8b
clc
adcx r12, rbp
adcx r9, rbp
adox r12, r13
adox r9, rax
adcx r11, rbp
mov r13, 0x7bc65c783158aea3 
mulx rbp, rax, r13
adcx rax, r15
adox r11, r10
adox rax, r14
mov r10, 0x6cfc5fd681c52056 
mulx r14, r15, r10
adcx r15, rbp
adox r15, rcx
mov rcx, 0x2341f27177344 
mulx r13, rbp, rcx
adcx rbp, r14
mov rdx, 0x0 
adcx r13, rdx
clc
adcx r12, [ rsp + 0x20 ]
adcx r9, [ rsp + 0x18 ]
mov r14, 0xffffffffffffffff 
mov rdx, r12
mulx rcx, r12, r14
adcx r11, [ rsp + 0x30 ]
adcx rax, [ rsp + 0x28 ]
adox rbp, rbx
adcx r15, [ rsp + 0x128 ]
adox r13, rdi
movzx rbx, r8b
mov rdi, 0x0 
adox rbx, rdi
adcx rbp, [ rsp + 0x138 ]
adcx r13, [ rsp + 0x130 ]
mulx rdi, r8, r10
mov r10, r12
mov r14, -0x2 
inc r14
adox r10, rdx
adcx rbx, [ rsp + 0x160 ]
mov r10, r12
setc r14b
clc
adcx r10, rcx
adcx r12, rcx
adox r10, r9
adox r12, r11
mov r9, 0xfdc1767ae2ffffff 
mov [ rsp + 0x1d8 ], r12
mulx r12, r11, r9
adcx r11, rcx
adox r11, rax
mov rcx, 0x7bc65c783158aea3 
mulx r9, rax, rcx
adcx rax, r12
adcx r8, r9
adox rax, r15
adox r8, rbp
mov r15, 0x2341f27177344 
mulx r12, rbp, r15
adcx rbp, rdi
adox rbp, r13
mov rdx, 0x0 
adcx r12, rdx
adox r12, rbx
movzx r13, r14b
adox r13, rdx
mov rdi, r10
mov r14, 0xffffffffffffffff 
sub rdi, r14
mov rbx, [ rsp + 0x1d8 ]
sbb rbx, r14
mov r9, r11
sbb r9, r14
mov rdx, rax
mov r15, 0xfdc1767ae2ffffff 
sbb rdx, r15
mov r15, r8
sbb r15, rcx
mov rcx, rbp
mov r14, 0x6cfc5fd681c52056 
sbb rcx, r14
mov r14, r12
mov [ rsp + 0x1e0 ], r9
mov r9, 0x2341f27177344 
sbb r14, r9
sbb r13, 0x00000000
cmovc r14, r12
cmovc rcx, rbp
cmovc rdx, rax
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], rdx
cmovc r15, r8
mov [ r13 + 0x30 ], r14
cmovc rdi, r10
cmovc rbx, [ rsp + 0x1d8 ]
mov [ r13 + 0x8 ], rbx
mov [ r13 + 0x28 ], rcx
mov r10, [ rsp + 0x1e0 ]
cmovc r10, r11
mov [ r13 + 0x10 ], r10
mov [ r13 + 0x20 ], r15
mov [ r13 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 616
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.8821
; seed 4312894110007884 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11237650 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=23, initial num_batches=31): 214420 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0190805017063176
; number reverted permutation / tried permutation: 69557 / 90034 =77.256%
; number reverted decision / tried decision: 62078 / 89965 =69.002%
; validated in 457.773s
