SECTION .text
	GLOBAL fiat_p434_square
fiat_p434_square:
sub rsp, 600
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x30 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
test al, al
adox rax, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rax
mulx rax, rbx, [ rsi + 0x10 ]
adox rbx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r10, [ rsi + 0x20 ]
adox r14, rax
adox r10, r15
mov rdx, [ rsi + 0x28 ]
mulx rax, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r14
mulx r14, r10, rdx
adcx r12, r14
adox r15, rbx
adox r8, rax
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, [ rsi + 0x0 ]
adcx rbx, r13
mov rdx, [ rsi + 0x20 ]
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r9
mov [ rsp - 0x8 ], r8
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, -0x2 
inc rdx
adox r13, rdi
adcx r9, rax
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, [ rsi + 0x20 ]
adcx rax, r8
adcx r11, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, r8, [ rsi + 0x20 ]
adox r8, r14
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x10 ], r8
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], r15
mulx r15, r13, [ rsi + 0x30 ]
adcx r13, rcx
setc dl
clc
adcx r14, rbp
movzx rcx, dl
lea rcx, [ rcx + r15 ]
mov rdx, [ rsi + 0x30 ]
mulx r15, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rcx
mulx rcx, r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r15
mov [ rsp + 0x40 ], r13
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], r11
mulx r11, r15, [ rsi + 0x8 ]
adcx rbp, r8
setc dl
clc
adcx r15, r13
adcx r14, r11
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mulx r11, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], r15
mulx r15, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x78 ], r8b
mov [ rsp + 0x80 ], rax
mulx rax, r8, [ rsi + 0x8 ]
adcx r13, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r13
mulx r13, rcx, [ rsi + 0x18 ]
adox rbp, rdi
setc dl
clc
adcx r8, r14
mov dil, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], rbp
mulx rbp, r14, rdx
adox r14, r15
adcx rcx, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, r15, rdx
adcx r15, r13
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x98 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], rcx
mulx rcx, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r9
mulx r9, r8, [ rsi + 0x28 ]
adox r8, rbp
adcx r15, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, rbp, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc0 ], r8
mov [ rsp + 0xc8 ], r15
mulx r15, r8, [ rsi + 0x10 ]
adox r13, r9
adcx rbp, rcx
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rsi + 0x30 ]
adcx rcx, rax
mov rdx, 0x0 
adox r14, rdx
adc r9, 0x0
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0xd0 ], r14
mulx r14, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xd8 ], r13
mov [ rsp + 0xe0 ], r9
mulx r9, r13, [ rsi + 0x10 ]
add dil, 0xFF
adcx r11, r8
adcx r13, r15
mov rdx, 0x7bc65c783158aea3 
mulx r8, rdi, r10
adcx rax, r9
mov r15, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, r15
mov r15, r10
adox r15, r9
mov [ rsp + 0xe8 ], rcx
mov rcx, 0x6cfc5fd681c52056 
mov [ rsp + 0xf0 ], rbp
mov [ rsp + 0xf8 ], rax
mulx rax, rbp, rcx
mov rcx, 0xfdc1767ae2ffffff 
mov [ rsp + 0x100 ], r13
mov [ rsp + 0x108 ], r11
mulx r11, r13, rcx
mov rcx, r10
adox rcx, r9
adox r13, r9
adox rdi, r11
adox rbp, r8
mov r8, 0x0 
adcx r14, r8
clc
adcx r10, rdx
adcx r15, r12
mov r10, 0x2341f27177344 
mulx r9, r12, r10
adox r12, rax
adcx rcx, rbx
adcx r13, [ rsp + 0xb8 ]
adcx rdi, [ rsp + 0x80 ]
adcx rbp, [ rsp + 0x50 ]
adox r9, r8
mov rdx, [ rsi + 0x30 ]
mulx rax, rbx, rdx
adcx r12, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, [ rsi + 0x30 ]
movzx rdx, byte [ rsp + 0x78 ]
mov r10, 0x0 
dec r10
adox rdx, r10
adox r11, [ rsp + 0x38 ]
adcx r9, [ rsp + 0x30 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x110 ], r11
mulx r11, r10, [ rsi + 0x30 ]
setc dl
clc
adcx r15, [ rsp + 0x8 ]
adox r10, r8
adcx rcx, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x28 ]
adcx rdi, [ rsp - 0x18 ]
adcx rbp, [ rsp - 0x20 ]
adcx r12, [ rsp + 0x0 ]
mov r8b, dl
mov rdx, [ rsi + 0x30 ]
mov [ rsp + 0x118 ], r10
mov [ rsp + 0x120 ], r14
mulx r14, r10, [ rsi + 0x28 ]
adox r10, r11
adox rbx, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x128 ], rbx
mov [ rsp + 0x130 ], r10
mulx r10, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x138 ], r11
mov [ rsp + 0x140 ], r12
mulx r12, r11, [ rsi + 0x30 ]
seto dl
mov [ rsp + 0x148 ], rbp
mov rbp, -0x2 
inc rbp
adox rbx, r14
adcx r9, [ rsp - 0x8 ]
movzx r8, r8b
movzx r14, r8b
adcx r14, [ rsp - 0x10 ]
movzx r8, dl
lea r8, [ r8 + rax ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, rax, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x150 ], r8
mov [ rsp + 0x158 ], rbx
mulx rbx, r8, [ rsi + 0x10 ]
adox r8, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x160 ], r8
mulx r8, r10, [ rsi + 0x18 ]
adox r10, rbx
adox r8, [ rsp - 0x38 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x168 ], r8
mulx r8, rbx, r15
mov rdx, rbx
mov [ rsp + 0x170 ], r10
setc r10b
clc
adcx rdx, r8
adox rax, [ rsp - 0x48 ]
adox r11, rbp
mov rbp, rbx
mov [ rsp + 0x178 ], r11
seto r11b
mov [ rsp + 0x180 ], rax
mov rax, -0x2 
inc rax
adox rbp, r15
adcx rbx, r8
adox rdx, rcx
mov rbp, 0xfdc1767ae2ffffff 
xchg rdx, r15
mulx rax, rcx, rbp
movzx rbp, r11b
lea rbp, [ rbp + r12 ]
adcx rcx, r8
mov r12, 0x7bc65c783158aea3 
mulx r11, r8, r12
adox rbx, r13
adox rcx, rdi
adcx r8, rax
mov r13, 0x6cfc5fd681c52056 
mulx rax, rdi, r13
mov r13, 0x2341f27177344 
mov [ rsp + 0x188 ], rbp
mulx rbp, r12, r13
adox r8, [ rsp + 0x148 ]
adcx rdi, r11
adox rdi, [ rsp + 0x140 ]
adcx r12, rax
mov rdx, 0x0 
adcx rbp, rdx
adox r12, r9
adox rbp, r14
clc
adcx r15, [ rsp + 0x48 ]
adcx rbx, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0x60 ]
mov r9, 0xfdc1767ae2ffffff 
mov rdx, r15
mulx r14, r15, r9
movzx r11, r10b
mov rax, 0x0 
adox r11, rax
adcx r8, [ rsp + 0x88 ]
adcx rdi, [ rsp + 0x108 ]
mov r10, 0xffffffffffffffff 
mulx r13, rax, r10
adcx r12, [ rsp + 0x100 ]
mov r9, rax
mov r10, -0x2 
inc r10
adox r9, r13
mov r10, rax
adox r10, r13
mov [ rsp + 0x190 ], r11
setc r11b
clc
adcx rax, rdx
adcx r9, rbx
adcx r10, rcx
mov rax, 0x7bc65c783158aea3 
mulx rcx, rbx, rax
adox r15, r13
adcx r15, r8
adox rbx, r14
adcx rbx, rdi
mov r14, 0x6cfc5fd681c52056 
mulx rdi, r8, r14
mov r13, 0x2341f27177344 
mulx rax, r14, r13
adox r8, rcx
adox r14, rdi
adcx r8, r12
mov rdx, 0x0 
adox rax, rdx
mov r12, -0x3 
inc r12
adox r9, [ rsp + 0x68 ]
adox r10, [ rsp + 0xb0 ]
adox r15, [ rsp + 0xa8 ]
adox rbx, [ rsp + 0xa0 ]
adox r8, [ rsp + 0xc8 ]
mov rcx, 0x6cfc5fd681c52056 
mov rdx, r9
mulx rdi, r9, rcx
mov r12, 0xfdc1767ae2ffffff 
mulx rcx, r13, r12
seto r12b
mov [ rsp + 0x198 ], rdi
mov rdi, 0x0 
dec rdi
movzx r11, r11b
adox r11, rdi
adox rbp, [ rsp + 0xf8 ]
adcx r14, rbp
mov r11, [ rsp + 0x190 ]
adox r11, [ rsp + 0x120 ]
adcx rax, r11
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x1a0 ], r9
mulx r9, rdi, r11
add r12b, 0xFF
adcx r14, [ rsp + 0xf0 ]
adcx rax, [ rsp + 0xe8 ]
mov r12, rdi
adox r12, rdx
movzx rbp, bpl
movzx r12, bpl
adcx r12, [ rsp + 0xe0 ]
mov rbp, rdi
setc r11b
clc
adcx rbp, r9
adcx rdi, r9
adcx r13, r9
adox rbp, r10
adox rdi, r15
adox r13, rbx
setc r10b
clc
adcx rbp, [ rsp + 0x20 ]
mov r15, 0xffffffffffffffff 
xchg rdx, r15
mulx r9, rbx, rbp
adcx rdi, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x10 ]
mov rdx, rbx
mov byte [ rsp + 0x1a8 ], r11b
seto r11b
mov [ rsp + 0x1b0 ], r12
mov r12, -0x2 
inc r12
adox rdx, r9
mov r12, rbx
mov [ rsp + 0x1b8 ], rax
setc al
clc
adcx r12, rbp
adox rbx, r9
adcx rdx, rdi
adcx rbx, r13
mov r12, 0x7bc65c783158aea3 
xchg rdx, r15
mulx r13, rdi, r12
setc r12b
clc
mov [ rsp + 0x1c0 ], rbx
mov rbx, -0x1 
movzx r10, r10b
adcx r10, rbx
adcx rcx, rdi
seto r10b
inc rbx
mov rdi, -0x1 
movzx r11, r11b
adox r11, rdi
adox r8, rcx
mov r11, 0x2341f27177344 
mulx rbx, rcx, r11
adcx r13, [ rsp + 0x1a0 ]
adcx rcx, [ rsp + 0x198 ]
mov rdx, 0x0 
adcx rbx, rdx
adox r13, r14
adox rcx, [ rsp + 0x1b8 ]
adox rbx, [ rsp + 0x1b0 ]
movzx r14, byte [ rsp + 0x1a8 ]
adox r14, rdx
mov rdx, 0xfdc1767ae2ffffff 
mulx r11, rdi, rbp
add al, 0x7F
adox r8, [ rsp + 0x90 ]
adox r13, [ rsp + 0x98 ]
adox rcx, [ rsp + 0xc0 ]
adox rbx, [ rsp + 0xd8 ]
mov rax, -0x1 
movzx r10, r10b
adcx r10, rax
adcx r9, rdi
adox r14, [ rsp + 0xd0 ]
seto r10b
inc rax
mov rdi, -0x1 
movzx r12, r12b
adox r12, rdi
adox r8, r9
mov r12, 0x7bc65c783158aea3 
mov rdx, rbp
mulx r9, rbp, r12
adcx rbp, r11
adox rbp, r13
mov r11, 0x2341f27177344 
mulx rax, r13, r11
mov rdi, 0x6cfc5fd681c52056 
mulx r12, r11, rdi
adcx r11, r9
adcx r13, r12
adox r11, rcx
mov rdx, 0x0 
adcx rax, rdx
clc
adcx r15, [ rsp + 0x138 ]
adox r13, rbx
adox rax, r14
mov rcx, [ rsp + 0x158 ]
adcx rcx, [ rsp + 0x1c0 ]
adcx r8, [ rsp + 0x160 ]
adcx rbp, [ rsp + 0x170 ]
adcx r11, [ rsp + 0x168 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, rbx
movzx r9, r10b
mov r12, 0x0 
adox r9, r12
mov r10, r15
mov rdi, -0x3 
inc rdi
adox r10, r14
adcx r13, [ rsp + 0x180 ]
mov r12, r15
adox r12, r14
adcx rax, [ rsp + 0x178 ]
adcx r9, [ rsp + 0x188 ]
setc dil
clc
adcx r15, rdx
adcx r10, rcx
mov r15, 0xfdc1767ae2ffffff 
mulx rbx, rcx, r15
adcx r12, r8
adox rcx, r14
adcx rcx, rbp
mov r8, 0x7bc65c783158aea3 
mulx r14, rbp, r8
adox rbp, rbx
adcx rbp, r11
mov r11, 0x6cfc5fd681c52056 
mulx r15, rbx, r11
adox rbx, r14
adcx rbx, r13
mov r13, 0x2341f27177344 
mulx r11, r14, r13
adox r14, r15
mov rdx, 0x0 
adox r11, rdx
adcx r14, rax
adcx r11, r9
movzx rax, dil
adc rax, 0x0
add r10, [ rsp - 0x40 ]
adcx r12, [ rsp + 0x28 ]
mov rdi, 0xfdc1767ae2ffffff 
mov rdx, r10
mulx r9, r10, rdi
adcx rcx, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x110 ]
adcx rbx, [ rsp + 0x118 ]
adcx r14, [ rsp + 0x130 ]
adcx r11, [ rsp + 0x128 ]
mov r15, 0xffffffffffffffff 
mulx rdi, r13, r15
adcx rax, [ rsp + 0x150 ]
mov r15, r13
mov r8, -0x2 
inc r8
adox r15, rdx
mov r15, r13
setc r8b
clc
adcx r15, rdi
adcx r13, rdi
adox r15, r12
adcx r10, rdi
adox r13, rcx
adox r10, rbp
mov r12, 0x7bc65c783158aea3 
mulx rbp, rcx, r12
adcx rcx, r9
adox rcx, rbx
mov r9, 0x6cfc5fd681c52056 
mulx rdi, rbx, r9
adcx rbx, rbp
adox rbx, r14
mov r14, 0x2341f27177344 
mulx r9, rbp, r14
adcx rbp, rdi
mov rdx, 0x0 
adcx r9, rdx
adox rbp, r11
adox r9, rax
movzx r11, r8b
adox r11, rdx
mov r8, r15
mov rax, 0xffffffffffffffff 
sub r8, rax
mov rdi, r13
sbb rdi, rax
mov rdx, r10
sbb rdx, rax
mov r14, rcx
mov rax, 0xfdc1767ae2ffffff 
sbb r14, rax
mov rax, rbx
sbb rax, r12
mov r12, rbp
mov [ rsp + 0x1c8 ], r14
mov r14, 0x6cfc5fd681c52056 
sbb r12, r14
mov r14, r9
mov [ rsp + 0x1d0 ], rdi
mov rdi, 0x2341f27177344 
sbb r14, rdi
sbb r11, 0x00000000
cmovc rdx, r10
cmovc r14, r9
cmovc r12, rbp
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x28 ], r12
mov [ r11 + 0x10 ], rdx
cmovc rax, rbx
cmovc r8, r15
mov [ r11 + 0x0 ], r8
mov [ r11 + 0x20 ], rax
mov r15, [ rsp + 0x1d0 ]
cmovc r15, r13
mov [ r11 + 0x8 ], r15
mov r13, [ rsp + 0x1c8 ]
cmovc r13, rcx
mov [ r11 + 0x18 ], r13
mov [ r11 + 0x30 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.8587
; seed 4206328996079927 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7572281 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=27, initial num_batches=31): 147260 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.019447244496077206
; number reverted permutation / tried permutation: 74158 / 90272 =82.150%
; number reverted decision / tried decision: 64012 / 89727 =71.341%
; validated in 388.394s
