SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 600
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], rbp
mulx rbp, rcx, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rdi
mulx rdi, rbx, [ rsi + 0x10 ]
add rcx, r12
mov rdx, 0xffffffff00000000 
mulx r12, rcx, r14
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r15
mulx r15, rbx, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r11, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r15
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r15
mulx r15, rdi, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r15
mulx r15, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], r9
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x30 ], r11
mov [ rsp + 0x38 ], r8
mulx r8, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r8
mov [ rsp + 0x48 ], r11
mulx r11, r8, [ rsi + 0x8 ]
setc dl
clc
adcx rax, r9
mov r9b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], rax
mulx rax, r11, [ rsi + 0x18 ]
adcx r8, r10
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x60 ], rax
mulx rax, r10, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x68 ], rax
mov rax, -0x2 
inc rax
adox rcx, rbp
mov rbp, 0xfffffffffffffffe 
xchg rdx, rbp
mov [ rsp + 0x70 ], r10
mulx r10, rax, r14
adox rax, r12
mov r14, rdi
adox r14, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rsi + 0x0 ]
setc dl
clc
adcx rbx, r15
setc r15b
clc
adcx r12, r13
adcx r10, [ rsp + 0x38 ]
mov r13b, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x78 ], rbx
mov byte [ rsp + 0x80 ], r15b
mulx r15, rbx, [ rsi + 0x0 ]
mov rdx, [ rsp + 0x28 ]
adcx rdx, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x30 ]
mov byte [ rsp + 0x88 ], bpl
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r11
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, rdi
adox rdx, [ rsp + 0x18 ]
mov [ rsp + 0xa0 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], r8
mov byte [ rsp + 0xb0 ], r13b
mulx r13, r8, [ rsi + 0x0 ]
adcx r8, r15
adox rdi, [ rsp + 0x18 ]
mov rdx, 0x0 
adcx r13, rdx
mov r15, [ rsp + 0x18 ]
adox r15, rdx
add r9b, 0x7F
adox r12, rcx
adox rax, r10
adox r14, rbp
adcx r12, [ rsp + 0x30 ]
adcx rax, [ rsp + 0x58 ]
adox r11, rbx
adox rdi, r8
adox r15, r13
mov r9, [ rsp + 0x50 ]
seto cl
movzx r10, byte [ rsp + 0xb0 ]
dec rdx
adox r10, rdx
adox r9, [ rsp + 0x98 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r10, [ rsi + 0x8 ]
mov rdx, 0x100000001 
mulx r8, rbx, r12
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r13, r8, rbx
adcx r14, [ rsp + 0x90 ]
adcx r9, r11
adox r10, [ rsp + 0x60 ]
adox rbp, [ rsp - 0x38 ]
mov r11, [ rsp - 0x40 ]
mov rdx, 0x0 
adox r11, rdx
adcx r10, rdi
mov rdi, 0xfffffffffffffffe 
mov rdx, rbx
mov [ rsp + 0xb8 ], r10
mulx r10, rbx, rdi
adcx rbp, r15
mov r15, 0xffffffff 
mov [ rsp + 0xc0 ], rbp
mulx rbp, rdi, r15
mov r15, -0x2 
inc r15
adox rdi, r12
mov rdi, 0xffffffff00000000 
mulx r15, r12, rdi
movzx rdx, cl
adcx rdx, r11
setc cl
clc
adcx r12, rbp
adcx rbx, r15
mov r11, r8
adcx r11, r10
mov r10, r8
adcx r10, r13
adcx r8, r13
adox r12, rax
mov rax, 0x0 
adcx r13, rax
adox rbx, r14
adox r11, r9
clc
adcx r12, [ rsp - 0x28 ]
adox r10, [ rsp + 0xb8 ]
mov r14, 0x100000001 
xchg rdx, r14
mulx rbp, r9, r12
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r15, rbp, r9
adox r8, [ rsp + 0xc0 ]
mov rdx, rdi
mulx rax, rdi, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], r15
mulx r15, r8, [ rsi + 0x18 ]
adox r13, r14
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], r13
mulx r13, r14, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], rbp
mov [ rsp + 0xe8 ], r13
mulx r13, rbp, rdx
movzx rdx, cl
mov [ rsp + 0xf0 ], r14
mov r14, 0x0 
adox rdx, r14
movzx rcx, byte [ rsp + 0x88 ]
dec r14
adox rcx, r14
adox rbp, [ rsp - 0x48 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xf8 ], rax
mulx rax, r14, [ rsi + 0x20 ]
adox r8, r13
adox r14, r15
adcx rbx, [ rsp + 0x10 ]
adcx rbp, r11
adox rax, [ rsp - 0x8 ]
adcx r8, r10
mov rdx, [ rsp - 0x10 ]
mov r11, 0x0 
adox rdx, r11
mov r10, 0xffffffff 
xchg rdx, r9
mulx r13, r15, r10
mov rdx, -0x3 
inc rdx
adox rdi, r13
mov r13, [ rsp + 0xf8 ]
adox r13, [ rsp + 0xf0 ]
mov r11, [ rsp + 0xe8 ]
adox r11, [ rsp + 0xe0 ]
mov rdx, [ rsp + 0xd0 ]
mov r10, rdx
adox r10, [ rsp + 0xe0 ]
mov [ rsp + 0x100 ], r10
mov r10, rdx
adox r10, [ rsp + 0xe0 ]
mov [ rsp + 0x108 ], r10
mov r10, 0x0 
adox rdx, r10
mov [ rsp + 0x110 ], rdx
mov rdx, -0x3 
inc rdx
adox r15, r12
adox rdi, rbx
adox r13, rbp
adcx r14, [ rsp + 0xc8 ]
adox r11, r8
mov rdx, [ rsi + 0x18 ]
mulx r12, r15, [ rsi + 0x0 ]
adcx rax, [ rsp + 0xd8 ]
adcx r9, rcx
adox r14, [ rsp + 0x100 ]
adox rax, [ rsp + 0x108 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, rdx
setc dl
clc
adcx r15, rdi
mov rdi, 0x100000001 
xchg rdx, rdi
mov [ rsp + 0x118 ], rax
mulx rax, r10, r15
adox r9, [ rsp + 0x110 ]
mov rax, 0xfffffffffffffffe 
mov rdx, r10
mov [ rsp + 0x120 ], r9
mulx r9, r10, rax
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x128 ], dil
mov [ rsp + 0x130 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], r10
mulx r10, r9, rax
seto dl
mov [ rsp + 0x148 ], r10
mov r10, -0x2 
inc r10
adox rcx, r12
adcx rcx, r13
adox rdi, rbx
adox rbp, r8
adcx rdi, r11
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, [ rsi + 0x20 ]
adcx rbp, r14
mov rdx, 0xffffffff 
mulx rbx, r14, rax
seto r8b
inc r10
adox r14, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x150 ], r15
mulx r15, r10, [ rsi + 0x20 ]
setc dl
clc
adcx r15, [ rsp + 0xa8 ]
mov [ rsp + 0x158 ], r15
mov r15, 0xffffffffffffffff 
xchg rdx, r15
mov [ rsp + 0x160 ], r14
mov [ rsp + 0x168 ], r12
mulx r12, r14, rax
seto al
mov rdx, -0x2 
inc rdx
adox r9, rbx
mov rbx, [ rsp + 0x148 ]
adox rbx, [ rsp + 0x140 ]
mov rdx, r14
adox rdx, [ rsp + 0x138 ]
mov byte [ rsp + 0x170 ], r15b
mov r15, r14
adox r15, r12
adox r14, r12
adcx r11, [ rsp + 0xa0 ]
mov [ rsp + 0x178 ], r11
seto r11b
mov [ rsp + 0x180 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rax, al
adox rax, r14
adox rcx, r9
mov rax, rdx
mov rdx, [ rsi + 0x28 ]
mulx r14, r9, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x188 ], r15
mov r15, -0x2 
inc r15
adox r10, rcx
setc cl
clc
movzx rdx, dl
adcx rdx, r15
adcx rdi, rbx
adcx rax, rbp
mov rbp, [ rsp + 0x130 ]
seto bl
inc r15
mov rdx, -0x1 
movzx r8, r8b
adox r8, rdx
adox rbp, [ rsp + 0x48 ]
adox r9, [ rsp + 0x40 ]
movzx r8, r11b
lea r8, [ r8 + r12 ]
adox r14, r15
movzx r12, r13b
movzx r11, byte [ rsp + 0x128 ]
lea r12, [ r12 + r11 ]
movzx r11, byte [ rsp + 0x170 ]
inc rdx
mov r15, -0x1 
adox r11, r15
adox rbp, [ rsp + 0x118 ]
adox r9, [ rsp + 0x120 ]
mov r13, 0x100000001 
mov rdx, r10
mulx r11, r10, r13
mov r11, 0xffffffff 
xchg rdx, r10
mulx r13, r15, r11
adox r14, r12
adcx rbp, [ rsp + 0x188 ]
seto r12b
mov r11, -0x2 
inc r11
adox r15, r10
adcx r9, [ rsp + 0x180 ]
mov r15, [ rsp + 0x160 ]
seto r10b
inc r11
mov r11, -0x1 
movzx rcx, cl
adox rcx, r11
adox r15, [ rsp + 0x168 ]
adcx r8, r14
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r14, rdx
adox r14, [ rsp + 0x150 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x190 ], r8
mov [ rsp + 0x198 ], r14
mulx r14, r8, rdx
adox r11, [ rsp + 0x8 ]
mov rdx, [ rsp + 0x0 ]
mov [ rsp + 0x1a0 ], r14
mov r14, 0x0 
adox rdx, r14
movzx r14, r12b
adc r14, 0x0
add bl, 0x7F
adox rdi, [ rsp + 0x158 ]
mov rbx, 0xffffffff00000000 
xchg rdx, rbx
mov [ rsp + 0x1a8 ], r8
mulx r8, r12, rcx
adcx r12, r13
adox rax, [ rsp + 0x178 ]
adox r15, rbp
mov r13, 0xfffffffffffffffe 
mov rdx, r13
mulx rbp, r13, rcx
adcx r13, r8
mov r8, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp + 0x1b0 ], rbx
mulx rbx, rcx, r8
mov rdx, rcx
adcx rdx, rbp
mov rbp, rcx
adcx rbp, rbx
adcx rcx, rbx
mov r8, 0x0 
adcx rbx, r8
clc
mov r8, -0x1 
movzx r10, r10b
adcx r10, r8
adcx rdi, r12
adox r9, [ rsp + 0x198 ]
adcx r13, rax
adox r11, [ rsp + 0x190 ]
adcx rdx, r15
adox r14, [ rsp + 0x1b0 ]
seto r10b
inc r8
adox rdi, [ rsp + 0x20 ]
mov r12, 0x100000001 
xchg rdx, rdi
mulx r15, rax, r12
mov r15, 0xffffffffffffffff 
xchg rdx, r15
mulx r12, r8, rax
adcx rbp, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x1b8 ], r12
mulx r12, r9, [ rsi + 0x28 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1c0 ], r8
mov [ rsp + 0x1c8 ], rbp
mulx rbp, r8, rax
adcx rcx, r11
adcx rbx, r14
mov rdx, [ rsi + 0x28 ]
mulx r14, r11, [ rsi + 0x10 ]
movzx rdx, r10b
mov [ rsp + 0x1d0 ], r8
mov r8, 0x0 
adcx rdx, r8
movzx r10, byte [ rsp + 0x80 ]
clc
mov r8, -0x1 
adcx r10, r8
adcx r11, [ rsp - 0x18 ]
adcx r9, r14
adcx r12, [ rsp + 0x70 ]
adox r13, [ rsp + 0x78 ]
adox r11, rdi
adox r9, [ rsp + 0x1c8 ]
mov r10, [ rsp + 0x68 ]
adcx r10, [ rsp + 0x1a8 ]
adox r12, rcx
adox r10, rbx
mov rdi, [ rsp + 0x1a0 ]
mov rcx, 0x0 
adcx rdi, rcx
mov rbx, 0xfffffffffffffffe 
xchg rdx, rbx
mulx rcx, r14, rax
adox rdi, rbx
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r8, rbx, rax
clc
adcx rbx, rbp
seto al
mov rbp, -0x2 
inc rbp
adox r15, [ rsp + 0x1d0 ]
adcx r14, r8
adcx rcx, [ rsp + 0x1c0 ]
mov r15, [ rsp + 0x1c0 ]
mov r8, r15
adcx r8, [ rsp + 0x1b8 ]
adox rbx, r13
adcx r15, [ rsp + 0x1b8 ]
adox r14, r11
adox rcx, r9
adox r8, r12
adox r15, r10
mov r13, [ rsp + 0x1b8 ]
mov r11, 0x0 
adcx r13, r11
adox r13, rdi
movzx r9, al
adox r9, r11
mov r12, rbx
mov r10, 0xffffffff 
sub r12, r10
mov rax, r14
sbb rax, rdx
mov rdi, rcx
mov r11, 0xfffffffffffffffe 
sbb rdi, r11
mov rbp, r8
mov rdx, 0xffffffffffffffff 
sbb rbp, rdx
mov r10, r15
sbb r10, rdx
mov r11, r13
sbb r11, rdx
sbb r9, 0x00000000
cmovc r10, r15
cmovc rdi, rcx
cmovc rbp, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rdi
mov [ r9 + 0x20 ], r10
cmovc rax, r14
cmovc r12, rbx
cmovc r11, r13
mov [ r9 + 0x28 ], r11
mov [ r9 + 0x18 ], rbp
mov [ r9 + 0x0 ], r12
mov [ r9 + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1658
; seed 2890541125721448 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4089642 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=64, initial num_batches=31): 109598 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02679892274189281
; number reverted permutation / tried permutation: 61575 / 89596 =68.725%
; number reverted decision / tried decision: 53258 / 90403 =58.912%
; validated in 24.712s
