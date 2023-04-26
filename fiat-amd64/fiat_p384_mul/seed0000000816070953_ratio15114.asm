SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 624
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov [ rsp - 0x60 ], r14
mov r14, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
test al, al
adox r10, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r10
mulx r10, rbp, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r10
mulx r10, rbp, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rdi
mulx rdi, r11, [ rax + 0x20 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r11
mulx r11, rdi, r9
adcx r12, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, r9, [ rax + 0x28 ]
adcx rbp, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r11
mulx r11, r13, [ rax + 0x10 ]
mov rdx, r14
adcx rdx, r10
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r13
mulx r13, r11, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x20 ], r9
mov r9, -0x2 
inc r9
adox r11, r8
mov r8b, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, r14
adcx rdx, r15
adcx r14, r15
adox r9, r13
mov r13, 0x0 
adcx r15, r13
clc
adcx rdi, rcx
mov rdi, rdx
mov rdx, [ rax + 0x18 ]
mulx r13, rcx, [ rsi + 0x0 ]
adox rcx, rbx
adcx r12, r11
adcx rbp, r9
mov rdx, [ rsi + 0x20 ]
mulx rbx, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r9, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x38 ], r11
mov byte [ rsp + 0x40 ], r8b
mulx r8, r11, [ rsi + 0x0 ]
adcx r10, rcx
adox r11, r13
mov rdx, [ rax + 0x20 ]
mulx rcx, r13, [ rsi + 0x8 ]
adox r9, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x48 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, 0x0 
adox rbx, rdx
mov [ rsp + 0x50 ], r10
mov r10, -0x3 
inc r10
adox r8, r12
mov rdx, [ rax + 0x20 ]
mulx r10, r12, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0x58 ], r10
mov [ rsp + 0x60 ], r12
mulx r12, r10, r8
adcx rdi, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, r12, [ rax + 0x10 ]
adcx r14, r9
adcx r15, rbx
setc dl
clc
adcx rcx, [ rsp + 0x28 ]
adcx r12, [ rsp - 0x10 ]
adox rcx, rbp
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, [ rax + 0x18 ]
adcx r9, r11
adcx r13, rbx
adox r12, [ rsp + 0x50 ]
mov rdx, 0xffffffff 
mulx rbx, r11, r10
adox r9, rdi
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x68 ], bpl
mulx rbp, rdi, [ rax + 0x28 ]
adcx rdi, [ rsp + 0x48 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r15
mulx r15, rdi, r10
mov rdx, 0x0 
adcx rbp, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x80 ], rbp
mov [ rsp + 0x88 ], r13
mulx r13, rbp, r10
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x90 ], r14
mov [ rsp + 0x98 ], r9
mulx r9, r14, r10
clc
adcx rdi, rbx
mov rdx, [ rax + 0x8 ]
mulx rbx, r10, [ rsi + 0x10 ]
adcx r14, r15
mov rdx, rbp
adcx rdx, r9
mov r15, rbp
adcx r15, r13
adcx rbp, r13
setc r9b
clc
adcx r11, r8
adcx rdi, rcx
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, [ rax + 0x18 ]
adcx r14, r12
adcx r11, [ rsp + 0x98 ]
mov rdx, [ rsp + 0x90 ]
adox rdx, [ rsp + 0x88 ]
mov r12, [ rsp + 0x78 ]
adox r12, [ rsp + 0x70 ]
adcx r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xa0 ], r15
mov [ rsp + 0xa8 ], r11
mulx r11, r15, [ rax + 0x18 ]
adcx rbp, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
movzx rdx, r9b
lea rdx, [ rdx + r13 ]
mov r13, [ rsp + 0x80 ]
movzx r9, byte [ rsp + 0x68 ]
adox r9, r13
adcx rdx, r9
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0xb8 ], r14
mulx r14, r9, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0xc0 ], r13
seto r13b
mov [ rsp + 0xc8 ], rcx
movzx rcx, byte [ rsp + 0x40 ]
mov [ rsp + 0xd0 ], r8
mov r8, 0x0 
dec r8
adox rcx, r8
adox rdx, [ rsp - 0x38 ]
adox r15, [ rsp - 0x40 ]
adox r12, r11
movzx rcx, r13b
mov r11, 0x0 
adcx rcx, r11
mov r13, rdx
mov rdx, [ rax + 0x10 ]
mulx r8, r11, [ rsi + 0x10 ]
clc
adcx r10, r14
adcx r11, rbx
adox rbp, [ rsp + 0x20 ]
mov rdx, [ rax + 0x28 ]
mulx r14, rbx, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0xd8 ], rbp
mov rbp, -0x2 
inc rbp
adox r9, rdi
movzx rdi, dl
mov rbp, [ rsp + 0x8 ]
lea rdi, [ rdi + rbp ]
mov rbp, 0x100000001 
mov rdx, r9
mov [ rsp + 0xe0 ], rdi
mulx rdi, r9, rbp
adcx r8, [ rsp + 0xd0 ]
mov rdi, [ rsp + 0xc8 ]
adcx rdi, [ rsp + 0x0 ]
adox r10, [ rsp + 0xb8 ]
mov rbp, 0xffffffff 
xchg rdx, r9
mov [ rsp + 0xe8 ], r12
mov [ rsp + 0xf0 ], r15
mulx r15, r12, rbp
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0xf8 ], r13
mov [ rsp + 0x100 ], r10
mulx r10, r13, rbp
adox r11, [ rsp + 0xa8 ]
adox r8, [ rsp + 0xa0 ]
adox rdi, [ rsp + 0xb0 ]
adcx rbx, [ rsp - 0x8 ]
mov rbp, 0x0 
adcx r14, rbp
adox rbx, [ rsp + 0xc0 ]
mov rbp, 0xffffffff00000000 
mov [ rsp + 0x108 ], rbx
mov [ rsp + 0x110 ], rdi
mulx rdi, rbx, rbp
adox r14, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp + 0x118 ], r14
mulx r14, rbp, rcx
clc
adcx rbx, r15
adcx r13, rdi
mov rdx, rbp
adcx rdx, r10
mov r15, rbp
adcx r15, r14
adcx rbp, r14
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x120 ], rdi
mov [ rsp + 0x128 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
setc dl
clc
adcx r12, r9
adcx rbx, [ rsp + 0x100 ]
adcx r13, r11
adcx r10, r8
adcx r15, [ rsp + 0x110 ]
adcx rbp, [ rsp + 0x108 ]
mov r12b, dl
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x130 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
seto dl
mov [ rsp + 0x138 ], rdi
mov rdi, -0x2 
inc rdi
adox r8, [ rsp + 0x128 ]
movzx rdi, r12b
lea rdi, [ rdi + r14 ]
adcx rdi, [ rsp + 0x118 ]
seto r14b
mov r12, -0x2 
inc r12
adox rbx, [ rsp - 0x48 ]
movzx r12, dl
mov [ rsp + 0x140 ], r8
mov r8, 0x0 
adcx r12, r8
adox r13, [ rsp - 0x30 ]
adox r10, [ rsp + 0xf8 ]
adox r15, [ rsp + 0xf0 ]
mov rdx, 0x100000001 
mov [ rsp + 0x148 ], r11
mulx r11, r8, rbx
mov r11, 0xfffffffffffffffe 
mov rdx, r8
mov [ rsp + 0x150 ], r9
mulx r9, r8, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x158 ], rcx
mov byte [ rsp + 0x160 ], r14b
mulx r14, rcx, r11
adox rbp, [ rsp + 0xe8 ]
adox rdi, [ rsp + 0xd8 ]
adox r12, [ rsp + 0xe0 ]
mov r11, 0xffffffff 
mov [ rsp + 0x168 ], r12
mov [ rsp + 0x170 ], rdi
mulx rdi, r12, r11
clc
adcx r12, rbx
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mulx r11, rbx, [ rsi + 0x20 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x178 ], r11
mov [ rsp + 0x180 ], rbx
mulx rbx, r11, r12
setc r12b
clc
adcx r11, rdi
adcx r8, rbx
seto dil
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx r12, r12b
adox r12, rbx
adox r13, r11
mov r12, rcx
adcx r12, r9
mov r9, rcx
adcx r9, r14
adcx rcx, r14
adox r8, r10
adox r12, r15
adox r9, rbp
adox rcx, [ rsp + 0x170 ]
mov r10, [ rsp + 0x158 ]
setc r15b
movzx rbp, byte [ rsp + 0x160 ]
clc
adcx rbp, rbx
adcx r10, [ rsp + 0x150 ]
movzx rbp, r15b
lea rbp, [ rbp + r14 ]
adox rbp, [ rsp + 0x168 ]
seto r14b
inc rbx
adox r13, [ rsp + 0x120 ]
mov rdx, [ rax + 0x18 ]
mulx r15, r11, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x38 ]
adcx rdx, [ rsp + 0x148 ]
adox r8, [ rsp + 0x140 ]
adox r10, r12
adox rdx, r9
mov r12, [ rsp + 0x30 ]
adcx r12, [ rsp + 0x138 ]
mov r9, [ rsp + 0x130 ]
adcx r9, [ rsp + 0x180 ]
mov rbx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x188 ], r10
mov [ rsp + 0x190 ], r8
mulx r8, r10, [ rax + 0x8 ]
adox r12, rcx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x198 ], r12
mulx r12, rcx, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x178 ]
mov [ rsp + 0x1a0 ], rbx
mov rbx, 0x0 
adcx rdx, rbx
clc
adcx r10, [ rsp - 0x20 ]
adcx r8, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x10 ]
adcx r15, [ rsp + 0x60 ]
mov rbx, 0x100000001 
xchg rdx, rbx
mov [ rsp + 0x1a8 ], r15
mov [ rsp + 0x1b0 ], r11
mulx r11, r15, r13
mov r11, 0xfffffffffffffffe 
mov rdx, r11
mov [ rsp + 0x1b8 ], r8
mulx r8, r11, r15
adcx rcx, [ rsp + 0x58 ]
mov rdx, 0x0 
adcx r12, rdx
movzx rdx, r14b
movzx rdi, dil
lea rdx, [ rdx + rdi ]
mov rdi, 0xffffffff 
xchg rdx, rdi
mov [ rsp + 0x1c0 ], r12
mulx r12, r14, r15
adox r9, rbp
mov rbp, 0xffffffff00000000 
mov rdx, r15
mov [ rsp + 0x1c8 ], rcx
mulx rcx, r15, rbp
clc
adcx r14, r13
adox rbx, rdi
seto r14b
mov r13, -0x2 
inc r13
adox r15, r12
adox r11, rcx
mov rdi, 0xffffffffffffffff 
mulx rcx, r12, rdi
adcx r15, [ rsp + 0x190 ]
mov rdx, r12
adox rdx, r8
mov r8, r12
adox r8, rcx
adcx r11, [ rsp + 0x188 ]
adcx rdx, [ rsp + 0x1a0 ]
adcx r8, [ rsp + 0x198 ]
adox r12, rcx
adcx r12, r9
seto r9b
inc r13
adox r15, [ rsp - 0x28 ]
adox r10, r11
adox rdx, [ rsp + 0x1b8 ]
mov r11, 0x100000001 
xchg rdx, r15
mulx rdi, r13, r11
mov rdi, 0xffffffffffffffff 
xchg rdx, rdi
mulx r11, rbp, r13
adox r8, [ rsp + 0x1b0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1d0 ], r12
mov [ rsp + 0x1d8 ], r11
mulx r11, r12, r13
movzx rdx, r9b
lea rdx, [ rdx + rcx ]
seto cl
mov r9, -0x2 
inc r9
adox r12, rdi
adcx rdx, rbx
movzx r12, r14b
mov rbx, 0x0 
adcx r12, rbx
mov r14, 0xffffffff00000000 
xchg rdx, r14
mulx rbx, rdi, r13
mov r9, 0xfffffffffffffffe 
mov rdx, r9
mov [ rsp + 0x1e0 ], r12
mulx r12, r9, r13
clc
adcx rdi, r11
adcx r9, rbx
adox rdi, r10
mov r10, rbp
adcx r10, r12
adox r9, r15
adox r10, r8
mov r15, rbp
adcx r15, [ rsp + 0x1d8 ]
adcx rbp, [ rsp + 0x1d8 ]
mov r13, [ rsp + 0x1d0 ]
setc r8b
clc
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx r13, [ rsp + 0x1a8 ]
movzx rcx, r8b
mov rbx, [ rsp + 0x1d8 ]
lea rcx, [ rcx + rbx ]
adox r15, r13
adcx r14, [ rsp + 0x1c8 ]
mov rbx, [ rsp + 0x1e0 ]
adcx rbx, [ rsp + 0x1c0 ]
adox rbp, r14
adox rcx, rbx
seto r12b
adc r12b, 0x0
movzx r12, r12b
mov r8, rdi
mov r13, 0xffffffff 
sub r8, r13
mov r14, r9
mov rbx, 0xffffffff00000000 
sbb r14, rbx
mov r11, r10
sbb r11, rdx
mov rdx, r15
mov rbx, 0xffffffffffffffff 
sbb rdx, rbx
mov r13, rbp
sbb r13, rbx
mov [ rsp + 0x1e8 ], r8
mov r8, rcx
sbb r8, rbx
movzx rbx, r12b
sbb rbx, 0x00000000
cmovc r8, rcx
cmovc r14, r9
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r14
mov [ rbx + 0x28 ], r8
cmovc r13, rbp
cmovc rdx, r15
mov [ rbx + 0x18 ], rdx
cmovc r11, r10
mov r9, [ rsp + 0x1e8 ]
cmovc r9, rdi
mov [ rbx + 0x10 ], r11
mov [ rbx + 0x20 ], r13
mov [ rbx + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 624
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5114
; seed 1229928336513946 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4799786 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=54, initial num_batches=31): 124353 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025908030066340456
; number reverted permutation / tried permutation: 60625 / 89801 =67.510%
; number reverted decision / tried decision: 45694 / 90198 =50.660%
; validated in 36.851s
