SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 696
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rax + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r11
mulx r11, rcx, r15
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], r8
mulx r8, r10, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r14
mulx r14, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r14
mulx r14, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r12
mov r12, 0xffffffffffffffff 
mov rdx, r12
mov [ rsp + 0x10 ], r13
mulx r13, r12, r15
adcx r10, r11
mov r11, 0xfffffffffffffffe 
mov rdx, r15
mov [ rsp + 0x18 ], r10
mulx r10, r15, r11
adcx r15, r8
mov rdx, r12
adcx rdx, r10
mov r8, r12
adcx r8, r13
mov r10, rdx
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x20 ], r8
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r8
mov [ rsp + 0x30 ], r11
mulx r11, r8, [ rsi + 0x10 ]
adcx r12, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r8
mov [ rsp + 0x40 ], r11
mulx r11, r8, [ rsi + 0x0 ]
adox r9, r14
setc dl
clc
adcx rcx, rbp
adox r8, rbx
adcx rdi, [ rsp + 0x18 ]
movzx rcx, dl
lea rcx, [ rcx + r13 ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, rbx, [ rax + 0x0 ]
adcx r15, r9
mov rdx, [ rax + 0x20 ]
mulx r13, r14, [ rsi + 0x0 ]
adox r14, r11
adcx r10, r8
mov rdx, [ rax + 0x28 ]
mulx r9, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x48 ], rbx
mulx rbx, r8, [ rax + 0x8 ]
adox r11, r13
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x50 ], r10
mulx r10, r13, [ rax + 0x20 ]
mov rdx, 0x0 
adox r9, rdx
mov [ rsp + 0x58 ], r15
mov r15, -0x3 
inc r15
adox r8, rbp
adox rbx, [ rsp + 0x10 ]
mov rbp, [ rsp - 0x18 ]
adox rbp, [ rsp - 0x20 ]
adox r13, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r13
mulx r13, r15, [ rax + 0x8 ]
adcx r14, [ rsp + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], rbp
mov [ rsp + 0x70 ], rbx
mulx rbx, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x78 ], r8
mov [ rsp + 0x80 ], r14
mulx r14, r8, [ rsi + 0x28 ]
adcx r12, r11
adcx rcx, r9
adox r8, r10
setc dl
clc
adcx rdi, [ rsp - 0x30 ]
mov r11, 0x100000001 
xchg rdx, r11
mulx r9, r10, rdi
seto r9b
mov rdx, -0x2 
inc rdx
adox r15, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r8
mov byte [ rsp + 0x90 ], r11b
mulx r11, r8, [ rax + 0x20 ]
adox rbp, r13
adcx r15, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x50 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x98 ], rbp
mulx rbp, r13, r10
movzx rdx, r9b
lea rdx, [ rdx + r14 ]
adox rbx, [ rsp - 0x8 ]
adox r8, [ rsp - 0x10 ]
mov r14, 0xffffffff 
xchg rdx, r10
mov [ rsp + 0xa0 ], r10
mulx r10, r9, r14
adcx rbx, [ rsp + 0x80 ]
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], r15
mulx r15, rbx, [ rax + 0x28 ]
adox rbx, r11
adcx r8, r12
setc dl
clc
adcx r13, r10
mov r12, 0xfffffffffffffffe 
xchg rdx, r14
mulx r10, r11, r12
seto r12b
mov [ rsp + 0xb8 ], r8
mov r8, 0x0 
dec r8
movzx r14, r14b
adox r14, r8
adox rcx, rbx
movzx rbx, r12b
lea rbx, [ rbx + r15 ]
adcx r11, rbp
movzx rbp, byte [ rsp + 0x90 ]
adox rbp, rbx
mov r15, 0xffffffffffffffff 
mulx r14, r12, r15
mov rdx, r12
adcx rdx, r10
seto r10b
inc r8
adox r9, rdi
adox r13, [ rsp + 0xb0 ]
adox r11, [ rsp + 0x98 ]
adox rdx, [ rsp + 0xa8 ]
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, rdi, [ rax + 0x8 ]
mov rdx, r12
adcx rdx, r14
adcx r12, r14
adox rdx, [ rsp + 0xb8 ]
adcx r14, r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r9
mulx r9, r15, [ rax + 0x28 ]
adox r12, rcx
adox r14, rbp
movzx rdx, r10b
mov rcx, 0x0 
adox rdx, rcx
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, [ rax + 0x8 ]
test al, al
adox rdi, [ rsp + 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], r14
mulx r14, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xd8 ], r10
mov [ rsp + 0xe0 ], r12
mulx r12, r10, [ rsi + 0x10 ]
adcx rbp, r14
adox r10, rbx
adox r12, [ rsp - 0x40 ]
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp - 0x48 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], rbp
mulx rbp, r14, [ rax + 0x18 ]
setc dl
clc
adcx r13, [ rsp + 0x38 ]
mov [ rsp + 0xf0 ], rbp
mov rbp, 0x100000001 
xchg rdx, rbp
mov [ rsp + 0xf8 ], r14
mov [ rsp + 0x100 ], rbx
mulx rbx, r14, r13
adox r15, [ rsp + 0x28 ]
mov rbx, 0x0 
adox r9, rbx
adcx rdi, r11
dec rbx
movzx rbp, bpl
adox rbp, rbx
adox rcx, [ rsp + 0x8 ]
adcx r10, [ rsp + 0xc0 ]
adcx r12, r8
mov r11, [ rsp + 0xe0 ]
adcx r11, [ rsp + 0x100 ]
mov rdx, [ rax + 0x20 ]
mulx rbp, r8, [ rsi + 0x18 ]
adcx r15, [ rsp + 0xd0 ]
mov rdx, [ rsp + 0x0 ]
adox rdx, [ rsp + 0xf8 ]
mov rbx, 0xffffffff 
xchg rdx, r14
mov [ rsp + 0x108 ], rbp
mov [ rsp + 0x110 ], r15
mulx r15, rbp, rbx
adox r8, [ rsp + 0xf0 ]
mov rbx, 0xffffffff00000000 
mov [ rsp + 0x118 ], r8
mov [ rsp + 0x120 ], r14
mulx r14, r8, rbx
seto bl
mov [ rsp + 0x128 ], r11
mov r11, -0x2 
inc r11
adox r8, r15
mov r15, 0xfffffffffffffffe 
mov byte [ rsp + 0x130 ], bl
mulx rbx, r11, r15
adcx r9, [ rsp + 0xc8 ]
mov r15, 0xffffffffffffffff 
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], rcx
mulx rcx, r9, r15
adox r11, r14
mov rdx, r9
adox rdx, rbx
mov r14, r9
adox r14, rcx
adox r9, rcx
seto bl
mov r15, -0x2 
inc r15
adox rbp, r13
adox r8, rdi
adox r11, r10
setc bpl
clc
adcx r8, [ rsp + 0xd8 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx r10, rdi, r8
mov rdx, [ rax + 0x8 ]
mulx r15, r10, [ rsi + 0x20 ]
adox r13, r12
mov rdx, [ rax + 0x0 ]
mov byte [ rsp + 0x148 ], bpl
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x150 ], r12
mov [ rsp + 0x158 ], r15
mulx r15, r12, [ rax + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x160 ], r15
mov [ rsp + 0x168 ], r12
mulx r12, r15, rdi
movzx rdx, bl
lea rdx, [ rdx + rcx ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x170 ], r15
mulx r15, rbx, [ rax + 0x18 ]
adcx r11, [ rsp + 0xe8 ]
adcx r13, [ rsp + 0x140 ]
adox r14, [ rsp + 0x128 ]
adcx r14, [ rsp + 0x120 ]
adox r9, [ rsp + 0x110 ]
adcx r9, [ rsp + 0x118 ]
adox rcx, [ rsp + 0x138 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], rcx
mov [ rsp + 0x180 ], r9
mulx r9, rcx, [ rax + 0x20 ]
seto dl
mov [ rsp + 0x188 ], r14
mov r14, -0x2 
inc r14
adox r10, rbp
mov rbp, [ rsp + 0x168 ]
adox rbp, [ rsp + 0x158 ]
adox rbx, [ rsp + 0x160 ]
mov r14, 0xfffffffffffffffe 
xchg rdx, rdi
mov byte [ rsp + 0x190 ], dil
mov [ rsp + 0x198 ], rbx
mulx rbx, rdi, r14
mov r14, 0xffffffff00000000 
mov [ rsp + 0x1a0 ], rbp
mov [ rsp + 0x1a8 ], r10
mulx r10, rbp, r14
setc r14b
clc
adcx rbp, r12
adox rcx, r15
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x1b0 ], rcx
mulx rcx, r15, r12
adcx rdi, r10
mov rdx, [ rsi + 0x20 ]
mulx r12, r10, [ rax + 0x28 ]
mov rdx, r15
adcx rdx, rbx
mov rbx, r15
adcx rbx, rcx
mov [ rsp + 0x1b8 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x1c0 ], r14b
mov [ rsp + 0x1c8 ], rbx
mulx rbx, r14, [ rax + 0x28 ]
adox r10, r9
setc dl
movzx r9, byte [ rsp + 0x130 ]
clc
mov [ rsp + 0x1d0 ], r10
mov r10, -0x1 
adcx r9, r10
adcx r14, [ rsp + 0x108 ]
mov r9, rcx
setc r10b
clc
mov [ rsp + 0x1d8 ], rbx
mov rbx, -0x1 
movzx rdx, dl
adcx rdx, rbx
adcx r9, r15
seto r15b
inc rbx
adox r8, [ rsp + 0x170 ]
adox rbp, r11
adox rdi, r13
adox r12, [ rsp + 0x188 ]
mov r8, [ rsp + 0x1c8 ]
adox r8, [ rsp + 0x180 ]
seto r11b
mov r13, -0x3 
inc r13
adox rbp, [ rsp + 0x150 ]
mov rdx, 0x100000001 
mulx r13, rbx, rbp
mov r13, 0xffffffffffffffff 
mov rdx, rbx
mov byte [ rsp + 0x1e0 ], r15b
mulx r15, rbx, r13
adox rdi, [ rsp + 0x1a8 ]
adox r12, [ rsp + 0x1a0 ]
mov r13, 0xffffffff00000000 
mov byte [ rsp + 0x1e8 ], r10b
mov [ rsp + 0x1f0 ], r9
mulx r9, r10, r13
mov r13, 0x0 
adcx rcx, r13
mov r13, 0xffffffff 
mov [ rsp + 0x1f8 ], rcx
mov byte [ rsp + 0x200 ], r11b
mulx r11, rcx, r13
clc
adcx rcx, rbp
adox r8, [ rsp + 0x198 ]
seto cl
mov rbp, -0x2 
inc rbp
adox r10, r11
adcx r10, rdi
mov rdi, 0xfffffffffffffffe 
mulx rbp, r11, rdi
adox r11, r9
adcx r11, r12
mov rdx, rbx
adox rdx, rbp
mov r12, rbx
adox r12, r15
adcx rdx, r8
adox rbx, r15
movzx r9, byte [ rsp + 0x190 ]
movzx r8, byte [ rsp + 0x148 ]
lea r9, [ r9 + r8 ]
setc r8b
movzx rbp, byte [ rsp + 0x1c0 ]
clc
mov rdi, -0x1 
adcx rbp, rdi
adcx r14, [ rsp + 0x178 ]
setc bpl
movzx rdi, byte [ rsp + 0x200 ]
clc
mov r13, -0x1 
adcx rdi, r13
adcx r14, [ rsp + 0x1f0 ]
setc dil
clc
movzx rcx, cl
adcx rcx, r13
adcx r14, [ rsp + 0x1b0 ]
movzx rcx, byte [ rsp + 0x1e8 ]
mov r13, [ rsp + 0x1d8 ]
lea rcx, [ rcx + r13 ]
setc r13b
clc
mov [ rsp + 0x208 ], rdx
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx r14, r12
setc r12b
clc
movzx rbp, bpl
adcx rbp, rdx
adcx r9, rcx
seto r8b
inc rdx
adox r10, [ rsp + 0x48 ]
adox r11, [ rsp + 0x78 ]
movzx rbp, byte [ rsp + 0x1e0 ]
mov rcx, [ rsp + 0x1b8 ]
lea rbp, [ rbp + rcx ]
seto cl
dec rdx
movzx rdi, dil
adox rdi, rdx
adox r9, [ rsp + 0x1f8 ]
setc dil
clc
movzx r13, r13b
adcx r13, rdx
adcx r9, [ rsp + 0x1d0 ]
movzx r13, dil
mov rdx, 0x0 
adox r13, rdx
adcx rbp, r13
movzx rdi, r8b
lea rdi, [ rdi + r15 ]
dec rdx
movzx r12, r12b
adox r12, rdx
adox r9, rbx
adox rdi, rbp
mov r15, 0x100000001 
mov rdx, r10
mulx r8, r10, r15
mov r8, 0xfffffffffffffffe 
xchg rdx, r8
mulx r12, rbx, r10
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov rbp, 0xffffffffffffffff 
mov rdx, r10
mulx r15, r10, rbp
mov rbp, 0xffffffff00000000 
mov byte [ rsp + 0x210 ], r13b
mov [ rsp + 0x218 ], rdi
mulx rdi, r13, rbp
mov rbp, 0xffffffff 
mov [ rsp + 0x220 ], r9
mov [ rsp + 0x228 ], r11
mulx r11, r9, rbp
mov rdx, [ rsp + 0x208 ]
add cl, 0x7F
adox rdx, [ rsp + 0x70 ]
adcx r13, r11
adcx rbx, rdi
adox r14, [ rsp + 0x68 ]
mov rcx, r10
adcx rcx, r12
mov r12, r10
adcx r12, r15
adcx r10, r15
mov rdi, 0x0 
adcx r15, rdi
clc
adcx r9, r8
adcx r13, [ rsp + 0x228 ]
adcx rbx, rdx
mov r9, [ rsp + 0x220 ]
adox r9, [ rsp + 0x60 ]
mov r8, [ rsp + 0x218 ]
adox r8, [ rsp + 0x88 ]
mov r11, [ rsp + 0xa0 ]
movzx rdx, byte [ rsp + 0x210 ]
adox rdx, r11
adcx rcx, r14
adcx r12, r9
adcx r10, r8
adcx r15, rdx
setc r11b
seto r14b
mov r9, r13
sub r9, rbp
movzx r8, r11b
movzx r14, r14b
lea r8, [ r8 + r14 ]
mov r14, rbx
mov rdx, 0xffffffff00000000 
sbb r14, rdx
mov r11, rcx
mov rdi, 0xfffffffffffffffe 
sbb r11, rdi
mov rdi, r12
mov rbp, 0xffffffffffffffff 
sbb rdi, rbp
mov rdx, r10
sbb rdx, rbp
mov [ rsp + 0x230 ], rdx
mov rdx, r15
sbb rdx, rbp
sbb r8, 0x00000000
cmovc rdi, r12
cmovc r11, rcx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r11
cmovc r9, r13
cmovc r14, rbx
mov r13, [ rsp + 0x230 ]
cmovc r13, r10
mov [ r8 + 0x20 ], r13
cmovc rdx, r15
mov [ r8 + 0x18 ], rdi
mov [ r8 + 0x0 ], r9
mov [ r8 + 0x28 ], rdx
mov [ r8 + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 696
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.3373
; seed 2046975766439698 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4456500 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=57, initial num_batches=31): 114215 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025628856726130373
; number reverted permutation / tried permutation: 59959 / 89823 =66.752%
; number reverted decision / tried decision: 52627 / 90176 =58.360%
; validated in 28.587s
