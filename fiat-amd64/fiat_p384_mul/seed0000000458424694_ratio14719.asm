SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 600
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, 0x100000001 
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, r15
mov r9, 0xffffffff 
mov rdx, rbx
mov [ rsp - 0x38 ], r14
mulx r14, rbx, r9
xor r9, r9
adox rbx, r15
mov rbx, 0xffffffff00000000 
mulx r9, r15, rbx
adcx r15, r14
mov r14, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp - 0x30 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], rbx
mulx rbx, r13, r14
adcx r13, r9
setc r9b
clc
adcx rbp, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
setc dl
clc
adcx rcx, r11
adox r15, rbp
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mov [ rsp - 0x10 ], rcx
mulx rcx, rbp, r14
seto r14b
mov rdx, -0x2 
inc rdx
adox r10, r15
seto r15b
inc rdx
mov rdx, -0x1 
movzx r9, r9b
adox r9, rdx
adox rbx, rbp
mov rdx, [ rax + 0x20 ]
mov byte [ rsp - 0x8 ], r15b
mulx r15, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
adcx rdi, r8
mov rdx, 0x100000001 
mov [ rsp + 0x10 ], rdi
mulx rdi, r8, r10
adcx r15, r13
mov rdx, [ rax + 0x8 ]
mulx r13, rdi, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], r13
mov [ rsp + 0x20 ], rdi
mulx rdi, r13, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x28 ], r15
mov r15, 0x0 
dec r15
movzx r11, r11b
adox r11, r15
adox r12, r13
adcx r9, rbx
mov r11, rcx
setc bl
clc
movzx rdx, dl
adcx rdx, r15
adcx r11, rbp
adcx rbp, rcx
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rax + 0x18 ]
adox r13, rdi
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x30 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
adox rdi, r15
seto dl
mov r15, 0x0 
dec r15
movzx r14, r14b
adox r14, r15
adox r12, [ rsp - 0x18 ]
adox r13, [ rsp + 0x8 ]
adox r11, rdi
setc r14b
movzx rdi, byte [ rsp - 0x8 ]
clc
adcx rdi, r15
adcx r12, [ rsp - 0x10 ]
mov rdi, 0xffffffff 
xchg rdx, r8
mov [ rsp + 0x38 ], rbp
mulx rbp, r15, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x40 ], r9
mov byte [ rsp + 0x48 ], r8b
mulx r8, r9, rdi
adcx r13, [ rsp + 0x10 ]
movzx rdi, r14b
lea rdi, [ rdi + rcx ]
seto cl
mov r14, -0x2 
inc r14
adox r15, r10
mov r15, 0xffffffff00000000 
mulx r14, r10, r15
adcx r11, [ rsp + 0x28 ]
setc r15b
clc
adcx r10, rbp
adcx r9, r14
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0x50 ], r11
mulx r11, r14, rbp
adox r10, r12
mov rdx, r14
adcx rdx, r8
adox r9, r13
mov r12, r14
adcx r12, r11
adcx r14, r11
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x58 ], r14
mov [ rsp + 0x60 ], r12
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], r11
mov [ rsp + 0x70 ], r8
mulx r8, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov byte [ rsp + 0x78 ], r15b
mov [ rsp + 0x80 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
clc
adcx r12, [ rsp - 0x30 ]
seto dl
mov byte [ rsp + 0x88 ], cl
mov rcx, -0x2 
inc rcx
adox r15, r8
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r15
mulx r15, rcx, [ rax + 0x18 ]
adox r13, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], r13
mulx r13, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x28 ]
mov byte [ rsp + 0xa0 ], r8b
mov [ rsp + 0xa8 ], r11
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], r11
mov byte [ rsp + 0xb8 ], bl
mulx rbx, r11, [ rax + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xc0 ], r12
mov [ rsp + 0xc8 ], r9
mulx r9, r12, [ rax + 0x10 ]
adox rcx, rbp
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd0 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
adox rbp, r15
adcx r12, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0xd8 ], rbp
mulx rbp, r15, [ rsi + 0x20 ]
adox r11, rcx
mov rdx, 0x0 
adox rbx, rdx
adcx r8, r13
mov rdx, [ rsi + 0x20 ]
mulx rcx, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], r13
mov [ rsp + 0xe8 ], rbx
mulx rbx, r13, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r14, r10
mov r10, [ rsp + 0xc8 ]
adox r10, [ rsp + 0xc0 ]
mov rdx, 0x100000001 
mov [ rsp + 0xf0 ], rbx
mov [ rsp + 0xf8 ], r11
mulx r11, rbx, r14
mov r11, 0xffffffffffffffff 
mov rdx, rbx
mov [ rsp + 0x100 ], r8
mulx r8, rbx, r11
mov r11, [ rsp - 0x20 ]
mov [ rsp + 0x108 ], rdi
setc dil
mov [ rsp + 0x110 ], r9
movzx r9, byte [ rsp + 0xb8 ]
clc
mov [ rsp + 0x118 ], r12
mov r12, -0x1 
adcx r9, r12
adcx r11, [ rsp + 0x0 ]
setc r9b
clc
adcx r15, rcx
movzx rcx, r9b
mov r12, [ rsp - 0x28 ]
lea rcx, [ rcx + r12 ]
adcx r13, rbp
mov r12, 0xffffffff 
mulx r9, rbp, r12
mov r12, rdx
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x120 ], r13
mov [ rsp + 0x128 ], r15
mulx r15, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000000 
mov byte [ rsp + 0x130 ], dil
mov [ rsp + 0x138 ], rcx
mulx rcx, rdi, r12
setc dl
clc
adcx rbp, r14
seto bpl
mov r14, -0x2 
inc r14
adox rdi, r9
mov r9, 0xfffffffffffffffe 
xchg rdx, r12
mov byte [ rsp + 0x140 ], r12b
mulx r12, r14, r9
adox r14, rcx
adcx rdi, r10
seto r10b
movzx rdx, byte [ rsp + 0x48 ]
mov rcx, 0x0 
dec rcx
adox rdx, rcx
adox r13, [ rsp + 0x40 ]
seto dl
inc rcx
adox rdi, [ rsp + 0xa8 ]
seto cl
movzx r9, byte [ rsp + 0x88 ]
mov [ rsp + 0x148 ], rdi
mov rdi, 0x0 
dec rdi
adox r9, rdi
adox r13, [ rsp + 0x38 ]
movzx r9, dl
lea r9, [ r9 + r15 ]
adox r9, [ rsp + 0x80 ]
setc r15b
clc
movzx r10, r10b
adcx r10, rdi
adcx r12, rbx
mov r10, rbx
adcx r10, r8
adcx rbx, r8
setc dl
movzx rdi, byte [ rsp + 0x78 ]
clc
mov [ rsp + 0x150 ], rbx
mov rbx, -0x1 
adcx rdi, rbx
adcx r13, [ rsp + 0x30 ]
adcx r11, r9
mov rdi, [ rsp + 0x70 ]
seto r9b
movzx rbx, byte [ rsp + 0xa0 ]
mov byte [ rsp + 0x158 ], cl
mov rcx, 0x0 
dec rcx
adox rbx, rcx
adox rdi, [ rsp + 0x50 ]
movzx rbx, dl
lea rbx, [ rbx + r8 ]
adox r13, [ rsp + 0x60 ]
seto r8b
inc rcx
mov rdx, -0x1 
movzx rbp, bpl
adox rbp, rdx
adox rdi, [ rsp + 0x118 ]
movzx r9, r9b
movzx rbp, r9b
adcx rbp, [ rsp + 0x138 ]
setc r9b
clc
movzx r8, r8b
adcx r8, rdx
adcx r11, [ rsp + 0x58 ]
adcx rbp, [ rsp + 0x68 ]
adox r13, [ rsp + 0x110 ]
adox r11, [ rsp + 0x108 ]
movzx r8, r9b
adcx r8, rcx
movzx r9, byte [ rsp + 0x130 ]
mov rcx, [ rsp + 0xb0 ]
lea r9, [ r9 + rcx ]
clc
movzx r15, r15b
adcx r15, rdx
adcx rdi, r14
adox rbp, [ rsp + 0x100 ]
adox r9, r8
mov rcx, 0x100000001 
mov rdx, rcx
mulx r14, rcx, [ rsp + 0x148 ]
adcx r12, r13
adcx r10, r11
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mulx r15, r14, rcx
seto r13b
movzx r11, byte [ rsp + 0x158 ]
mov r8, 0x0 
dec r8
adox r11, r8
adox rdi, [ rsp + 0x90 ]
adox r12, [ rsp + 0x98 ]
adox r10, [ rsp + 0xd0 ]
adcx rbp, [ rsp + 0x150 ]
adcx rbx, r9
adox rbp, [ rsp + 0xd8 ]
adox rbx, [ rsp + 0xf8 ]
mov r11, 0xffffffff00000000 
mov rdx, rcx
mulx r9, rcx, r11
mov r8, 0xffffffff 
mov [ rsp + 0x160 ], rbx
mulx rbx, r11, r8
setc r8b
clc
adcx rcx, rbx
adcx r14, r9
movzx r9, r8b
movzx r13, r13b
lea r9, [ r9 + r13 ]
mov r13, 0xffffffffffffffff 
mulx rbx, r8, r13
adox r9, [ rsp + 0xe8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x168 ], r9
mulx r9, r13, [ rsi + 0x20 ]
mov rdx, r8
adcx rdx, r15
mov r15, r8
adcx r15, rbx
adcx r8, rbx
mov [ rsp + 0x170 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x178 ], r15
mov [ rsp + 0x180 ], rbp
mulx rbp, r15, [ rax + 0x18 ]
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r11, [ rsp + 0x148 ]
adcx rcx, rdi
adcx r14, r12
seto r11b
movzx rdi, byte [ rsp + 0x140 ]
dec rdx
adox rdi, rdx
adox r15, [ rsp + 0xf0 ]
adox r13, rbp
mov rdx, [ rax + 0x28 ]
mulx r12, rdi, [ rsi + 0x20 ]
adox rdi, r9
mov rdx, 0x0 
adox r12, rdx
mov r9, -0x3 
inc r9
adox rcx, [ rsp + 0xe0 ]
adcx r8, r10
adox r14, [ rsp + 0x128 ]
adox r8, [ rsp + 0x120 ]
mov r10, [ rsp + 0x178 ]
adcx r10, [ rsp + 0x180 ]
mov rbp, 0x100000001 
mov rdx, rbp
mulx r9, rbp, rcx
mov r9, 0xfffffffffffffffe 
mov rdx, rbp
mov [ rsp + 0x188 ], r8
mulx r8, rbp, r9
mov r9, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x190 ], r8
mov [ rsp + 0x198 ], r14
mulx r14, r8, [ rax + 0x20 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x1a0 ], r14
mov [ rsp + 0x1a8 ], r8
mulx r8, r14, r9
mov rdx, [ rsp + 0x160 ]
adcx rdx, [ rsp + 0x170 ]
adcx rbx, [ rsp + 0x168 ]
adox r15, r10
adox r13, rdx
adox rdi, rbx
movzx r10, r11b
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, r11, [ rsi + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1b0 ], rbx
mov [ rsp + 0x1b8 ], r11
mulx r11, rbx, r9
adox r12, r10
clc
adcx r14, rcx
seto r14b
mov rcx, -0x2 
inc rcx
adox rbx, r8
adox rbp, r11
adcx rbx, [ rsp + 0x198 ]
mov rdx, [ rsi + 0x28 ]
mulx r10, r8, [ rax + 0x10 ]
adcx rbp, [ rsp + 0x188 ]
mov rdx, 0xffffffffffffffff 
mulx rcx, r11, r9
mov r9, r11
adox r9, [ rsp + 0x190 ]
mov rdx, r11
adox rdx, rcx
adox r11, rcx
adcx r9, r15
adcx rdx, r13
adcx r11, rdi
mov r15, 0x0 
adox rcx, r15
adcx rcx, r12
mov r13, rdx
mov rdx, [ rsi + 0x28 ]
mulx r12, rdi, [ rax + 0x18 ]
mov rdx, -0x3 
inc rdx
adox rbx, [ rsp + 0x1b8 ]
movzx r15, r14b
mov rdx, 0x0 
adcx r15, rdx
mov r14, [ rsp + 0x1b0 ]
clc
adcx r14, [ rsp + 0x20 ]
adox r14, rbp
adcx r8, [ rsp + 0x18 ]
adcx rdi, r10
adcx r12, [ rsp + 0x1a8 ]
adox r8, r9
adox rdi, r13
adox r12, r11
mov rdx, [ rax + 0x28 ]
mulx rbp, r10, [ rsi + 0x28 ]
adcx r10, [ rsp + 0x1a0 ]
mov rdx, 0x100000001 
mulx r13, r9, rbx
mov r13, 0xffffffff 
mov rdx, r13
mulx r11, r13, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x1c0 ], r12
mov [ rsp + 0x1c8 ], rdi
mulx rdi, r12, r9
adox r10, rcx
mov rcx, 0x0 
adcx rbp, rcx
clc
adcx r12, r11
adox rbp, r15
seto r15b
mov r11, -0x3 
inc r11
adox r13, rbx
adox r12, r14
mov r13, 0xfffffffffffffffe 
mov rdx, r13
mulx rbx, r13, r9
adcx r13, rdi
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx rdi, r9, r14
mov rdx, r9
adcx rdx, rbx
mov rbx, r9
adcx rbx, rdi
adox r13, r8
adox rdx, [ rsp + 0x1c8 ]
adox rbx, [ rsp + 0x1c0 ]
adcx r9, rdi
adox r9, r10
adcx rdi, rcx
adox rdi, rbp
movzx r8, r15b
adox r8, rcx
mov r10, r12
mov r15, 0xffffffff 
sub r10, r15
mov rbp, r13
mov rcx, 0xffffffff00000000 
sbb rbp, rcx
mov r11, rdx
mov r14, 0xfffffffffffffffe 
sbb r11, r14
mov rcx, rbx
mov r14, 0xffffffffffffffff 
sbb rcx, r14
mov r15, r9
sbb r15, r14
mov [ rsp + 0x1d0 ], r15
mov r15, rdi
sbb r15, r14
sbb r8, 0x00000000
cmovc r11, rdx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r11
cmovc rbp, r13
cmovc r10, r12
cmovc r15, rdi
mov [ r8 + 0x8 ], rbp
mov [ r8 + 0x0 ], r10
cmovc rcx, rbx
mov r12, [ rsp + 0x1d0 ]
cmovc r12, r9
mov [ r8 + 0x28 ], r15
mov [ r8 + 0x18 ], rcx
mov [ r8 + 0x20 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 600
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4719
; seed 1162558990880060 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4895565 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=55, initial num_batches=31): 126269 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.025792528543692097
; number reverted permutation / tried permutation: 67125 / 90182 =74.433%
; number reverted decision / tried decision: 62782 / 89817 =69.900%
; validated in 37.637s
