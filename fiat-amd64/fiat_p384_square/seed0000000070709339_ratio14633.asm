SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 496
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], rax
mulx rax, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rbx
mulx rbx, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r10
mulx r10, rbx, [ rsi + 0x20 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], r11
mulx r11, r10, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r11
mulx r11, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rdi
mulx rdi, r10, rdx
adox rbx, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
adcx r10, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r10
mulx r10, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r10
mulx r10, rbx, [ rsi + 0x18 ]
adox rcx, r11
seto dl
mov r11, -0x2 
inc r11
adox rbp, r10
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], rcx
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], rbp
mov [ rsp + 0x48 ], rbx
mulx rbx, rbp, rdx
adcx r14, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
adcx r11, r15
setc dl
clc
adcx rdi, rax
adcx rbp, rcx
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x58 ], rbp
mov [ rsp + 0x60 ], rdi
mulx rdi, rbp, rdx
adcx rax, rbx
mov rdx, 0x100000001 
mov [ rsp + 0x68 ], rax
mulx rax, rbx, rbp
adcx r8, rcx
mov rax, 0xfffffffffffffffe 
mov rdx, rbx
mulx rcx, rbx, rax
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r8
mov byte [ rsp + 0x78 ], r15b
mulx r15, r8, [ rsi + 0x28 ]
adcx r8, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x88 ], r11
mov [ rsp + 0x90 ], r14
mulx r14, r11, [ rsi + 0x18 ]
setc dl
clc
adcx r12, rdi
adcx r9, r13
movzx r13, dl
lea r13, [ r13 + r15 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, rdi, [ rsi + 0x28 ]
mov rdx, [ rsp + 0x30 ]
adox rdx, [ rsp + 0x10 ]
adcx r11, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r11
mulx r11, r13, [ rsi + 0x0 ]
adcx r13, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], r8
mulx r8, r14, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0xb0 ], r8
mov [ rsp + 0xb8 ], r13
mulx r13, r8, rax
adcx rdi, r11
mov r11, [ rsp - 0x38 ]
adox r11, [ rsp - 0x28 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsp + 0x28 ]
clc
mov [ rsp + 0xc0 ], r11
mov r11, -0x1 
movzx r10, r10b
adcx r10, r11
adcx rdx, [ rsp - 0x18 ]
mov r10, [ rsp - 0x20 ]
adcx r10, [ rsp + 0x8 ]
mov r11, 0xffffffff 
xchg rdx, r11
mov [ rsp + 0xc8 ], r10
mov [ rsp + 0xd0 ], r11
mulx r11, r10, rax
setc dl
clc
adcx r8, r11
adcx rbx, r13
adox r14, [ rsp - 0x40 ]
seto r13b
mov r11, -0x2 
inc r11
adox r10, rbp
adox r8, r12
mov r10, 0xffffffffffffffff 
xchg rdx, rax
mulx r12, rbp, r10
adox rbx, r9
mov rdx, rbp
adcx rdx, rcx
mov rcx, rbp
adcx rcx, r12
adcx rbp, r12
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rsi + 0x28 ]
mov rdx, 0x0 
adcx r12, rdx
adox r9, [ rsp + 0xa0 ]
clc
adcx r8, [ rsp - 0x48 ]
adcx rbx, [ rsp + 0x20 ]
adcx r9, [ rsp + 0x90 ]
adox rcx, [ rsp + 0xb8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xd8 ], r11
mov byte [ rsp + 0xe0 ], al
mulx rax, r11, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0xe8 ], r14
mov byte [ rsp + 0xf0 ], r13b
mulx r13, r14, r8
adox rbp, rdi
mov r13, 0xffffffff 
mov rdx, r13
mulx rdi, r13, r14
adox r12, r15
adcx rcx, [ rsp + 0x88 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xf8 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], rbp
mov [ rsp + 0x108 ], rcx
mulx rcx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x110 ], r9
mov [ rsp + 0x118 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
setc dl
clc
adcx r9, r10
adcx r15, rbx
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x120 ], r15
mulx r15, rbx, [ rsi + 0x28 ]
adcx rbx, r12
adcx r11, r15
mov rdx, [ rsi + 0x28 ]
mulx r15, r12, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x128 ], r11
movzx r11, byte [ rsp + 0x78 ]
mov [ rsp + 0x130 ], rbx
mov rbx, 0x0 
dec rbx
adox r11, rbx
adox rbp, [ rsp + 0x50 ]
adox r12, rcx
mov r11, 0x0 
adox r15, r11
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mulx rbx, r11, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x138 ], r9
mov [ rsp + 0x140 ], rbx
mulx rbx, r9, r14
mov rdx, -0x2 
inc rdx
adox r13, r8
adcx r11, rax
setc r13b
clc
adcx r9, rdi
mov r8, 0xfffffffffffffffe 
mov rdx, r8
mulx rax, r8, r14
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp + 0x148 ], r11
mulx r11, rdi, r14
adox r9, [ rsp + 0x118 ]
adcx r8, rbx
adox r8, [ rsp + 0x110 ]
mov r14, rdi
adcx r14, rax
mov rbx, rdi
adcx rbx, r11
adox r14, [ rsp + 0x108 ]
adcx rdi, r11
mov rax, 0x0 
adcx r11, rax
clc
mov rax, -0x1 
movzx r10, r10b
adcx r10, rax
adcx rbp, [ rsp + 0x100 ]
adcx r12, [ rsp + 0xf8 ]
movzx r10, cl
adcx r10, r15
adox rbx, rbp
movzx rcx, r13b
mov r15, [ rsp + 0x140 ]
lea rcx, [ rcx + r15 ]
setc r15b
clc
adcx r9, [ rsp - 0x30 ]
adox rdi, r12
adox r11, r10
adcx r8, [ rsp + 0x60 ]
mov r13, 0x100000001 
mov rdx, r13
mulx rbp, r13, r9
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx r12, rbp, r13
adcx r14, [ rsp + 0x58 ]
adcx rbx, [ rsp + 0x68 ]
adcx rdi, [ rsp + 0x70 ]
mov r10, 0xffffffff 
mov rdx, r10
mulx rax, r10, r13
seto dl
mov [ rsp + 0x150 ], rcx
mov rcx, -0x2 
inc rcx
adox rbp, rax
movzx rax, dl
movzx r15, r15b
lea rax, [ rax + r15 ]
adcx r11, [ rsp + 0x80 ]
adcx rax, [ rsp + 0x98 ]
setc r15b
clc
adcx r10, r9
mov r10, 0xfffffffffffffffe 
mov rdx, r13
mulx r9, r13, r10
adcx rbp, r8
mov r8, rdx
mov rdx, [ rsi + 0x28 ]
mulx r10, rcx, [ rsi + 0x18 ]
adox r13, r12
adcx r13, r14
mov rdx, 0xffffffffffffffff 
mulx r14, r12, r8
mov r8, r12
adox r8, r9
adcx r8, rbx
mov rbx, r12
adox rbx, r14
adox r12, r14
mov r9, 0x0 
adox r14, r9
mov rdx, -0x3 
inc rdx
adox rbp, [ rsp + 0x48 ]
adox r13, [ rsp + 0x40 ]
adcx rbx, rdi
adcx r12, r11
adcx r14, rax
adox r8, [ rsp + 0xa8 ]
mov rdi, 0x100000001 
mov rdx, rbp
mulx r11, rbp, rdi
movzx r11, r15b
adcx r11, r9
movzx r15, byte [ rsp + 0xf0 ]
clc
mov rax, -0x1 
adcx r15, rax
adcx rcx, [ rsp + 0xb0 ]
adcx r10, r9
adox rbx, [ rsp + 0xc0 ]
adox r12, [ rsp + 0xe8 ]
adox rcx, r14
mov r15, 0xffffffff00000000 
xchg rdx, rbp
mulx r9, r14, r15
mov rax, 0xffffffff 
mulx rdi, r15, rax
mov rax, 0xffffffffffffffff 
mov [ rsp + 0x158 ], rcx
mov [ rsp + 0x160 ], r12
mulx r12, rcx, rax
clc
adcx r14, rdi
mov rdi, 0xfffffffffffffffe 
mov [ rsp + 0x168 ], rbx
mulx rbx, rax, rdi
adcx rax, r9
mov rdx, rcx
adcx rdx, rbx
mov r9, rcx
adcx r9, r12
adox r10, r11
adcx rcx, r12
seto r11b
mov rbx, -0x2 
inc rbx
adox r15, rbp
movzx r15, byte [ rsp + 0xe0 ]
mov rbp, [ rsp + 0x0 ]
lea r15, [ r15 + rbp ]
adox r14, r13
adox rax, r8
mov rbp, 0x0 
adcx r12, rbp
clc
adcx r14, [ rsp - 0x8 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx rbp, r8, r14
adcx rax, [ rsp - 0x10 ]
mov rdx, rdi
mulx rbp, rdi, r8
adox r13, [ rsp + 0x168 ]
adcx r13, [ rsp + 0x18 ]
adox r9, [ rsp + 0x160 ]
adox rcx, [ rsp + 0x158 ]
adcx r9, [ rsp + 0x38 ]
adcx rcx, [ rsp + 0xd0 ]
adox r12, r10
adcx r12, [ rsp + 0xc8 ]
movzx r10, r11b
mov rbx, 0x0 
adox r10, rbx
mov r11, 0xffffffff 
mov rdx, r11
mulx rbx, r11, r8
mov rdx, -0x2 
inc rdx
adox r11, r14
mov r11, 0xffffffff00000000 
mov rdx, r11
mulx r14, r11, r8
adcx r15, r10
setc r10b
clc
adcx r11, rbx
adox r11, rax
adcx rdi, r14
adox rdi, r13
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx r13, rax, r8
setc r8b
clc
adcx r11, [ rsp + 0xd8 ]
adcx rdi, [ rsp + 0x138 ]
setc bl
clc
mov r14, -0x1 
movzx r8, r8b
adcx r8, r14
adcx rbp, rax
mov r8, rax
adcx r8, r13
adcx rax, r13
mov r14, 0x0 
adcx r13, r14
adox rbp, r9
adox r8, rcx
clc
mov r9, -0x1 
movzx rbx, bl
adcx rbx, r9
adcx rbp, [ rsp + 0x120 ]
adcx r8, [ rsp + 0x130 ]
adox rax, r12
adox r13, r15
adcx rax, [ rsp + 0x128 ]
movzx rcx, r10b
adox rcx, r14
mov r12, 0x100000001 
mov rdx, r12
mulx r10, r12, r11
adcx r13, [ rsp + 0x148 ]
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx r15, r10, r12
mov rbx, 0xffffffff 
mov rdx, r12
mulx r14, r12, rbx
inc r9
adox r12, r11
mov r12, 0xfffffffffffffffe 
mulx r9, r11, r12
adcx rcx, [ rsp + 0x150 ]
setc bl
clc
adcx r10, r14
adcx r11, r15
mov r15, 0xffffffffffffffff 
mulx r12, r14, r15
mov rdx, r14
adcx rdx, r9
mov r9, r14
adcx r9, r12
adox r10, rdi
adcx r14, r12
adox r11, rbp
mov rdi, 0x0 
adcx r12, rdi
adox rdx, r8
adox r9, rax
adox r14, r13
adox r12, rcx
seto bpl
mov r8, r10
mov rax, 0xffffffff 
sub r8, rax
mov r13, r11
mov rcx, 0xffffffff00000000 
sbb r13, rcx
movzx rdi, bpl
movzx rbx, bl
lea rdi, [ rdi + rbx ]
mov rbx, rdx
mov rbp, 0xfffffffffffffffe 
sbb rbx, rbp
mov rax, r9
sbb rax, r15
mov rcx, r14
sbb rcx, r15
mov rbp, r12
sbb rbp, r15
sbb rdi, 0x00000000
cmovc rcx, r14
cmovc rbx, rdx
cmovc r13, r11
cmovc rax, r9
cmovc r8, r10
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r13
mov [ rdi + 0x0 ], r8
cmovc rbp, r12
mov [ rdi + 0x18 ], rax
mov [ rdi + 0x20 ], rcx
mov [ rdi + 0x28 ], rbp
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 496
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4633
; seed 2734755499952263 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4124610 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=60, initial num_batches=31): 115448 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027990040270474057
; number reverted permutation / tried permutation: 67134 / 89843 =74.724%
; number reverted decision / tried decision: 62513 / 90156 =69.339%
; validated in 33.946s
