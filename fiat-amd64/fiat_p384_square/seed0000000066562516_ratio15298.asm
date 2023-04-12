SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 520
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rbx
mulx rbx, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r10
mulx r10, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], rbx
mulx rbx, r14, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, rax
adox r15, rcx
adox r13, rdi
mov rdx, [ rsi + 0x20 ]
mulx rcx, r8, [ rsi + 0x28 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp - 0x8 ], rcx
mulx rcx, rdi, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], rbx
mulx rbx, r8, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r12
mulx r12, r14, r9
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], r10
mulx r10, rbp, r9
adcx r14, r10
adcx rdi, r12
mov r9, r8
adcx r9, rcx
mov rcx, r8
adcx rcx, rbx
adcx r8, rbx
mov r12, 0x0 
adcx rbx, r12
clc
adcx rbp, rax
adcx r14, r11
adcx rdi, r15
adcx r9, r13
mov rdx, [ rsi + 0x20 ]
mulx rax, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x28 ]
mulx r15, r11, [ rsi + 0x0 ]
adox rbp, [ rsp + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], r13
mulx r13, r12, [ rsi + 0x8 ]
adox r11, rax
adcx rcx, rbp
adcx r8, r11
mov rdx, 0x0 
adox r15, rdx
mov rax, -0x3 
inc rax
adox r12, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rax, r11, [ rsi + 0x10 ]
adox r11, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r11
mulx r11, r13, rdx
adcx rbx, r15
setc dl
clc
adcx r10, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x40 ], r12
mov [ rsp + 0x48 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x50 ], r13
mov [ rsp + 0x58 ], r10
mulx r10, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], rbp
mov byte [ rsp + 0x68 ], r15b
mulx r15, rbp, [ rsi + 0x20 ]
adox rax, [ rsp + 0x10 ]
adcx r12, r11
adox rbp, [ rsp + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x70 ], rbp
mulx rbp, r11, rdx
seto dl
mov [ rsp + 0x78 ], rax
mov rax, -0x2 
inc rax
adox r11, r10
setc r10b
clc
adcx r13, r14
adcx r11, rdi
adox rbp, [ rsp - 0x10 ]
mov r14b, dl
mov rdx, [ rsi + 0x8 ]
mulx rax, rdi, [ rsi + 0x18 ]
adcx rbp, r9
adox rdi, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x80 ], r15
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, 0x100000001 
mov byte [ rsp + 0x88 ], r14b
mov byte [ rsp + 0x90 ], r10b
mulx r10, r14, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r12
mulx r12, r10, [ rsi + 0x28 ]
adox r9, rax
adcx rdi, rcx
adcx r9, r8
mov rdx, [ rsi + 0x28 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa0 ], r9
mulx r9, rax, [ rsi + 0x8 ]
adox rax, r15
mov rdx, 0x0 
adox r9, rdx
adcx rax, rbx
mov rdx, [ rsi + 0x10 ]
mulx r15, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rax
mov [ rsp + 0xb0 ], rdi
mulx rdi, rax, rdx
mov rdx, -0x2 
inc rdx
adox r10, [ rsp - 0x20 ]
adox rbx, r12
movzx r12, byte [ rsp + 0x68 ]
adcx r12, r9
adox rcx, r15
mov r9, 0xffffffff00000000 
mov rdx, r9
mulx r15, r9, r14
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], rdi
mov [ rsp + 0xc0 ], rcx
mulx rcx, rdi, [ rsi + 0x28 ]
adox rdi, r8
adox rax, rcx
mov rdx, 0xfffffffffffffffe 
mulx rcx, r8, r14
mov rdx, 0xffffffff 
mov [ rsp + 0xc8 ], rax
mov [ rsp + 0xd0 ], rdi
mulx rdi, rax, r14
setc dl
clc
adcx rax, r13
seto al
mov r13, -0x2 
inc r13
adox r9, rdi
adox r8, r15
adcx r9, r11
mov r11, 0xffffffffffffffff 
xchg rdx, r11
mulx rdi, r15, r14
mov r14, r15
adox r14, rcx
mov rcx, r15
adox rcx, rdi
adox r15, rdi
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0xd8 ], al
mulx rax, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe0 ], rbx
mov [ rsp + 0xe8 ], r10
mulx r10, rbx, [ rsi + 0x10 ]
setc dl
clc
adcx r13, [ rsp - 0x28 ]
adcx rbx, rax
mov rax, 0x0 
adox rdi, rax
dec rax
movzx rdx, dl
adox rdx, rax
adox rbp, r8
adox r14, [ rsp + 0xb0 ]
adox rcx, [ rsp + 0xa0 ]
adox r15, [ rsp + 0xa8 ]
adox rdi, r12
mov rdx, [ rsi + 0x20 ]
mulx r8, r12, [ rsi + 0x18 ]
adcx r12, r10
adcx r8, [ rsp - 0x30 ]
movzx rdx, r11b
mov r10, 0x0 
adox rdx, r10
mov r11, -0x3 
inc r11
adox r9, [ rsp + 0x60 ]
adox rbp, [ rsp + 0x58 ]
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx rax, r11, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0xf0 ], r8
mov [ rsp + 0xf8 ], r12
mulx r12, r8, r9
mov r12, 0xffffffff00000000 
mov rdx, r12
mov [ rsp + 0x100 ], rbx
mulx rbx, r12, r8
mov rdx, [ rsp + 0x0 ]
adcx rdx, [ rsp - 0x40 ]
mov [ rsp + 0x108 ], rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x110 ], r13
mov [ rsp + 0x118 ], rbp
mulx rbp, r13, r8
adox r14, [ rsp + 0x48 ]
adox rcx, [ rsp + 0x98 ]
setc dl
mov [ rsp + 0x120 ], rcx
movzx rcx, byte [ rsp + 0x90 ]
clc
mov [ rsp + 0x128 ], r14
mov r14, -0x1 
adcx rcx, r14
adcx r11, [ rsp + 0x50 ]
adox r11, r15
mov cl, dl
mov rdx, [ rsi + 0x28 ]
mulx r14, r15, [ rsi + 0x10 ]
adcx r15, rax
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rsi + 0x28 ]
mov byte [ rsp + 0x130 ], cl
mulx rcx, rax, [ rsi + 0x18 ]
adox r15, rdi
adox r14, r10
mov rdx, 0xffffffff 
mulx r10, rdi, r8
clc
adcx r12, r10
mov r10, 0xfffffffffffffffe 
mov rdx, r10
mov [ rsp + 0x138 ], r14
mulx r14, r10, r8
adcx r10, rbx
mov r8, r13
adcx r8, r14
mov rbx, r13
adcx rbx, rbp
adcx r13, rbp
mov r14, 0x0 
adcx rbp, r14
clc
adcx rdi, r9
adcx r12, [ rsp + 0x118 ]
adcx r10, [ rsp + 0x128 ]
adcx r8, [ rsp + 0x120 ]
seto dil
movzx r9, byte [ rsp + 0x88 ]
dec r14
adox r9, r14
adox rax, [ rsp + 0x80 ]
mov r9, 0x0 
adox rcx, r9
mov r14, -0x3 
inc r14
adox r12, [ rsp + 0x30 ]
adox r10, [ rsp + 0x40 ]
adcx rbx, r11
adcx r13, r15
adcx rbp, [ rsp + 0x138 ]
adox r8, [ rsp + 0x38 ]
adox rbx, [ rsp + 0x78 ]
mov r11, 0x100000001 
mov rdx, r11
mulx r15, r11, r12
adox r13, [ rsp + 0x70 ]
adox rax, rbp
movzx r15, dil
adcx r15, r9
mov rdi, 0xffffffff 
mov rdx, rdi
mulx rbp, rdi, r11
adox rcx, r15
mov r15, 0xffffffff00000000 
mov rdx, r15
mulx r9, r15, r11
clc
adcx r15, rbp
mov rbp, 0xfffffffffffffffe 
mov rdx, r11
mulx r14, r11, rbp
adcx r11, r9
mov r9, 0xffffffffffffffff 
mov [ rsp + 0x140 ], rcx
mulx rcx, rbp, r9
mov rdx, rbp
adcx rdx, r14
mov r14, rbp
adcx r14, rcx
seto r9b
mov [ rsp + 0x148 ], rax
mov rax, -0x2 
inc rax
adox rdi, r12
adox r15, r10
adcx rbp, rcx
adox r11, r8
setc dil
clc
adcx r15, [ rsp - 0x48 ]
mov r12, 0x100000001 
xchg rdx, r15
mulx r8, r10, r12
adcx r11, [ rsp + 0x110 ]
adox r15, rbx
adcx r15, [ rsp + 0x100 ]
mov r8, 0xffffffff 
xchg rdx, r10
mulx rax, rbx, r8
mov r8, 0xffffffffffffffff 
mov [ rsp + 0x150 ], r15
mulx r15, r12, r8
adox r14, r13
adcx r14, [ rsp + 0xf8 ]
movzx r13, dil
lea r13, [ r13 + rcx ]
adox rbp, [ rsp + 0x148 ]
adox r13, [ rsp + 0x140 ]
adcx rbp, [ rsp + 0xf0 ]
adcx r13, [ rsp + 0x108 ]
movzx rcx, r9b
mov rdi, 0x0 
adox rcx, rdi
mov r9, 0xfffffffffffffffe 
mulx r8, rdi, r9
movzx r9, byte [ rsp + 0x130 ]
mov [ rsp + 0x158 ], r13
mov r13, [ rsp - 0x8 ]
lea r9, [ r9 + r13 ]
mov r13, 0xffffffff00000000 
mov [ rsp + 0x160 ], rbp
mov [ rsp + 0x168 ], r14
mulx r14, rbp, r13
mov rdx, -0x2 
inc rdx
adox rbp, rax
adox rdi, r14
mov rax, r12
adox rax, r8
mov r8, r12
adox r8, r15
adcx r9, rcx
setc cl
clc
adcx rbx, r10
adcx rbp, r11
adox r12, r15
seto bl
inc rdx
adox rbp, [ rsp - 0x38 ]
mov r10, 0x100000001 
mov rdx, r10
mulx r11, r10, rbp
adcx rdi, [ rsp + 0x150 ]
adcx rax, [ rsp + 0x168 ]
mov r11, 0xfffffffffffffffe 
mov rdx, r10
mulx r14, r10, r11
mov [ rsp + 0x170 ], r14
mulx r14, r11, r13
adox rdi, [ rsp + 0xe8 ]
mov r13, 0xffffffffffffffff 
mov [ rsp + 0x178 ], rdi
mov [ rsp + 0x180 ], r10
mulx r10, rdi, r13
adcx r8, [ rsp + 0x160 ]
adox rax, [ rsp + 0xe0 ]
adcx r12, [ rsp + 0x158 ]
adox r8, [ rsp + 0xc0 ]
movzx r13, bl
lea r13, [ r13 + r15 ]
adcx r13, r9
movzx r15, cl
mov r9, 0x0 
adcx r15, r9
adox r12, [ rsp + 0xd0 ]
adox r13, [ rsp + 0xc8 ]
mov rcx, 0xffffffff 
mulx r9, rbx, rcx
clc
adcx r11, r9
movzx rdx, byte [ rsp + 0xd8 ]
mov r9, [ rsp + 0xb8 ]
lea rdx, [ rdx + r9 ]
adox rdx, r15
adcx r14, [ rsp + 0x180 ]
seto r9b
mov r15, -0x2 
inc r15
adox rbx, rbp
adox r11, [ rsp + 0x178 ]
mov rbx, rdi
adcx rbx, [ rsp + 0x170 ]
mov rbp, rdi
adcx rbp, r10
adox r14, rax
adox rbx, r8
adcx rdi, r10
adox rbp, r12
adox rdi, r13
mov rax, 0x0 
adcx r10, rax
adox r10, rdx
movzx r8, r9b
adox r8, rax
mov r12, r11
sub r12, rcx
mov r13, r14
mov r9, 0xffffffff00000000 
sbb r13, r9
mov rdx, rbx
mov rax, 0xfffffffffffffffe 
sbb rdx, rax
mov r15, rbp
mov rcx, 0xffffffffffffffff 
sbb r15, rcx
mov rax, rdi
sbb rax, rcx
mov r9, r10
sbb r9, rcx
sbb r8, 0x00000000
cmovc r15, rbp
cmovc r13, r14
cmovc rax, rdi
cmovc rdx, rbx
cmovc r12, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], r12
cmovc r9, r10
mov [ r8 + 0x18 ], r15
mov [ r8 + 0x10 ], rdx
mov [ r8 + 0x20 ], rax
mov [ r8 + 0x8 ], r13
mov [ r8 + 0x28 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 520
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5298
; seed 0937279201452437 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4311477 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=60, initial num_batches=31): 118751 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02754299744611881
; number reverted permutation / tried permutation: 67175 / 89770 =74.830%
; number reverted decision / tried decision: 62793 / 90229 =69.593%
; validated in 33.1s
