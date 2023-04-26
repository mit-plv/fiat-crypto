SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 528
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x28 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, [ rsi + 0x28 ]
xor rdx, rdx
adox r15, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r15
mulx r15, rbx, [ rsi + 0x10 ]
adcx r10, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rbp
mulx rbp, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rbx
mulx rbx, r10, [ rax + 0x18 ]
adcx r15, r11
adcx r10, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r11, [ rax + 0x0 ]
adox rcx, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rcx
mulx rcx, rdi, [ rax + 0x20 ]
mov rdx, 0x100000001 
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r15
mulx r15, r10, r11
adox r9, r8
adcx rdi, rbx
mov rdx, [ rsi + 0x18 ]
mulx r8, r15, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r9
mulx r9, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], rcx
mulx rcx, rdi, [ rsi + 0x18 ]
setc dl
clc
adcx r15, rcx
adcx rbx, r8
mov r8b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
adcx rcx, r9
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x20 ], rcx
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adcx r15, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r15
mulx r15, rbx, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov byte [ rsp + 0x40 ], r8b
mov [ rsp + 0x48 ], r10
mulx r10, r8, [ rsi + 0x0 ]
adcx r9, rdi
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x50 ], r9
mulx r9, rdi, [ rax + 0x8 ]
setc dl
clc
adcx rbx, rbp
seto bpl
mov [ rsp + 0x58 ], rbx
mov rbx, -0x2 
inc rbx
adox rdi, r12
movzx r12, dl
lea r12, [ r12 + rcx ]
mov rdx, [ rax + 0x10 ]
mulx rbx, rcx, [ rsi + 0x20 ]
adox rcx, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x60 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
adcx r8, r15
adox r9, rbx
mov rdx, [ rax + 0x28 ]
mulx rbx, r15, [ rsi + 0x0 ]
adcx r13, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x68 ], r9
mulx r9, r10, [ rax + 0x20 ]
adcx r10, r14
adcx r15, r9
mov rdx, 0x0 
adcx rbx, rdx
mov r14, 0xffffffff 
mov rdx, r14
mulx r9, r14, [ rsp + 0x48 ]
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x70 ], rdi
mov [ rsp + 0x78 ], r12
mulx r12, rdi, [ rsp + 0x48 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x80 ], rbx
mov [ rsp + 0x88 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x90 ], r10
mov [ rsp + 0x98 ], r13
mulx r13, r10, [ rsp + 0x48 ]
clc
adcx rdi, r9
adcx r10, r12
adox rbx, rcx
setc cl
clc
adcx r14, r11
adcx rdi, [ rsp + 0x58 ]
adcx r10, r8
mov rdx, [ rax + 0x8 ]
mulx r11, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x0 ]
seto dl
mov r12, -0x2 
inc r12
adox r8, rdi
setc dil
clc
adcx r14, r9
mov r9b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0xa0 ], rbx
mulx rbx, r12, [ rsi + 0x8 ]
adcx r12, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xa8 ], r12
mulx r12, r11, [ rax + 0x18 ]
adcx r11, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb0 ], r11
mulx r11, rbx, [ rax + 0x28 ]
adox r14, r10
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0xb8 ], dil
mulx rdi, r10, [ rax + 0x28 ]
seto dl
mov [ rsp + 0xc0 ], r13
movzx r13, byte [ rsp + 0x40 ]
mov byte [ rsp + 0xc8 ], cl
mov rcx, 0x0 
dec rcx
adox r13, rcx
adox rbx, [ rsp + 0x10 ]
mov r13, 0x0 
adox r11, r13
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0xd0 ], r11
mulx r11, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xd8 ], rbx
mov byte [ rsp + 0xe0 ], r13b
mulx r13, rbx, [ rsi + 0x28 ]
adcx rcx, r12
adcx r10, r11
adc rdi, 0x0
mov rdx, 0x100000001 
mulx r11, r12, r8
add bpl, 0x7F
adox rbx, [ rsp - 0x40 ]
mov rdx, [ rax + 0x28 ]
mulx rbp, r11, [ rsi + 0x28 ]
adox r11, r13
mov rdx, 0x0 
adox rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xe8 ], rbp
mulx rbp, r13, [ rax + 0x28 ]
add r9b, 0xFF
adcx r15, r13
mov rdx, 0xffffffff00000000 
mulx r13, r9, r12
mov rdx, 0xffffffff 
mov [ rsp + 0xf0 ], r11
mov [ rsp + 0xf8 ], rbx
mulx rbx, r11, r12
adox r9, rbx
mov rbx, 0x0 
adcx rbp, rbx
clc
adcx r11, r8
adcx r9, r14
mov r11, 0xffffffffffffffff 
mov rdx, [ rsp + 0x48 ]
mulx r14, r8, r11
setc dl
clc
adcx r9, [ rsp - 0x20 ]
mov rbx, r8
setc r11b
mov [ rsp + 0x100 ], rbp
movzx rbp, byte [ rsp + 0xc8 ]
clc
mov [ rsp + 0x108 ], r15
mov r15, -0x1 
adcx rbp, r15
adcx rbx, [ rsp + 0xc0 ]
mov rbp, r8
adcx rbp, r14
adcx r8, r14
setc r15b
mov byte [ rsp + 0x110 ], r11b
movzx r11, byte [ rsp + 0xb8 ]
clc
mov byte [ rsp + 0x118 ], dl
mov rdx, -0x1 
adcx r11, rdx
adcx rbx, [ rsp + 0x98 ]
adcx rbp, [ rsp + 0x90 ]
adcx r8, [ rsp + 0x88 ]
movzx r11, r15b
lea r11, [ r11 + r14 ]
adcx r11, [ rsp + 0x80 ]
setc r14b
movzx r15, byte [ rsp + 0xe0 ]
clc
adcx r15, rdx
adcx rbx, [ rsp + 0xa8 ]
adcx rbp, [ rsp + 0xb0 ]
adcx rcx, r8
adcx r10, r11
mov r15, 0x100000001 
mov rdx, r15
mulx r8, r15, r9
mov r8, 0xffffffff00000000 
mov rdx, r15
mulx r11, r15, r8
movzx r8, r14b
adcx r8, rdi
mov rdi, 0xfffffffffffffffe 
xchg rdx, rdi
mov [ rsp + 0x120 ], r8
mulx r8, r14, r12
mov rdx, 0xffffffff 
mov [ rsp + 0x128 ], r10
mov [ rsp + 0x130 ], rcx
mulx rcx, r10, rdi
adox r14, r13
setc r13b
clc
adcx r15, rcx
mov rcx, 0xfffffffffffffffe 
mov rdx, rcx
mov [ rsp + 0x138 ], r15
mulx r15, rcx, rdi
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x140 ], r10
mov byte [ rsp + 0x148 ], r13b
mulx r13, r10, rdi
mov [ rsp + 0x150 ], rbp
mulx rbp, rdi, r12
adcx rcx, r11
mov r12, rdi
adox r12, r8
mov r11, rdi
adox r11, rbp
mov r8, r10
adcx r8, r15
mov r15, r10
adcx r15, r13
adcx r10, r13
adox rdi, rbp
mov rdx, 0x0 
adox rbp, rdx
adc r13, 0x0
add byte [ rsp + 0x118 ], 0xFF
adcx rbx, r14
adcx r12, [ rsp + 0x150 ]
adcx r11, [ rsp + 0x130 ]
adcx rdi, [ rsp + 0x128 ]
adcx rbp, [ rsp + 0x120 ]
movzx r14, byte [ rsp + 0x148 ]
adc r14, 0x0
add byte [ rsp + 0x110 ], 0xFF
adcx rbx, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x8 ]
adcx r11, [ rsp - 0x10 ]
adcx rdi, [ rsp + 0x8 ]
adcx rbp, [ rsp + 0xd8 ]
adox r9, [ rsp + 0x140 ]
adox rbx, [ rsp + 0x138 ]
adox rcx, r12
adox r8, r11
adox r15, rdi
adox r10, rbp
adcx r14, [ rsp + 0xd0 ]
adox r13, r14
setc r9b
clc
adcx rbx, [ rsp + 0x30 ]
mov r12, 0x100000001 
mov rdx, rbx
mulx r11, rbx, r12
adcx rcx, [ rsp + 0x28 ]
adcx r8, [ rsp + 0x18 ]
adcx r15, [ rsp + 0x20 ]
movzx r11, r9b
mov rdi, 0x0 
adox r11, rdi
mov rbp, 0xffffffff 
xchg rdx, rbp
mulx r14, r9, rbx
mov rdi, 0xffffffff00000000 
mov rdx, rbx
mulx r12, rbx, rdi
adcx r10, [ rsp + 0x38 ]
adcx r13, [ rsp + 0x50 ]
mov rdi, -0x2 
inc rdi
adox r9, rbp
adcx r11, [ rsp + 0x78 ]
setc r9b
clc
adcx rbx, r14
adox rbx, rcx
mov rbp, 0xfffffffffffffffe 
mulx r14, rcx, rbp
adcx rcx, r12
adox rcx, r8
mov r8, 0xffffffffffffffff 
mulx rdi, r12, r8
mov rdx, r12
adcx rdx, r14
adox rdx, r15
mov r15, r12
adcx r15, rdi
adox r15, r10
adcx r12, rdi
mov r10, 0x0 
adcx rdi, r10
adox r12, r13
adox rdi, r11
clc
adcx rbx, [ rsp - 0x48 ]
mov r13, 0x100000001 
xchg rdx, rbx
mulx r14, r11, r13
movzx r14, r9b
adox r14, r10
xchg rdx, rbp
mulx r10, r9, r11
mov r8, 0xffffffff 
mov rdx, r8
mulx r13, r8, r11
adcx rcx, [ rsp + 0x70 ]
mov rdx, -0x2 
inc rdx
adox r8, rbp
adcx rbx, [ rsp + 0x60 ]
adcx r15, [ rsp + 0x68 ]
adcx r12, [ rsp + 0xa0 ]
adcx rdi, [ rsp + 0x108 ]
mov r8, 0xffffffff00000000 
mov rdx, r11
mulx rbp, r11, r8
adcx r14, [ rsp + 0x100 ]
setc r8b
clc
adcx r11, r13
mov r13, 0xffffffffffffffff 
mov byte [ rsp + 0x158 ], r8b
mov [ rsp + 0x160 ], r14
mulx r14, r8, r13
adcx r9, rbp
adox r11, rcx
mov rdx, r8
adcx rdx, r10
adox r9, rbx
mov r10, r8
adcx r10, r14
adcx r8, r14
adox rdx, r15
mov rcx, 0x0 
adcx r14, rcx
adox r10, r12
clc
adcx r11, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov rbx, 0x100000001 
xchg rdx, rbx
mulx r12, r15, r11
mov rdx, r13
mulx r13, r12, r15
adcx rbx, [ rsp - 0x18 ]
adcx r10, [ rsp + 0x0 ]
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx rcx, rbp, r15
mov rdx, 0xffffffff 
mov [ rsp + 0x168 ], r10
mov [ rsp + 0x170 ], rbx
mulx rbx, r10, r15
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x178 ], r9
mov [ rsp + 0x180 ], r10
mulx r10, r9, r15
setc r15b
clc
adcx rbp, rbx
adcx r9, rcx
mov rcx, r12
adcx rcx, r10
mov rbx, r12
adcx rbx, r13
adcx r12, r13
adox r8, rdi
mov rdi, 0x0 
adcx r13, rdi
adox r14, [ rsp + 0x160 ]
movzx r10, byte [ rsp + 0x158 ]
adox r10, rdi
add r15b, 0xFF
adcx r8, [ rsp + 0xf8 ]
adcx r14, [ rsp + 0xf0 ]
adox r11, [ rsp + 0x180 ]
adox rbp, [ rsp + 0x178 ]
adcx r10, [ rsp + 0xe8 ]
adox r9, [ rsp + 0x170 ]
adox rcx, [ rsp + 0x168 ]
adox rbx, r8
adox r12, r14
adox r13, r10
seto r11b
adc r11b, 0x0
movzx r11, r11b
mov r15, rbp
mov r8, 0xffffffff 
sub r15, r8
mov r14, r9
mov r10, 0xffffffff00000000 
sbb r14, r10
mov rdi, rcx
sbb rdi, rdx
mov rdx, rbx
mov r10, 0xffffffffffffffff 
sbb rdx, r10
mov r8, r12
sbb r8, r10
mov [ rsp + 0x188 ], rdx
mov rdx, r13
sbb rdx, r10
movzx r10, r11b
sbb r10, 0x00000000
cmovc r14, r9
cmovc r15, rbp
cmovc rdi, rcx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x0 ], r15
cmovc rdx, r13
mov [ r10 + 0x28 ], rdx
cmovc r8, r12
mov [ r10 + 0x20 ], r8
mov [ r10 + 0x10 ], rdi
mov rbp, [ rsp + 0x188 ]
cmovc rbp, rbx
mov [ r10 + 0x18 ], rbp
mov [ r10 + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 528
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4880
; seed 4309795652349232 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7703366 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=47, initial num_batches=31): 198847 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02581300174495149
; number reverted permutation / tried permutation: 74689 / 89927 =83.055%
; number reverted decision / tried decision: 65301 / 90072 =72.499%
; validated in 44.765s
