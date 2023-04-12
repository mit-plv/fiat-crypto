SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 520
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mulx r9, r8, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r15
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], rbp
mulx rbp, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], rbp
mov [ rsp + 0x10 ], r15
mulx r15, rbp, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], r10
mulx r10, r11, r8
test al, al
adox rbp, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rbp
mulx rbp, rcx, [ rsi + 0x28 ]
adox rcx, r15
adox r13, rbp
mov rdx, 0xffffffff 
mulx rbp, r15, r8
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], rcx
mulx rcx, r13, r8
adcx r15, rax
mov r15, 0xfffffffffffffffe 
mov rdx, r8
mulx rax, r8, r15
setc dl
clc
adcx r13, rbp
adcx r8, rcx
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mulx r15, rcx, [ rsi + 0x28 ]
mov rdx, r11
adcx rdx, rax
adox rcx, r14
mov r14, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x40 ], rcx
mulx rcx, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r15
mov [ rsp + 0x50 ], r14
mulx r14, r15, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x58 ], r8
mov r8, -0x2 
inc r8
adox rax, r12
mov r12, r11
adcx r12, r10
mov r8b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x60 ], rax
mov [ rsp + 0x68 ], r12
mulx r12, rax, [ rsi + 0x20 ]
adox r15, rcx
adcx r11, r10
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x70 ], r8b
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x78 ], r15
mov [ rsp + 0x80 ], r10
mulx r10, r15, [ rsi + 0x0 ]
adox rax, r14
adox r9, r12
mov rdx, [ rsi + 0x28 ]
mulx r12, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], rax
mulx rax, r9, [ rsi + 0x0 ]
clc
adcx rcx, r10
adox r14, rbx
adcx rdi, r8
mov rdx, [ rsp + 0x20 ]
setc bl
clc
adcx rdx, [ rsp + 0x18 ]
adcx r9, [ rsp + 0x10 ]
mov r8, 0x0 
adox r12, r8
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x98 ], r12
mulx r12, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xa0 ], r14
mov byte [ rsp + 0xa8 ], bl
mulx rbx, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xb0 ], rdi
mov [ rsp + 0xb8 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r15
mov [ rsp + 0xc8 ], r11
mulx r11, r15, [ rsi + 0x20 ]
mov rdx, -0x2 
inc rdx
adox r8, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd0 ], r8
mov [ rsp + 0xd8 ], r9
mulx r9, r8, [ rsi + 0x18 ]
adcx r8, rax
adox r12, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xe0 ], rcx
mov [ rsp + 0xe8 ], rax
mulx rax, rcx, [ rsi + 0x28 ]
adox rcx, rbx
adcx r15, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rbx, [ rsi + 0x28 ]
adcx rbx, r11
mov rdx, 0x0 
adcx r9, rdx
adox rax, rdx
add bpl, 0xFF
adcx r10, r13
adox r10, [ rsp + 0x0 ]
mov rbp, [ rsp + 0xd8 ]
adcx rbp, [ rsp + 0x58 ]
adcx r8, [ rsp + 0x50 ]
adcx r15, [ rsp + 0x68 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r13, [ rsi + 0x28 ]
mov rdx, 0x100000001 
mov [ rsp + 0xf0 ], rax
mov [ rsp + 0xf8 ], rcx
mulx rcx, rax, r10
adcx rbx, [ rsp + 0xc8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x100 ], r14
mulx r14, rcx, [ rsi + 0x10 ]
adcx r9, [ rsp + 0x80 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x108 ], rdi
mov [ rsp + 0x110 ], r12
mulx r12, rdi, rdx
mov rdx, 0xffffffff 
mov [ rsp + 0x118 ], r11
mov [ rsp + 0x120 ], r9
mulx r9, r11, rax
setc dl
clc
adcx rdi, [ rsp - 0x8 ]
adox rdi, rbp
adcx rcx, r12
adcx r14, [ rsp - 0x30 ]
adox rcx, r8
adox r14, r15
mov bpl, dl
mov rdx, [ rsi + 0x20 ]
mulx r15, r8, [ rsi + 0x8 ]
adcx r8, [ rsp - 0x38 ]
adcx r13, r15
adox r8, rbx
adox r13, [ rsp + 0x120 ]
mov rdx, 0xffffffff00000000 
mulx r12, rbx, rax
mov r15, 0xffffffffffffffff 
mov rdx, r15
mov byte [ rsp + 0x128 ], bpl
mulx rbp, r15, rax
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x130 ], r13
mov [ rsp + 0x138 ], r8
mulx r8, r13, rax
setc al
clc
adcx rbx, r9
adcx r13, r12
mov r9, r15
adcx r9, r8
mov r12, r15
adcx r12, rbp
adcx r15, rbp
setc r8b
clc
adcx r11, r10
adcx rbx, rdi
adcx r13, rcx
adcx r9, r14
adcx r12, [ rsp + 0x138 ]
adcx r15, [ rsp + 0x130 ]
movzx r11, al
mov r10, [ rsp + 0x118 ]
lea r11, [ r11 + r10 ]
movzx r10, byte [ rsp + 0x128 ]
adox r10, r11
movzx rdi, r8b
lea rdi, [ rdi + rbp ]
seto cl
mov r14, -0x2 
inc r14
adox rbx, [ rsp - 0x40 ]
adox r13, [ rsp + 0xd0 ]
adcx rdi, r10
mov rax, 0x100000001 
mov rdx, rax
mulx rbp, rax, rbx
mov rbp, 0xffffffff00000000 
mov rdx, rax
mulx r8, rax, rbp
adox r9, [ rsp + 0x110 ]
movzx r11, cl
mov r10, 0x0 
adcx r11, r10
adox r12, [ rsp + 0x108 ]
adox r15, [ rsp + 0x100 ]
adox rdi, [ rsp + 0xf8 ]
adox r11, [ rsp + 0xf0 ]
mov rcx, 0xffffffff 
mulx r14, r10, rcx
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0x140 ], r11
mulx r11, rcx, rbp
clc
adcx rax, r14
adcx rcx, r8
mov r8, 0xffffffffffffffff 
mulx rbp, r14, r8
mov rdx, r14
adcx rdx, r11
mov r11, r14
adcx r11, rbp
adcx r14, rbp
seto r8b
mov [ rsp + 0x148 ], r14
mov r14, -0x2 
inc r14
adox r10, rbx
adox rax, r13
adox rcx, r9
mov r10, 0x0 
adcx rbp, r10
adox rdx, r12
clc
adcx rax, [ rsp + 0xc0 ]
adcx rcx, [ rsp + 0xb8 ]
adox r11, r15
adcx rdx, [ rsp + 0xb0 ]
adox rdi, [ rsp + 0x148 ]
adox rbp, [ rsp + 0x140 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ rsi + 0x18 ]
movzx rdx, r8b
adox rdx, r10
movzx r8, byte [ rsp + 0xa8 ]
inc r14
mov r10, -0x1 
adox r8, r10
adox r13, [ rsp + 0x8 ]
adcx r13, r11
adox r12, r9
adox r15, [ rsp + 0xe8 ]
adcx r12, rdi
adcx r15, rbp
mov r8, [ rsp + 0xe0 ]
adox r8, r14
mov r11, rdx
mov rdx, [ rsi + 0x28 ]
mulx rbp, rdi, rdx
mov rdx, 0x100000001 
mulx r14, r9, rax
mov r14, 0xfffffffffffffffe 
mov rdx, r14
mulx r10, r14, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x150 ], rbp
mov [ rsp + 0x158 ], rdi
mulx rdi, rbp, r9
mov rdx, 0xffffffff 
mov [ rsp + 0x160 ], r15
mov [ rsp + 0x168 ], r12
mulx r12, r15, r9
adcx r8, r11
mov r11, -0x2 
inc r11
adox r15, rax
setc r15b
clc
adcx rbp, r12
adcx r14, rdi
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx rdi, rax, r9
mov r9, rax
adcx r9, r10
adox rbp, rcx
adox r14, rbx
adox r9, r13
mov rcx, rax
adcx rcx, rdi
adox rcx, [ rsp + 0x168 ]
adcx rax, rdi
mov rbx, 0x0 
adcx rdi, rbx
adox rax, [ rsp + 0x160 ]
adox rdi, r8
clc
adcx rbp, [ rsp - 0x18 ]
adcx r14, [ rsp + 0x60 ]
mov r13, 0x100000001 
mov rdx, r13
mulx r10, r13, rbp
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r12, r10, r13
adcx r9, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0x90 ]
mov r8, 0xfffffffffffffffe 
mov rdx, r13
mulx rbx, r13, r8
adcx rax, [ rsp + 0x88 ]
adcx rdi, [ rsp + 0xa0 ]
movzx r11, r15b
mov r8, 0x0 
adox r11, r8
adcx r11, [ rsp + 0x98 ]
mov r15, 0xffffffff00000000 
mov [ rsp + 0x170 ], r11
mulx r11, r8, r15
mov r15, 0xffffffff 
mov [ rsp + 0x178 ], rdi
mov [ rsp + 0x180 ], rax
mulx rax, rdi, r15
mov rdx, -0x2 
inc rdx
adox r8, rax
setc al
clc
adcx rdi, rbp
adcx r8, r14
adox r13, r11
mov rdi, r10
adox rdi, rbx
mov rbp, r10
adox rbp, r12
adcx r13, r9
adox r10, r12
adcx rdi, rcx
mov r14, 0x0 
adox r12, r14
adcx rbp, [ rsp + 0x180 ]
adcx r10, [ rsp + 0x178 ]
adcx r12, [ rsp + 0x170 ]
mov r9, [ rsp + 0x48 ]
movzx rcx, byte [ rsp + 0x70 ]
dec r14
adox rcx, r14
adox r9, [ rsp + 0x158 ]
mov rdx, [ rsp + 0x150 ]
mov rcx, 0x0 
adox rdx, rcx
movzx rbx, al
adc rbx, 0x0
add r8, [ rsp - 0x48 ]
adcx r13, [ rsp + 0x28 ]
adcx rdi, [ rsp + 0x38 ]
adcx rbp, [ rsp + 0x30 ]
adcx r10, [ rsp + 0x40 ]
adcx r9, r12
mov rax, 0x100000001 
xchg rdx, rax
mulx r12, r11, r8
mov rdx, r15
mulx r15, r12, r11
adcx rax, rbx
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx rcx, rbx, r11
inc r14
adox rbx, r15
setc r15b
clc
adcx r12, r8
adcx rbx, r13
mov r12, 0xfffffffffffffffe 
mov rdx, r12
mulx r8, r12, r11
adox r12, rcx
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx rcx, r13, r11
mov r11, r13
adox r11, r8
mov r8, r13
adox r8, rcx
adox r13, rcx
adcx r12, rdi
adcx r11, rbp
adox rcx, r14
adcx r8, r10
adcx r13, r9
adcx rcx, rax
movzx rdi, r15b
adc rdi, 0x0
mov rbp, rbx
mov r10, 0xffffffff 
sub rbp, r10
mov r9, r12
mov r15, 0xffffffff00000000 
sbb r9, r15
mov rax, r11
mov r14, 0xfffffffffffffffe 
sbb rax, r14
mov r14, r8
sbb r14, rdx
mov r15, r13
sbb r15, rdx
mov r10, rcx
sbb r10, rdx
sbb rdi, 0x00000000
cmovc rax, r11
cmovc r14, r8
cmovc rbp, rbx
cmovc r15, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x20 ], r15
cmovc r9, r12
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x8 ], r9
cmovc r10, rcx
mov [ rdi + 0x18 ], r14
mov [ rdi + 0x28 ], r10
mov [ rdi + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 520
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5879
; seed 0752318274422541 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4284629 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=61, initial num_batches=31): 116464 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027181816675376093
; number reverted permutation / tried permutation: 66945 / 89602 =74.714%
; number reverted decision / tried decision: 62940 / 90397 =69.626%
; validated in 32.218s
