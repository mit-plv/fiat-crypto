SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 408
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
test al, al
adox rbp, rbx
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rax + 0x8 ]
adcx rdi, r11
mov rdx, 0x100000001 
mov [ rsp - 0x40 ], rdi
mulx rdi, r11, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r15
mulx r15, r9, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r9
mulx r9, r15, [ rsi + 0x18 ]
adcx rdi, r10
adcx r15, rbp
adcx rbx, r9
mov rdx, [ rax + 0x28 ]
mulx rbp, r10, [ rsi + 0x18 ]
adcx r10, r13
mov rdx, 0x0 
adcx rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x18 ]
adox rcx, r12
adox r13, r8
mov rdx, 0xffffffff00000000 
mulx r12, r8, r11
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], r10
mulx r10, rbp, r11
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x0 ], rbx
mov [ rsp + 0x8 ], r15
mulx r15, rbx, [ rax + 0x0 ]
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], rdi
mulx rdi, rbx, r11
clc
adcx r8, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, [ rax + 0x20 ]
adox r11, r9
adcx rbx, r12
adcx rdi, [ rsp - 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r12, r9, [ rsi + 0x28 ]
setc dl
clc
adcx r9, r15
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], r9
mov [ rsp + 0x28 ], r11
mulx r11, r9, [ rax + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x30 ], r13
mov [ rsp + 0x38 ], rcx
mulx rcx, r13, [ rax + 0x10 ]
adcx r13, r12
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x40 ], r13
mulx r13, r12, [ rsi + 0x28 ]
adcx r12, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x48 ], r12
mulx r12, rcx, [ rsi + 0x0 ]
adox r9, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x50 ], r9
mulx r9, r10, [ rax + 0x8 ]
mov rdx, 0x0 
adox r11, rdx
mov [ rsp + 0x58 ], r11
mov r11, -0x3 
inc r11
adox rbp, r14
setc bpl
clc
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x0 ]
adox r8, r10
adcx rcx, r9
adox rbx, rcx
adcx r14, r12
adox rdi, r14
mov rdx, [ rax + 0x0 ]
mulx r9, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x60 ], r11
mulx r11, r14, [ rsi + 0x8 ]
setc dl
clc
adcx r14, r9
mov r9b, dl
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x68 ], r13
mov byte [ rsp + 0x70 ], bpl
mulx rbp, r13, [ rsi + 0x8 ]
seto dl
mov [ rsp + 0x78 ], rbp
mov rbp, -0x2 
inc rbp
adox r12, r8
mov r8b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x80 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
adcx rbp, r11
adcx r10, r12
adox r14, rbx
mov rdx, [ rax + 0x8 ]
mulx r11, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x88 ], r10
mulx r10, r12, [ rsi + 0x20 ]
adcx r13, rcx
adox rbp, rdi
mov rdx, [ rsi + 0x20 ]
mulx rcx, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x90 ], rdi
mov [ rsp + 0x98 ], r13
mulx r13, rdi, [ rax + 0x10 ]
setc dl
clc
adcx rbx, rcx
mov cl, dl
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa0 ], rbx
mov [ rsp + 0xa8 ], rbp
mulx rbp, rbx, [ rax + 0x20 ]
adcx rdi, r11
adcx r12, r13
mov rdx, [ rsp - 0x20 ]
mov r11, rdx
seto r13b
mov [ rsp + 0xb0 ], r12
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx r15, r15b
adox r15, r12
adox r11, [ rsp - 0x18 ]
mov r15, rdx
adox r15, [ rsp - 0x18 ]
mov r12, 0x0 
adox rdx, r12
adcx rbx, r10
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xb8 ], rbx
mulx rbx, r12, [ rax + 0x28 ]
adcx r12, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xc0 ], r12
mulx r12, rbp, [ rax + 0x28 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xc8 ], rdi
mov byte [ rsp + 0xd0 ], r13b
mulx r13, rdi, [ rsi + 0x28 ]
adc rbx, 0x0
add byte [ rsp + 0x70 ], 0xFF
adcx rdi, [ rsp + 0x68 ]
adcx rbp, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], rbp
mulx rbp, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xe0 ], rdi
mov [ rsp + 0xe8 ], rbx
mulx rbx, rdi, [ rax + 0x28 ]
adc r12, 0x0
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0xf0 ], r12
mov [ rsp + 0xf8 ], r14
mulx r14, r12, [ rsi + 0x8 ]
add r9b, 0xFF
adcx r13, [ rsp + 0x60 ]
adcx rdi, rbp
mov rdx, 0x100000001 
mulx rbp, r9, [ rsp + 0x80 ]
adc rbx, 0x0
add cl, 0xFF
adcx r12, [ rsp + 0x78 ]
mov rbp, 0xffffffff 
mov rdx, rbp
mulx rcx, rbp, r9
adc r14, 0x0
add r8b, 0xFF
adcx r13, r11
adcx r15, rdi
mov r8, 0xffffffff00000000 
mov rdx, r9
mulx r11, r9, r8
adox r9, rcx
adcx r10, rbx
mov rdi, 0xfffffffffffffffe 
mulx rcx, rbx, rdi
adox rbx, r11
mov r11, 0xffffffffffffffff 
mulx r8, rdi, r11
setc dl
clc
adcx rbp, [ rsp + 0x80 ]
adcx r9, [ rsp + 0xf8 ]
mov rbp, rdi
adox rbp, rcx
mov rcx, rdi
adox rcx, r8
adox rdi, r8
mov r11, 0x0 
adox r8, r11
adcx rbx, [ rsp + 0xa8 ]
movzx r11, byte [ rsp + 0xd0 ]
mov [ rsp + 0x100 ], r8
mov r8, 0x0 
dec r8
adox r11, r8
adox r13, [ rsp + 0x88 ]
adox r15, [ rsp + 0x98 ]
adox r12, r10
adcx rbp, r13
movzx r11, dl
adox r11, r14
adcx rcx, r15
adcx rdi, r12
seto r14b
inc r8
adox r9, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adox rbp, [ rsp + 0x38 ]
mov rdx, 0x100000001 
mulx r13, r10, r9
adox rcx, [ rsp + 0x30 ]
adox rdi, [ rsp + 0x28 ]
adcx r11, [ rsp + 0x100 ]
movzx r13, r14b
adcx r13, r8
adox r11, [ rsp + 0x50 ]
adox r13, [ rsp + 0x58 ]
mov r15, 0xffffffff 
mov rdx, r10
mulx r12, r10, r15
clc
adcx r10, r9
mov r10, 0xffffffff00000000 
mulx r9, r14, r10
mov r8, 0xfffffffffffffffe 
mulx r10, r15, r8
seto r8b
mov [ rsp + 0x108 ], r13
mov r13, -0x2 
inc r13
adox r14, r12
adox r15, r9
adcx r14, rbx
mov rbx, 0xffffffffffffffff 
mulx r9, r12, rbx
mov rdx, r12
adox rdx, r10
mov r10, r12
adox r10, r9
adox r12, r9
adcx r15, rbp
mov rbp, 0x0 
adox r9, rbp
adcx rdx, rcx
adcx r10, rdi
adcx r12, r11
adcx r9, [ rsp + 0x108 ]
mov rcx, -0x3 
inc rcx
adox r14, [ rsp - 0x48 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx rbp, r11, r14
adox r15, [ rsp - 0x40 ]
mov rbp, 0xffffffff00000000 
mov rdx, r11
mulx rcx, r11, rbp
adox rdi, [ rsp + 0x18 ]
adox r10, [ rsp + 0x8 ]
adox r12, [ rsp + 0x0 ]
adox r9, [ rsp - 0x8 ]
movzx r13, r8b
mov rbx, 0x0 
adcx r13, rbx
mov r8, 0xffffffff 
mulx rbp, rbx, r8
clc
adcx r11, rbp
adox r13, [ rsp - 0x10 ]
seto bpl
mov r8, -0x2 
inc r8
adox rbx, r14
mov rbx, 0xfffffffffffffffe 
mulx r8, r14, rbx
adcx r14, rcx
adox r11, r15
mov r15, 0xffffffffffffffff 
mulx rbx, rcx, r15
mov rdx, rcx
adcx rdx, r8
mov r8, rcx
adcx r8, rbx
adox r14, rdi
adox rdx, r10
adox r8, r12
adcx rcx, rbx
adox rcx, r9
setc dil
clc
adcx r11, [ rsp + 0x90 ]
adcx r14, [ rsp + 0xa0 ]
mov r10, 0x100000001 
xchg rdx, r10
mulx r9, r12, r11
movzx r9, dil
lea r9, [ r9 + rbx ]
mov rbx, 0xffffffff 
mov rdx, rbx
mulx rdi, rbx, r12
adox r9, r13
adcx r10, [ rsp + 0xc8 ]
movzx r13, bpl
mov r15, 0x0 
adox r13, r15
adcx r8, [ rsp + 0xb0 ]
adcx rcx, [ rsp + 0xb8 ]
mov rbp, -0x3 
inc rbp
adox rbx, r11
adcx r9, [ rsp + 0xc0 ]
mov rbx, 0xffffffff00000000 
mov rdx, r12
mulx r11, r12, rbx
adcx r13, [ rsp + 0xe8 ]
setc bpl
clc
adcx r12, rdi
adox r12, r14
mov r14, 0xfffffffffffffffe 
mulx r15, rdi, r14
adcx rdi, r11
adox rdi, r10
mov r10, 0xffffffffffffffff 
mulx r14, r11, r10
mov rdx, r11
adcx rdx, r15
mov r15, r11
adcx r15, r14
adox rdx, r8
adox r15, rcx
adcx r11, r14
mov r8, 0x0 
adcx r14, r8
adox r11, r9
adox r14, r13
clc
adcx r12, [ rsp + 0x10 ]
movzx rcx, bpl
adox rcx, r8
adcx rdi, [ rsp + 0x20 ]
mov r9, 0x100000001 
xchg rdx, r9
mulx r13, rbp, r12
adcx r9, [ rsp + 0x40 ]
adcx r15, [ rsp + 0x48 ]
mov rdx, rbp
mulx r13, rbp, rbx
adcx r11, [ rsp + 0xe0 ]
adcx r14, [ rsp + 0xd8 ]
mov r8, 0xffffffff 
mulx rbx, r10, r8
mov r8, -0x2 
inc r8
adox r10, r12
adcx rcx, [ rsp + 0xf0 ]
setc r10b
clc
adcx rbp, rbx
adox rbp, rdi
mov r12, 0xfffffffffffffffe 
mulx rbx, rdi, r12
adcx rdi, r13
adox rdi, r9
mov r9, 0xffffffffffffffff 
mulx r8, r13, r9
mov rdx, r13
adcx rdx, rbx
mov rbx, r13
adcx rbx, r8
adox rdx, r15
adcx r13, r8
adox rbx, r11
mov r15, 0x0 
adcx r8, r15
adox r13, r14
adox r8, rcx
movzx r11, r10b
adox r11, r15
mov r14, rbp
mov r10, 0xffffffff 
sub r14, r10
mov rcx, rdi
mov r15, 0xffffffff00000000 
sbb rcx, r15
mov r9, rdx
sbb r9, r12
mov r12, rbx
mov r15, 0xffffffffffffffff 
sbb r12, r15
mov r10, r13
sbb r10, r15
mov [ rsp + 0x110 ], r9
mov r9, r8
sbb r9, r15
sbb r11, 0x00000000
cmovc r12, rbx
cmovc r14, rbp
cmovc r9, r8
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x28 ], r9
mov [ r11 + 0x0 ], r14
cmovc rcx, rdi
mov [ r11 + 0x18 ], r12
cmovc r10, r13
mov rbp, [ rsp + 0x110 ]
cmovc rbp, rdx
mov [ r11 + 0x20 ], r10
mov [ r11 + 0x8 ], rcx
mov [ r11 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 408
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5785
; seed 2200971061696762 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4498070 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=48, initial num_batches=31): 122217 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02717098666761522
; number reverted permutation / tried permutation: 73953 / 90089 =82.089%
; number reverted decision / tried decision: 64960 / 89910 =72.250%
; validated in 43.986s
