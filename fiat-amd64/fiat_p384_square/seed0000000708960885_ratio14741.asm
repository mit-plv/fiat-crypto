SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 432
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0x100000001 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x28 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r9
mulx r9, r15, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbp
mulx rbp, r8, [ rsi + 0x20 ]
xor rdx, rdx
adox r13, rdi
adox rax, r14
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx rdi, r14, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rax
mov [ rsp - 0x20 ], r13
mulx r13, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rax
mov [ rsp - 0x10 ], rbp
mulx rbp, rax, [ rsi + 0x8 ]
adcx rax, r13
adcx r11, rbp
mov rdx, [ rsi + 0x28 ]
mulx rbp, r13, [ rsi + 0x18 ]
adox r13, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r13
mulx r13, r10, rdx
adcx r10, rcx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], rax
mulx rax, r11, [ rsi + 0x20 ]
adcx rcx, r13
adox r11, rbp
mov rdx, [ rsi + 0x28 ]
mulx r13, rbp, rdx
adox rbp, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbp
mulx rbp, rax, [ rsi + 0x28 ]
adcx rax, r10
mov rdx, 0x0 
adox r13, rdx
adc rbp, 0x0
mov r10, 0xffffffff 
mov rdx, r10
mov [ rsp + 0x20 ], r13
mulx r13, r10, r12
xor rdx, rdx
adox r15, r13
mov r13, 0xfffffffffffffffe 
mov rdx, r13
mov [ rsp + 0x28 ], r11
mulx r11, r13, r12
adox r13, r9
mov r12, r14
adox r12, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, r14
adox rdx, rdi
adox r14, rdi
mov [ rsp + 0x30 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], rax
mov [ rsp + 0x40 ], rcx
mulx rcx, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r9
mov [ rsp + 0x50 ], r14
mulx r14, r9, rdx
adcx rax, r11
adcx r9, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
adcx r11, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x58 ], r11
mulx r11, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r9
mov [ rsp + 0x68 ], rax
mulx rax, r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x70 ], r14
mov [ rsp + 0x78 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
mov rdx, 0x0 
adox rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x80 ], rdi
mov [ rsp + 0x88 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r9, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x90 ], r9
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x98 ], r13
mov [ rsp + 0xa0 ], r15
mulx r15, r13, [ rsi + 0x28 ]
adox rdi, rax
adox r11, r12
mov rdx, [ rsi + 0x20 ]
mulx r12, rax, [ rsi + 0x8 ]
adox rax, r9
adcx r14, rcx
adcx r13, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ rsi + 0x28 ]
adox rcx, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r9, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xa8 ], r15
mov [ rsp + 0xb0 ], r13
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, 0x0 
adox rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xb8 ], r15
mov [ rsp + 0xc0 ], r14
mulx r14, r15, [ rsi + 0x0 ]
test al, al
adox r9, [ rsp - 0x30 ]
adcx r8, r13
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc8 ], r8
mov [ rsp + 0xd0 ], rbp
mulx rbp, r8, [ rsi + 0x28 ]
adox r12, r14
adox r13, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0xd8 ], rcx
mulx rcx, r14, [ rsi + 0x20 ]
adox r8, [ rsp - 0x40 ]
mov rdx, 0x0 
adox rbp, rdx
mov [ rsp + 0xe0 ], rax
mov rax, -0x3 
inc rax
adox r10, rbx
adox r9, [ rsp + 0xa0 ]
adox r15, [ rsp + 0x98 ]
adox r12, [ rsp + 0x88 ]
adox r13, [ rsp + 0x78 ]
mov rdx, [ rsi + 0x20 ]
mulx rbx, r10, rdx
adcx r14, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0xe8 ], r14
mulx r14, rax, [ rsi + 0x20 ]
adcx rax, rcx
adcx r10, r14
mov rdx, [ rsi + 0x20 ]
mulx r14, rcx, [ rsi + 0x28 ]
adcx rcx, rbx
mov rdx, 0x0 
adcx r14, rdx
clc
adcx r9, [ rsp + 0x70 ]
adcx r15, [ rsp + 0x90 ]
mov rbx, 0x100000001 
mov rdx, rbx
mov [ rsp + 0xf0 ], r14
mulx r14, rbx, r9
adcx rdi, r12
adcx r11, r13
adox r8, [ rsp + 0x50 ]
adox rbp, [ rsp + 0x80 ]
adcx r8, [ rsp + 0xe0 ]
adcx rbp, [ rsp + 0xd8 ]
mov r14, 0xffffffff 
mov rdx, rbx
mulx r12, rbx, r14
mov r13, 0xfffffffffffffffe 
mov [ rsp + 0xf8 ], rcx
mulx rcx, r14, r13
mov r13, 0xffffffff00000000 
mov [ rsp + 0x100 ], r10
mov [ rsp + 0x108 ], rax
mulx rax, r10, r13
setc r13b
movzx r13, r13b
adox r13, [ rsp + 0xd0 ]
clc
adcx r10, r12
adcx r14, rax
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x110 ], r13
mulx r13, rax, r12
mov rdx, rax
adcx rdx, rcx
mov rcx, rax
adcx rcx, r13
adcx rax, r13
mov r12, 0x0 
adcx r13, r12
clc
adcx rbx, r9
adcx r10, r15
adcx r14, rdi
adcx rdx, r11
adcx rcx, r8
adcx rax, rbp
adcx r13, [ rsp + 0x110 ]
setc bl
clc
adcx r10, [ rsp + 0x48 ]
movzx r9, bl
adox r9, r12
mov r15, 0x100000001 
xchg rdx, r15
mulx r11, rdi, r10
mov r11, 0xffffffff 
mov rdx, rdi
mulx r8, rdi, r11
mov rbp, -0x3 
inc rbp
adox rdi, r10
mov rdi, 0xffffffff00000000 
mulx r10, rbx, rdi
adcx r14, [ rsp + 0x68 ]
adcx r15, [ rsp + 0x60 ]
adcx rcx, [ rsp + 0x58 ]
adcx rax, [ rsp + 0xc0 ]
adcx r13, [ rsp + 0xb0 ]
mov r12, 0xfffffffffffffffe 
mulx rdi, rbp, r12
seto r12b
mov r11, -0x2 
inc r11
adox rbx, r8
adox rbp, r10
adcx r9, [ rsp + 0xa8 ]
mov r8, 0xffffffffffffffff 
mulx r11, r10, r8
setc dl
clc
mov r8, -0x1 
movzx r12, r12b
adcx r12, r8
adcx r14, rbx
adcx rbp, r15
mov r12, r10
adox r12, rdi
mov r15, r10
adox r15, r11
adox r10, r11
adcx r12, rcx
adcx r15, rax
adcx r10, r13
mov rcx, 0x0 
adox r11, rcx
adcx r11, r9
movzx rax, dl
adc rax, 0x0
xor r13, r13
adox r14, [ rsp - 0x18 ]
mov rcx, 0x100000001 
mov rdx, rcx
mulx rdi, rcx, r14
adox rbp, [ rsp + 0x10 ]
adox r12, [ rsp + 0x8 ]
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mulx rbx, rcx, rdi
adox r15, [ rsp + 0x0 ]
adox r10, [ rsp + 0x40 ]
adox r11, [ rsp + 0x38 ]
adox rax, [ rsp + 0x30 ]
mov r9, 0xffffffff 
mulx r8, r13, r9
adcx r13, r14
seto r13b
mov r14, -0x2 
inc r14
adox rcx, r8
adcx rcx, rbp
mov rbp, 0xfffffffffffffffe 
mulx r14, r8, rbp
adox r8, rbx
mov rbx, 0xffffffffffffffff 
mulx rbp, rdi, rbx
mov rdx, rdi
adox rdx, r14
mov r14, rdi
adox r14, rbp
adcx r8, r12
adox rdi, rbp
adcx rdx, r15
mov r12, 0x0 
adox rbp, r12
mov r15, -0x3 
inc r15
adox rcx, [ rsp + 0xb8 ]
adcx r14, r10
adox r8, [ rsp + 0xc8 ]
adcx rdi, r11
adcx rbp, rax
mov r10, 0x100000001 
xchg rdx, rcx
mulx rax, r11, r10
adox rcx, [ rsp + 0xe8 ]
adox r14, [ rsp + 0x108 ]
mov rax, 0xffffffff00000000 
xchg rdx, rax
mulx r15, r12, r11
mov rbx, 0xfffffffffffffffe 
mov rdx, r11
mulx r10, r11, rbx
adox rdi, [ rsp + 0x100 ]
mov [ rsp + 0x118 ], rdi
mulx rdi, rbx, r9
seto r9b
mov [ rsp + 0x120 ], r14
mov r14, -0x2 
inc r14
adox r12, rdi
setc dil
clc
adcx rbx, rax
setc bl
clc
movzx r9, r9b
adcx r9, r14
adcx rbp, [ rsp + 0xf8 ]
movzx rax, dil
movzx r13, r13b
lea rax, [ rax + r13 ]
adcx rax, [ rsp + 0xf0 ]
adox r11, r15
mov r13, 0xffffffffffffffff 
mulx r15, rdi, r13
mov rdx, rdi
adox rdx, r10
mov r10, rdi
adox r10, r15
adox rdi, r15
setc r9b
clc
movzx rbx, bl
adcx rbx, r14
adcx r8, r12
adcx r11, rcx
adcx rdx, [ rsp + 0x120 ]
adcx r10, [ rsp + 0x118 ]
adcx rdi, rbp
mov rcx, 0x0 
adox r15, rcx
mov r12, -0x3 
inc r12
adox r8, [ rsp - 0x48 ]
mov rbx, 0x100000001 
xchg rdx, r8
mulx rcx, rbp, rbx
xchg rdx, rbp
mulx r12, rcx, r13
adox r11, [ rsp - 0x20 ]
mov r14, 0xffffffff 
mulx rbx, r13, r14
adox r8, [ rsp - 0x28 ]
adcx r15, rax
movzx rax, r9b
mov r14, 0x0 
adcx rax, r14
adox r10, [ rsp - 0x8 ]
adox rdi, [ rsp + 0x28 ]
adox r15, [ rsp + 0x18 ]
adox rax, [ rsp + 0x20 ]
mov r9, 0xffffffff00000000 
mov [ rsp + 0x128 ], rax
mulx rax, r14, r9
clc
adcx r14, rbx
seto bl
mov r9, -0x2 
inc r9
adox r13, rbp
adox r14, r11
mov r13, 0xfffffffffffffffe 
mulx r11, rbp, r13
adcx rbp, rax
mov rdx, rcx
adcx rdx, r11
mov rax, rcx
adcx rax, r12
adox rbp, r8
adox rdx, r10
adcx rcx, r12
adox rax, rdi
mov r8, 0x0 
adcx r12, r8
adox rcx, r15
adox r12, [ rsp + 0x128 ]
movzx r10, bl
adox r10, r8
mov rdi, r14
mov r15, 0xffffffff 
sub rdi, r15
mov rbx, rbp
mov r11, 0xffffffff00000000 
sbb rbx, r11
mov r8, rdx
sbb r8, r13
mov r9, rax
mov r11, 0xffffffffffffffff 
sbb r9, r11
mov r13, rcx
sbb r13, r11
mov r15, r12
sbb r15, r11
sbb r10, 0x00000000
cmovc r8, rdx
cmovc r9, rax
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], r9
cmovc r13, rcx
cmovc rbx, rbp
mov [ r10 + 0x8 ], rbx
cmovc rdi, r14
mov [ r10 + 0x20 ], r13
cmovc r15, r12
mov [ r10 + 0x10 ], r8
mov [ r10 + 0x0 ], rdi
mov [ r10 + 0x28 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 432
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4741
; seed 1950844697601171 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7065270 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=49, initial num_batches=31): 185822 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.02630076416046379
; number reverted permutation / tried permutation: 82761 / 90029 =91.927%
; number reverted decision / tried decision: 78330 / 89970 =87.062%
; validated in 39.27s
