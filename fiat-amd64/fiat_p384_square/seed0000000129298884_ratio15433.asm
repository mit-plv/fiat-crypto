SECTION .text
	GLOBAL fiat_p384_square
fiat_p384_square:
sub rsp, 376
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox rbx, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
adcx r11, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r11
mulx r11, rax, [ rsi + 0x18 ]
adcx r14, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mulx r14, rcx, rdx
adox rcx, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
adox rbp, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r14, [ rsi + 0x20 ]
adox r14, rcx
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x18 ], r14
mulx r14, rcx, [ rsi + 0x10 ]
adox rcx, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, rbp, [ rsi + 0x8 ]
adcx rbp, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
adcx rbx, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
adcx r8, rbp
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x8 ], r14
mulx r14, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r8
mulx r8, rbp, rdx
adc r9, 0x0
add r12, r14
adcx rcx, r13
adcx rax, rbx
adcx rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, rbx, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rbp
mov [ rsp + 0x28 ], rax
mulx rax, rbp, [ rsi + 0x0 ]
adcx rbx, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x38 ], rcx
mov [ rsp + 0x40 ], r12
mulx r12, rcx, [ rsi + 0x18 ]
adc r14, 0x0
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r8
mulx r8, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r9
mov [ rsp + 0x60 ], r10
mulx r10, r9, [ rsi + 0x10 ]
test al, al
adox rcx, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x68 ], rcx
mulx rcx, rbx, rdx
adox r9, r12
adcx rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x70 ], r11
mov [ rsp + 0x78 ], r9
mulx r9, r11, [ rsi + 0x28 ]
adcx r15, rax
adox rbx, r10
adox r14, rcx
adox r11, r8
mov rdx, [ rsi + 0x28 ]
mulx r8, rax, [ rsi + 0x20 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rsi + 0x28 ]
mov rdx, -0x2 
inc rdx
adox r10, r12
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0x80 ], r10
mulx r10, r12, [ rsi + 0x10 ]
mov rdx, 0x100000001 
mov [ rsp + 0x88 ], r9
mov [ rsp + 0x90 ], r11
mulx r11, r9, r13
mov r11, 0xffffffff 
mov rdx, r9
mov [ rsp + 0x98 ], r14
mulx r14, r9, r11
adox r12, rcx
mov rcx, 0xfffffffffffffffe 
mov [ rsp + 0xa0 ], r12
mulx r12, r11, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x28 ]
mov [ rsp + 0xa8 ], rbx
mov [ rsp + 0xb0 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
adox rbx, r10
adox rax, rdi
mov rdx, 0xffffffff00000000 
mulx rdi, r10, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0xb8 ], rax
mov [ rsp + 0xc0 ], rbx
mulx rbx, rax, rcx
setc cl
clc
adcx r10, r14
adcx r11, rdi
mov r14, rax
adcx r14, r12
mov r12, rax
adcx r12, rbx
adcx rax, rbx
setc dil
clc
adcx r9, r13
adcx r10, rbp
movzx r9, dil
lea r9, [ r9 + rbx ]
mov rdx, [ rsi + 0x28 ]
mulx rbp, r13, [ rsi + 0x0 ]
adcx r11, r15
mov rdx, [ rsi + 0x28 ]
mulx rbx, r15, rdx
adox r15, r8
mov rdx, [ rsi + 0x0 ]
mulx rdi, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0xc8 ], r15
mov [ rsp + 0xd0 ], r9
mulx r9, r15, [ rsi + 0x0 ]
mov rdx, 0x0 
adox rbx, rdx
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r8, [ rsp + 0xb0 ]
adcx r14, r8
adox r15, rdi
adox r13, r9
seto cl
inc rdx
adox r10, [ rsp + 0x60 ]
adox r11, [ rsp - 0x38 ]
mov rdi, 0x100000001 
mov rdx, rdi
mulx r9, rdi, r10
mov r9, 0xffffffff 
mov rdx, r9
mulx r8, r9, rdi
adcx r12, r15
adcx rax, r13
mov r15, 0xffffffff00000000 
mov rdx, rdi
mulx r13, rdi, r15
adox r14, [ rsp - 0x30 ]
movzx r15, cl
lea r15, [ r15 + rbp ]
adox r12, [ rsp - 0x8 ]
adcx r15, [ rsp + 0xd0 ]
mov rbp, 0xfffffffffffffffe 
mov [ rsp + 0xd8 ], rbx
mulx rbx, rcx, rbp
mov rbp, 0xffffffffffffffff 
mov [ rsp + 0xe0 ], r12
mov [ rsp + 0xe8 ], r14
mulx r14, r12, rbp
setc dl
clc
adcx rdi, r8
adcx rcx, r13
mov r8, r12
adcx r8, rbx
mov r13, r12
adcx r13, r14
adcx r12, r14
mov rbx, 0x0 
adcx r14, rbx
adox rax, [ rsp + 0x0 ]
clc
adcx r9, r10
adcx rdi, r11
adox r15, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0xe8 ]
movzx rdx, dl
movzx r9, dl
adox r9, [ rsp + 0x58 ]
seto r10b
mov r11, -0x3 
inc r11
adox rdi, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov rdx, 0x100000001 
mulx r11, rbx, rdi
adcx r8, [ rsp + 0xe0 ]
mov r11, 0xffffffff00000000 
mov rdx, r11
mulx rbp, r11, rbx
adcx r13, rax
adox r8, [ rsp - 0x28 ]
adcx r12, r15
adox r13, [ rsp - 0x20 ]
mov rax, 0xffffffff 
mov rdx, rbx
mulx r15, rbx, rax
adcx r14, r9
adox r12, [ rsp - 0x18 ]
movzx r9, r10b
mov rax, 0x0 
adcx r9, rax
adox r14, [ rsp - 0x10 ]
clc
adcx r11, r15
mov r10, 0xfffffffffffffffe 
mulx rax, r15, r10
adcx r15, rbp
adox r9, [ rsp + 0x8 ]
seto bpl
mov r10, -0x2 
inc r10
adox rbx, rdi
mov rbx, 0xffffffffffffffff 
mulx r10, rdi, rbx
mov rdx, rdi
adcx rdx, rax
adox r11, rcx
adox r15, r8
adox rdx, r13
mov rcx, rdi
adcx rcx, r10
adox rcx, r12
adcx rdi, r10
mov r8, 0x0 
adcx r10, r8
adox rdi, r14
adox r10, r9
clc
adcx r11, [ rsp + 0x50 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx r14, r12, r11
adcx r15, [ rsp + 0x68 ]
adcx r13, [ rsp + 0x78 ]
adcx rcx, [ rsp + 0xa8 ]
mov r14, 0xffffffff 
mov rdx, r12
mulx rax, r12, r14
movzx r9, bpl
adox r9, r8
mov rbp, 0xfffffffffffffffe 
mulx rbx, r8, rbp
adcx rdi, [ rsp + 0x98 ]
adcx r10, [ rsp + 0x90 ]
mov rbp, 0xffffffff00000000 
mov [ rsp + 0xf0 ], r10
mulx r10, r14, rbp
mov rbp, -0x2 
inc rbp
adox r14, rax
adox r8, r10
adcx r9, [ rsp + 0x88 ]
setc al
clc
adcx r12, r11
adcx r14, r15
mov r12, 0xffffffffffffffff 
mulx r15, r11, r12
adcx r8, r13
mov rdx, r11
adox rdx, rbx
adcx rdx, rcx
mov r13, r11
adox r13, r15
adox r11, r15
adcx r13, rdi
mov rcx, 0x0 
adox r15, rcx
adcx r11, [ rsp + 0xf0 ]
adcx r15, r9
movzx rbx, al
adc rbx, 0x0
test al, al
adox r14, [ rsp + 0x10 ]
adox r8, [ rsp + 0x40 ]
mov rdi, 0x100000001 
xchg rdx, rdi
mulx rax, r10, r14
mov rax, 0xffffffff00000000 
mov rdx, r10
mulx r9, r10, rax
adox rdi, [ rsp + 0x38 ]
adox r13, [ rsp + 0x28 ]
adox r11, [ rsp + 0x20 ]
mov rcx, 0xffffffff 
mulx r12, rbp, rcx
adox r15, [ rsp + 0x30 ]
adcx r10, r12
mov r12, 0xfffffffffffffffe 
mulx rcx, rax, r12
adcx rax, r9
adox rbx, [ rsp + 0x48 ]
seto r9b
mov r12, -0x2 
inc r12
adox rbp, r14
adox r10, r8
mov rbp, 0xffffffffffffffff 
mulx r8, r14, rbp
mov rdx, r14
adcx rdx, rcx
mov rcx, r14
adcx rcx, r8
adox rax, rdi
adox rdx, r13
adox rcx, r11
adcx r14, r8
mov rdi, 0x0 
adcx r8, rdi
clc
adcx r10, [ rsp + 0x70 ]
adcx rax, [ rsp + 0x80 ]
mov r13, 0x100000001 
xchg rdx, r13
mulx rdi, r11, r10
adcx r13, [ rsp + 0xa0 ]
adcx rcx, [ rsp + 0xc0 ]
mov rdx, rbp
mulx rbp, rdi, r11
adox r14, r15
adcx r14, [ rsp + 0xb8 ]
adox r8, rbx
movzx r15, r9b
mov rbx, 0x0 
adox r15, rbx
mov r9, 0xffffffff 
mov rdx, r9
mulx rbx, r9, r11
adcx r8, [ rsp + 0xc8 ]
inc r12
adox r9, r10
mov r9, 0xffffffff00000000 
mov rdx, r11
mulx r10, r11, r9
adcx r15, [ rsp + 0xd8 ]
setc r9b
clc
adcx r11, rbx
adox r11, rax
mov rax, 0xfffffffffffffffe 
mulx r12, rbx, rax
adcx rbx, r10
adox rbx, r13
mov rdx, rdi
adcx rdx, r12
mov r13, rdi
adcx r13, rbp
adox rdx, rcx
adox r13, r14
adcx rdi, rbp
adox rdi, r8
mov rcx, 0x0 
adcx rbp, rcx
adox rbp, r15
movzx r14, r9b
adox r14, rcx
mov r8, r11
mov r10, 0xffffffff 
sub r8, r10
mov r9, rbx
mov r15, 0xffffffff00000000 
sbb r9, r15
mov r12, rdx
sbb r12, rax
mov rcx, r13
mov r15, 0xffffffffffffffff 
sbb rcx, r15
mov rax, rdi
sbb rax, r15
mov r10, rbp
sbb r10, r15
sbb r14, 0x00000000
cmovc rcx, r13
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], rcx
cmovc rax, rdi
mov [ r14 + 0x20 ], rax
cmovc r12, rdx
cmovc r9, rbx
mov [ r14 + 0x8 ], r9
cmovc r10, rbp
cmovc r8, r11
mov [ r14 + 0x28 ], r10
mov [ r14 + 0x0 ], r8
mov [ r14 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 376
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5433
; seed 3067273207181704 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4248688 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=50, initial num_batches=31): 117680 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027697962288593562
; number reverted permutation / tried permutation: 74661 / 89997 =82.959%
; number reverted decision / tried decision: 63964 / 90002 =71.070%
; validated in 39.537s
