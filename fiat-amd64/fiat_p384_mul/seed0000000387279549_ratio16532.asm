SECTION .text
	GLOBAL fiat_p384_mul
fiat_p384_mul:
sub rsp, 376
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
test al, al
adox rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x10 ]
adox r14, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r12, [ rsi + 0x28 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], rbp
mulx rbp, r14, [ rax + 0x0 ]
adcx r12, rbp
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x38 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r9
mulx r9, r14, [ rax + 0x18 ]
adcx rbp, rdi
adcx r14, r12
adox r10, r15
mov rdx, [ rax + 0x20 ]
mulx rdi, r15, [ rsi + 0x28 ]
adcx r15, r9
mov rdx, [ rsi + 0x20 ]
mulx r9, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x28 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r14
mulx r14, r15, [ rax + 0x28 ]
adcx r15, rdi
adox r12, r11
mov rdx, [ rsi + 0x20 ]
mulx rdi, r11, [ rax + 0x28 ]
adox r11, r9
mov rdx, 0x0 
adcx r14, rdx
adox rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r14
mulx r14, r9, [ rsi + 0x18 ]
test al, al
adox rcx, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r15
mulx r15, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rbp
mov [ rsp + 0x8 ], rdi
mulx rdi, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r12
mulx r12, r11, [ rax + 0x8 ]
adox r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x20 ], r10
mulx r10, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], rcx
mulx rcx, r9, [ rax + 0x0 ]
adcx r11, rcx
adcx rbp, r12
mov rdx, 0x100000001 
mulx rcx, r12, r8
setc cl
clc
adcx r13, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
adcx r10, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x40 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
adox r15, r14
mov rdx, [ rax + 0x28 ]
mov [ rsp + 0x48 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x50 ], r11
mov [ rsp + 0x58 ], r9
mulx r9, r11, [ rax + 0x20 ]
adox r11, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x60 ], r11
mulx r11, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x68 ], r10
mov [ rsp + 0x70 ], rbp
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x78 ], r13
mov [ rsp + 0x80 ], rbx
mulx rbx, r13, r12
adox r14, r9
setc r9b
clc
adcx r13, r8
setc r13b
clc
adcx r10, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, [ rax + 0x10 ]
adcx r8, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x88 ], r14
mulx r14, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x90 ], r8
mov [ rsp + 0x98 ], r10
mulx r10, r8, [ rsi + 0x8 ]
adcx rbp, r11
adcx r8, r14
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r11, [ rax + 0x28 ]
adcx r11, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xa0 ], r15
mulx r15, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0xa8 ], r11
mov [ rsp + 0xb0 ], r8
mulx r8, r11, [ rsi + 0x10 ]
adc r14, 0x0
add cl, 0xFF
adcx rdi, r10
adcx r11, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, [ rax + 0x28 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0xb8 ], r11
mulx r11, r15, [ rsi + 0x0 ]
adcx rcx, r8
adc r10, 0x0
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xc0 ], r10
mulx r10, r8, [ rax + 0x20 ]
add r9b, 0xFF
adcx r15, [ rsp + 0x80 ]
adcx r8, r11
mov rdx, 0xffffffff00000000 
mulx r11, r9, r12
mov rdx, 0xfffffffffffffffe 
mov [ rsp + 0xc8 ], rcx
mov [ rsp + 0xd0 ], rdi
mulx rdi, rcx, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0xd8 ], r14
mov [ rsp + 0xe0 ], rbp
mulx rbp, r14, [ rax + 0x28 ]
adox r9, rbx
adox rcx, r11
adcx r14, r10
mov rdx, 0xffffffffffffffff 
mulx r10, rbx, r12
mov r12, rbx
adox r12, rdi
mov r11, rbx
adox r11, r10
adox rbx, r10
mov rdi, 0x0 
adcx rbp, rdi
adox r10, rdi
add r13b, 0xFF
adcx r9, [ rsp + 0x78 ]
adox r9, [ rsp + 0x70 ]
adcx rcx, [ rsp + 0x68 ]
adox rcx, [ rsp + 0x98 ]
adcx r12, r15
adox r12, [ rsp + 0x90 ]
adcx r11, r8
adcx rbx, r14
adox r11, [ rsp + 0xe0 ]
adox rbx, [ rsp + 0xb0 ]
mov r13, 0x100000001 
mov rdx, r13
mulx r15, r13, r9
mov r15, 0xffffffff 
mov rdx, r13
mulx r8, r13, r15
adcx r10, rbp
adox r10, [ rsp + 0xa8 ]
seto r14b
mov rbp, -0x3 
inc rbp
adox r13, r9
mov r13, 0xffffffff00000000 
mulx rdi, r9, r13
movzx r14, r14b
movzx rbp, r14b
adcx rbp, [ rsp + 0xd8 ]
setc r14b
clc
adcx r9, r8
mov r8, 0xfffffffffffffffe 
mulx r15, r13, r8
adcx r13, rdi
adox r9, rcx
mov rcx, 0xffffffffffffffff 
mulx r8, rdi, rcx
adox r13, r12
mov r12, rdi
adcx r12, r15
adox r12, r11
mov r11, rdi
adcx r11, r8
adcx rdi, r8
adox r11, rbx
adox rdi, r10
mov rbx, 0x0 
adcx r8, rbx
adox r8, rbp
clc
adcx r9, [ rsp + 0x58 ]
adcx r13, [ rsp + 0x50 ]
adcx r12, [ rsp + 0x40 ]
adcx r11, [ rsp + 0xd0 ]
adcx rdi, [ rsp + 0xb8 ]
mov rdx, 0x100000001 
mulx rbp, r10, r9
mov rdx, r10
mulx rbp, r10, rcx
movzx r15, r14b
adox r15, rbx
mov r14, 0xffffffff 
mulx rcx, rbx, r14
adcx r8, [ rsp + 0xc8 ]
mov r14, -0x2 
inc r14
adox rbx, r9
adcx r15, [ rsp + 0xc0 ]
mov rbx, 0xffffffff00000000 
mulx r14, r9, rbx
setc bl
clc
adcx r9, rcx
adox r9, r13
mov r13, 0xfffffffffffffffe 
mov byte [ rsp + 0xe8 ], bl
mulx rbx, rcx, r13
adcx rcx, r14
mov rdx, r10
adcx rdx, rbx
mov r14, r10
adcx r14, rbp
adcx r10, rbp
adox rcx, r12
adox rdx, r11
adox r14, rdi
mov r12, 0x0 
adcx rbp, r12
adox r10, r8
clc
adcx r9, [ rsp + 0x38 ]
adcx rcx, [ rsp + 0x30 ]
mov r11, 0x100000001 
xchg rdx, r11
mulx r8, rdi, r9
mov r8, 0xffffffff 
mov rdx, rdi
mulx rbx, rdi, r8
adcx r11, [ rsp + 0x28 ]
adcx r14, [ rsp + 0x48 ]
adox rbp, r15
adcx r10, [ rsp + 0x60 ]
movzx r15, byte [ rsp + 0xe8 ]
adox r15, r12
mov r13, -0x3 
inc r13
adox rdi, r9
adcx rbp, [ rsp + 0x88 ]
mov rdi, 0xffffffff00000000 
mulx r12, r9, rdi
adcx r15, [ rsp + 0xa0 ]
setc r13b
clc
adcx r9, rbx
adox r9, rcx
mov rcx, 0xfffffffffffffffe 
mulx rdi, rbx, rcx
adcx rbx, r12
mov r12, 0xffffffffffffffff 
mulx r8, rcx, r12
mov rdx, rcx
adcx rdx, rdi
adox rbx, r11
mov r11, rcx
adcx r11, r8
adox rdx, r14
adox r11, r10
adcx rcx, r8
mov r14, 0x0 
adcx r8, r14
adox rcx, rbp
adox r8, r15
movzx r10, r13b
adox r10, r14
test al, al
adox r9, [ rsp - 0x28 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mulx r15, r13, r9
adox rbx, [ rsp - 0x40 ]
mov r15, 0xffffffff 
mov rdx, r13
mulx rdi, r13, r15
mov r14, 0xffffffff00000000 
mulx r15, r12, r14
adox rbp, [ rsp - 0x48 ]
adcx r12, rdi
adox r11, [ rsp + 0x20 ]
adox rcx, [ rsp + 0x18 ]
adox r8, [ rsp + 0x10 ]
adox r10, [ rsp + 0x8 ]
seto dil
mov r14, -0x2 
inc r14
adox r13, r9
mov r13, 0xfffffffffffffffe 
mulx r14, r9, r13
adcx r9, r15
adox r12, rbx
mov rbx, 0xffffffffffffffff 
mulx r13, r15, rbx
mov rdx, r15
adcx rdx, r14
mov r14, r15
adcx r14, r13
adcx r15, r13
mov rbx, 0x0 
adcx r13, rbx
adox r9, rbp
adox rdx, r11
adox r14, rcx
clc
adcx r12, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov rbp, 0x100000001 
xchg rdx, rbp
mulx rcx, r11, r12
mov rcx, 0xffffffff00000000 
mov rdx, r11
mulx rbx, r11, rcx
adox r15, r8
adox r13, r10
adcx rbp, [ rsp + 0x0 ]
movzx r8, dil
mov r10, 0x0 
adox r8, r10
adcx r14, [ rsp - 0x18 ]
adcx r15, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x8 ]
adcx r8, [ rsp - 0x10 ]
mov rdi, 0xffffffff 
mulx rcx, r10, rdi
mov rdi, -0x2 
inc rdi
adox r11, rcx
setc cl
clc
adcx r10, r12
mov r10, 0xfffffffffffffffe 
mulx rdi, r12, r10
adox r12, rbx
adcx r11, r9
adcx r12, rbp
mov r9, 0xffffffffffffffff 
mulx rbp, rbx, r9
mov rdx, rbx
adox rdx, rdi
mov rdi, rbx
adox rdi, rbp
adox rbx, rbp
adcx rdx, r14
adcx rdi, r15
mov r14, 0x0 
adox rbp, r14
adcx rbx, r13
adcx rbp, r8
movzx r15, cl
adc r15, 0x0
mov r13, r11
mov rcx, 0xffffffff 
sub r13, rcx
mov r8, r12
mov r14, 0xffffffff00000000 
sbb r8, r14
mov r9, rdx
sbb r9, r10
mov r10, rdi
mov r14, 0xffffffffffffffff 
sbb r10, r14
mov rcx, rbx
sbb rcx, r14
mov [ rsp + 0xf0 ], rcx
mov rcx, rbp
sbb rcx, r14
sbb r15, 0x00000000
cmovc r9, rdx
cmovc r10, rdi
cmovc rcx, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x28 ], rcx
cmovc r13, r11
cmovc r8, r12
mov [ r15 + 0x8 ], r8
mov [ r15 + 0x10 ], r9
mov r11, [ rsp + 0xf0 ]
cmovc r11, rbx
mov [ r15 + 0x18 ], r10
mov [ r15 + 0x0 ], r13
mov [ r15 + 0x20 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 376
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6532
; seed 0851227241522009 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6756019 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=40, initial num_batches=31): 184622 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.027327039784820026
; number reverted permutation / tried permutation: 72780 / 89684 =81.152%
; number reverted decision / tried decision: 63323 / 90315 =70.113%
; validated in 46.32s
