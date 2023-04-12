SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
test al, al
adox r15, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rbx
mulx rbx, r11, r10
adcx r13, rbx
mov rbx, 0x0 
adcx r14, rbx
clc
adcx r11, r10
adcx r13, r15
adox rcx, rdi
mov r11, 0xffffffff00000001 
mov rdx, r11
mulx rdi, r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r15, r10, [ rax + 0x8 ]
adox rbp, r8
adcx r14, rcx
adcx r11, rbp
adox r12, rbx
mov rdx, -0x3 
inc rdx
adox r9, r13
adcx rdi, r12
setc r8b
clc
adcx r10, [ rsp - 0x48 ]
mov rdx, [ rax + 0x10 ]
mulx rcx, r13, [ rsi + 0x8 ]
adox r10, r14
adcx r13, r15
mov rdx, [ rsi + 0x8 ]
mulx rbp, r15, [ rax + 0x18 ]
adox r13, r11
adcx r15, rcx
mov rdx, 0xffffffffffffffff 
mulx r11, r14, r9
mov r12, 0xffffffff 
mov rdx, r12
mulx rcx, r12, r9
setc dl
clc
adcx r12, r11
adcx rcx, rbx
clc
adcx r14, r9
adcx r12, r10
adcx rcx, r13
adox r15, rdi
movzx r14, dl
lea r14, [ r14 + rbp ]
mov rdi, 0xffffffff00000001 
mov rdx, r9
mulx r10, r9, rdi
adcx r9, r15
movzx rdx, r8b
adox rdx, r14
adcx r10, rdx
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rdx, [ rax + 0x0 ]
mulx r13, rbp, [ rsi + 0x10 ]
adox rbp, r12
mov rdx, [ rsi + 0x10 ]
mulx r12, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, [ rax + 0x8 ]
adcx r15, r13
adox r15, rcx
mov rdx, [ rax + 0x10 ]
mulx r13, rcx, [ rsi + 0x10 ]
adcx rcx, r14
adcx r11, r13
mov rdx, 0xffffffffffffffff 
mulx r13, r14, rbp
adox rcx, r9
adox r11, r10
adcx r12, rbx
mov rdx, [ rsi + 0x18 ]
mulx r10, r9, [ rax + 0x0 ]
movzx rdx, r8b
adox rdx, r12
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
clc
adcx r12, r10
adcx rdi, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r10, [ rsi + 0x18 ]
adcx r10, r8
mov rdx, 0x0 
adcx rbx, rdx
mov r8, 0xffffffff 
mov rdx, r8
mov [ rsp - 0x38 ], rbx
mulx rbx, r8, rbp
clc
adcx r14, rbp
seto r14b
mov rdx, -0x2 
inc rdx
adox r8, r13
mov r13, 0x0 
adox rbx, r13
adcx r8, r15
mov r15, -0x3 
inc r15
adox r9, r8
mov r8, 0xffffffff00000001 
mov rdx, r8
mulx r13, r8, rbp
adcx rbx, rcx
mulx rcx, rbp, r9
adcx r8, r11
adcx r13, [ rsp - 0x40 ]
movzx r11, r14b
mov r15, 0x0 
adcx r11, r15
adox r12, rbx
adox rdi, r8
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx rbx, r9, r14
adox r10, r13
adox r11, [ rsp - 0x38 ]
mov r8, 0xffffffff 
mulx r15, r13, r8
clc
adcx r13, rbx
mov rbx, 0x0 
adcx r15, rbx
clc
adcx r9, rdx
adcx r13, r12
adcx r15, rdi
setc r9b
seto dl
mov r12, r13
sub r12, r14
dec rbx
movzx r9, r9b
adox r9, rbx
adox r10, rbp
adox rcx, r11
seto bpl
mov rdi, r15
sbb rdi, r8
mov r11, r10
sbb r11, 0x00000000
mov r9, rcx
mov rbx, 0xffffffff00000001 
sbb r9, rbx
movzx rbx, bpl
movzx rdx, dl
lea rbx, [ rbx + rdx ]
sbb rbx, 0x00000000
cmovc r9, rcx
cmovc r12, r13
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], r9
cmovc r11, r10
mov [ rbx + 0x10 ], r11
cmovc rdi, r15
mov [ rbx + 0x0 ], r12
mov [ rbx + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6198
; seed 4297873694564506 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1993420 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 127051 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06373518877105677
; number reverted permutation / tried permutation: 63615 / 90021 =70.667%
; number reverted decision / tried decision: 54989 / 89978 =61.114%
; validated in 2.336s
