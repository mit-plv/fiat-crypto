SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
add r9, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mulx r15, r8, rcx
adcx r10, rbx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r8, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r14
mulx r14, r8, [ rsi + 0x18 ]
adcx rbx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r14
mulx r14, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r13
mulx r13, r8, [ rax + 0x8 ]
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
clc
adcx r8, r14
adcx r11, r13
adcx rbp, rdi
mov rdx, 0xffffffff 
mulx r13, r14, rcx
setc dil
clc
adcx r14, r15
mov r15, 0x0 
adcx r13, r15
adox r14, r9
adox r13, r10
movzx r9, dil
lea r9, [ r9 + r12 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rax + 0x0 ]
mov rdx, 0xffffffff00000001 
mulx r15, rdi, rcx
adox rdi, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], rbp
mulx rbp, r9, [ rax + 0x8 ]
clc
adcx r9, r10
adox r15, [ rsp - 0x20 ]
adcx rcx, rbp
seto dl
mov r10, -0x2 
inc r10
adox r12, r14
adox r9, r13
adox rcx, rdi
mov r14b, dl
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x18 ]
adcx r13, rbx
adox r13, r15
mov rdx, 0x0 
adcx rdi, rdx
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx rbp, rbx, r12
mov r15, 0xffffffff 
mov rdx, r12
mulx r10, r12, r15
clc
adcx r12, rbp
mov rbp, 0x0 
adcx r10, rbp
clc
adcx rbx, rdx
adcx r12, r9
movzx rbx, r14b
adox rbx, rdi
seto r14b
mov r9, -0x3 
inc r9
adox r12, [ rsp - 0x28 ]
adcx r10, rcx
adox r8, r10
mov rcx, 0xffffffff00000001 
mulx r10, rdi, rcx
mov rdx, r12
mulx rbp, r12, rcx
adcx rdi, r13
adcx r10, rbx
adox r11, rdi
movzx r13, r14b
mov rbx, 0x0 
adcx r13, rbx
adox r10, [ rsp - 0x10 ]
mov r14, 0xffffffffffffffff 
mulx rbx, rdi, r14
mulx r14, r9, r15
clc
adcx r9, rbx
mov rbx, 0x0 
adcx r14, rbx
clc
adcx rdi, rdx
adcx r9, r8
adcx r14, r11
adcx r12, r10
adox r13, [ rsp - 0x18 ]
adcx rbp, r13
seto dil
adc dil, 0x0
movzx rdi, dil
mov rdx, [ rax + 0x18 ]
mulx r11, r8, [ rsi + 0x18 ]
adox r9, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x48 ]
adcx rdx, [ rsp - 0x38 ]
adox rdx, r14
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, [ rax + 0x10 ]
adcx r14, [ rsp - 0x40 ]
adcx r8, r13
adcx r11, rbx
adox r14, r12
adox r8, rbp
mov rdx, 0xffffffffffffffff 
mulx rbp, r12, r9
mov rdx, r15
mulx r13, r15, r9
clc
adcx r15, rbp
movzx rbp, dil
adox rbp, r11
adcx r13, rbx
clc
adcx r12, r9
adcx r15, r10
mov rdx, r9
mulx r12, r9, rcx
adcx r13, r14
adcx r9, r8
setc dil
seto dl
mov r10, r15
mov r11, 0xffffffffffffffff 
sub r10, r11
mov r14, r13
mov r8, 0xffffffff 
sbb r14, r8
mov r11, r9
sbb r11, 0x00000000
dec rbx
movzx rdi, dil
adox rdi, rbx
adox rbp, r12
movzx r12, dl
mov rdi, 0x0 
adox r12, rdi
mov rdx, rbp
sbb rdx, rcx
sbb r12, 0x00000000
cmovc r14, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r14
cmovc r10, r15
cmovc r11, r9
mov [ r12 + 0x10 ], r11
cmovc rdx, rbp
mov [ r12 + 0x18 ], rdx
mov [ r12 + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5850
; seed 0225951427246490 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1992642 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=115, initial num_batches=31): 126159 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06331242641678736
; number reverted permutation / tried permutation: 65335 / 90152 =72.472%
; number reverted decision / tried decision: 55746 / 89847 =62.045%
; validated in 2.245s
