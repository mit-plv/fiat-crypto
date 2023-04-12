SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
test al, al
adox r13, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rax + 0x10 ]
adox rdi, r14
adox r10, r12
mov rdx, 0xffffffffffffffff 
mulx r12, r14, r15
adcx r14, r15
mov r14, 0x0 
adox r11, r14
mov r14, 0xffffffff 
mov rdx, r15
mov [ rsp - 0x40 ], rbp
mulx rbp, r15, r14
mov r14, 0xffffffff00000001 
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, r14
mov rdx, -0x2 
inc rdx
adox r15, r12
adcx r15, r13
mov r13, 0x0 
adox rbp, r13
adcx rbp, rdi
adcx rbx, r10
adcx r9, r11
mov rdx, [ rax + 0x0 ]
mulx r10, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r12, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r12, r10
setc r10b
clc
adcx rdi, r15
adcx r12, rbp
adox r13, r11
adox rcx, r14
mov r15, 0xffffffffffffffff 
mov rdx, rdi
mulx rbp, rdi, r15
mov r11, 0x0 
adox r8, r11
mov r14, 0xffffffff 
mulx r15, r11, r14
mov r14, -0x2 
inc r14
adox r11, rbp
mov rbp, 0x0 
adox r15, rbp
mov r14, -0x3 
inc r14
adox rdi, rdx
adcx r13, rbx
adox r11, r12
adcx rcx, r9
movzx rdi, r10b
adcx rdi, r8
mov rbx, 0xffffffff00000001 
mulx r9, r10, rbx
adox r15, r13
mov rdx, [ rax + 0x0 ]
mulx r8, r12, [ rsi + 0x10 ]
adox r10, rcx
adox r9, rdi
seto dl
adc dl, 0x0
movzx rdx, dl
adox r12, r11
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rax + 0x8 ]
adcx r11, r8
adox r11, r15
adcx rcx, [ rsp - 0x30 ]
adox rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx r15, rdi, [ rax + 0x18 ]
adcx rdi, [ rsp - 0x38 ]
mov rdx, 0xffffffff 
mulx r10, r8, r12
adcx r15, rbp
adox rdi, r9
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rbp, r9, r12
mov rdx, [ rax + 0x0 ]
mulx rbx, r14, [ rsi + 0x18 ]
clc
adcx r8, rbp
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, rbp, [ rax + 0x8 ]
clc
adcx rbp, rbx
setc dl
clc
adcx r9, r12
adcx r8, r11
adcx r10, rcx
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rax + 0x10 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x20 ], rcx
mulx rcx, rbx, r12
setc r12b
clc
adcx r14, r8
mov r8, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp - 0x18 ], r11
mulx r11, r14, r8
adcx rbp, r10
movzx r10, r13b
adox r10, r15
setc r13b
clc
mov r15, -0x1 
movzx r12, r12b
adcx r12, r15
adcx rbx, [ rsp - 0x28 ]
adcx rcx, r10
seto r12b
adc r12b, 0x0
movzx r12, r12b
add r9b, 0x7F
adox rdi, [ rsp - 0x18 ]
mov r9, [ rsp - 0x20 ]
adox r9, [ rsp - 0x40 ]
mov r10, [ rsp - 0x48 ]
mov r15, 0x0 
adox r10, r15
add r13b, 0xFF
adcx rbx, rdi
adcx r9, rcx
mov r13, 0xffffffff 
mulx rdi, rcx, r13
adox rcx, r11
movzx r11, r12b
adcx r11, r10
setc r12b
clc
adcx r14, rdx
adcx rcx, rbp
adox rdi, r15
adcx rdi, rbx
mov r14, 0xffffffff00000001 
mulx r10, rbp, r14
adcx rbp, r9
adcx r10, r11
movzx rdx, r12b
adc rdx, 0x0
mov rbx, rcx
sub rbx, r8
mov r9, rdi
sbb r9, r13
mov r12, rbp
sbb r12, 0x00000000
mov r11, r10
sbb r11, r14
sbb rdx, 0x00000000
cmovc r11, r10
cmovc r9, rdi
cmovc r12, rbp
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r12
cmovc rbx, rcx
mov [ rdx + 0x8 ], r9
mov [ rdx + 0x0 ], rbx
mov [ rdx + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5968
; seed 3863025873113359 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1620561 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=212, initial num_batches=31): 137051 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08457009640488695
; number reverted permutation / tried permutation: 63758 / 90085 =70.775%
; number reverted decision / tried decision: 53657 / 89914 =59.676%
; validated in 3.006s
