SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, r13
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, r13
xor rdx, rdx
adox r8, r14
adox r9, rcx
adox r10, rbx
adcx rdi, rbp
adcx r15, rdx
clc
adcx r12, r13
adcx rdi, r8
adox r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r12, [ rax + 0x0 ]
adcx r15, r9
mov rdx, 0xffffffff00000001 
mulx rbp, r14, r13
adcx r14, r10
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r12, rdi
adcx rbp, r11
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, [ rax + 0x18 ]
setc dl
clc
adcx r13, rbx
adcx r8, rcx
adox r13, r15
adox r8, r14
adcx r10, r9
adox r10, rbp
mov r11, 0x0 
adcx rdi, r11
movzx rbx, dl
adox rbx, rdi
mov r15, 0xffffffff 
mov rdx, r15
mulx r14, r15, r12
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rbp, rcx, r12
clc
adcx r15, rbp
seto r9b
mov rdi, -0x3 
inc rdi
adox rcx, r12
adox r15, r13
mov rdx, [ rax + 0x0 ]
mulx r13, rcx, [ rsi + 0x10 ]
adcx r14, r11
adox r14, r8
mov rdx, 0xffffffff00000001 
mulx rbp, r8, r12
adox r8, r10
adox rbp, rbx
mov rdx, [ rax + 0x8 ]
mulx r10, r12, [ rsi + 0x10 ]
clc
adcx rcx, r15
mov rdx, [ rsi + 0x10 ]
mulx r15, rbx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mulx rdi, r11, rcx
movzx rdx, r9b
mov [ rsp - 0x18 ], r11
mov r11, 0x0 
adox rdx, r11
mov r9, -0x3 
inc r9
adox r12, r13
adcx r12, r14
adox rbx, r10
adcx rbx, r8
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r8, r14, [ rsi + 0x18 ]
adox r15, [ rsp - 0x20 ]
adcx r15, rbp
mov rdx, 0xffffffff 
mulx r10, rbp, rcx
mov r11, [ rsp - 0x28 ]
mov r9, 0x0 
adox r11, r9
mov rdx, -0x3 
inc rdx
adox rbp, rdi
adcx r11, r13
mov rdi, rcx
setc r13b
clc
adcx rdi, [ rsp - 0x18 ]
adcx rbp, r12
mov rdi, 0xffffffff00000001 
mov rdx, rcx
mulx r12, rcx, rdi
adox r10, r9
adcx r10, rbx
adcx rcx, r15
adcx r12, r11
mov rdx, [ rsi + 0x18 ]
mulx r15, rbx, [ rax + 0x10 ]
movzx rdx, r13b
adc rdx, 0x0
xor r13, r13
adox r8, [ rsp - 0x30 ]
adcx r14, rbp
mov r9, 0xffffffffffffffff 
xchg rdx, r14
mulx rbp, r11, r9
adox rbx, [ rsp - 0x38 ]
adox r15, [ rsp - 0x40 ]
adcx r8, r10
adcx rbx, rcx
adcx r15, r12
mov r10, [ rsp - 0x48 ]
adox r10, r13
adcx r10, r14
mov rcx, -0x3 
inc rcx
adox r11, rdx
mov r11, 0xffffffff 
mulx r14, r12, r11
setc cl
clc
adcx r12, rbp
adox r12, r8
mulx r8, rbp, rdi
adcx r14, r13
adox r14, rbx
adox rbp, r15
adox r8, r10
movzx rdx, cl
adox rdx, r13
mov rbx, r12
sub rbx, r9
mov r15, r14
sbb r15, r11
mov rcx, rbp
sbb rcx, 0x00000000
mov r10, r8
sbb r10, rdi
sbb rdx, 0x00000000
cmovc rcx, rbp
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rcx
cmovc r10, r8
cmovc r15, r14
cmovc rbx, r12
mov [ rdx + 0x18 ], r10
mov [ rdx + 0x8 ], r15
mov [ rdx + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.6923
; seed 1361483313957027 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1699837 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=85, initial num_batches=31): 107909 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06348196915351295
; number reverted permutation / tried permutation: 65766 / 89640 =73.367%
; number reverted decision / tried decision: 39058 / 90359 =43.225%
; validated in 2.172s
