SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
xor r14, r14
adox rbx, r10
mov r10, 0xffffffff 
mov rdx, rax
mulx r14, rax, r10
adcx rax, r13
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r14, rdx
adox rdi, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r15
mulx r15, rbp, [ rsi + 0x18 ]
clc
adcx r12, r13
adcx rax, rbx
adox rbp, r8
adcx r14, rdi
mov rdx, 0x0 
adox r15, rdx
mov r12, 0xffffffff00000001 
mov rdx, r13
mulx rbx, r13, r12
adcx r13, rbp
mov rdx, [ rsi + 0x18 ]
mulx rdi, r8, rdx
mov rdx, -0x2 
inc rdx
adox r11, r9
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, [ rsi + 0x18 ]
adox r9, rcx
adcx rbx, r15
mov rdx, [ rsi + 0x10 ]
mulx r15, rcx, [ rsi + 0x8 ]
adox r8, rbp
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, rdx
setc dl
clc
adcx rbp, r10
mov r10, 0x0 
adox rdi, r10
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
adcx rcx, r12
adcx rdi, r15
adc r8, 0x0
xor rdx, rdx
adox rax, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, [ rsi + 0x10 ]
adox rbp, r14
adox rcx, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r11
mulx r11, r9, [ rsi + 0x10 ]
adcx r9, r12
adcx r14, r11
adox rdi, rbx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbx, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r14
mulx r14, r11, rax
adcx rbx, r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp - 0x10 ], rbx
mulx rbx, r13, rax
mov rdx, 0x0 
adcx r12, rdx
clc
adcx r13, r14
adcx rbx, rdx
clc
adcx r11, rax
adcx r13, rbp
adcx rbx, rcx
movzx r11, r10b
adox r11, r8
mov r10, 0xffffffff00000001 
mov rdx, r10
mulx r8, r10, rax
seto al
mov rbp, -0x2 
inc rbp
adox r15, r13
mov rcx, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, rcx
adcx r10, rdi
adox r9, rbx
adcx r8, r11
adox r10, [ rsp - 0x18 ]
adox r8, [ rsp - 0x10 ]
movzx rdi, al
mov r13, 0x0 
adcx rdi, r13
mov rbx, 0xffffffff 
mulx r11, rax, rbx
clc
adcx rax, r14
adcx r11, r13
adox r12, rdi
mov r14, 0xffffffff00000001 
mulx r13, rdi, r14
clc
adcx r15, rdx
adcx rax, r9
seto r15b
inc rbp
adox rax, [ rsp - 0x48 ]
mov rdx, r14
mulx r9, r14, rax
mov rdx, rax
mulx rbp, rax, rcx
adcx r11, r10
adcx rdi, r8
adcx r13, r12
movzx r10, r15b
mov r8, 0x0 
adcx r10, r8
mulx r12, r15, rbx
adox r11, [ rsp - 0x20 ]
clc
adcx r15, rbp
adcx r12, r8
clc
adcx rax, rdx
adcx r15, r11
adox rdi, [ rsp - 0x28 ]
adcx r12, rdi
adox r13, [ rsp - 0x30 ]
adcx r14, r13
adox r10, [ rsp - 0x38 ]
adcx r9, r10
seto al
adc al, 0x0
movzx rax, al
mov rdx, r15
sub rdx, rcx
mov rbp, r12
sbb rbp, rbx
mov r11, r14
sbb r11, 0x00000000
mov rdi, r9
mov r13, 0xffffffff00000001 
sbb rdi, r13
movzx r10, al
sbb r10, 0x00000000
cmovc rdi, r9
cmovc rbp, r12
cmovc rdx, r15
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], rbp
cmovc r11, r14
mov [ r10 + 0x10 ], r11
mov [ r10 + 0x0 ], rdx
mov [ r10 + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.8558
; seed 3883026564856508 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 857878 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=193, initial num_batches=31): 72085 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08402709942439368
; number reverted permutation / tried permutation: 78665 / 90225 =87.188%
; number reverted decision / tried decision: 62088 / 89774 =69.160%
; validated in 1.044s
