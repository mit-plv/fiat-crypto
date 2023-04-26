SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r9
mulx r9, r15, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], rbp
mulx rbp, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rcx
mulx rcx, r10, [ rax + 0x8 ]
test al, al
adox r9, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], rcx
mulx rcx, r12, [ rsi + 0x10 ]
adox r13, rbx
adcx r12, r9
adcx rbp, r13
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
mov r13, rdx
adcx r13, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mulx r14, r11, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rbx, r8
mov r8, 0x0 
adcx rdi, r8
adox r9, r12
clc
adcx r10, rbx
adcx r15, r9
adox r11, rbp
mov rdx, [ rax + 0x10 ]
mulx rbp, r12, [ rsi + 0x18 ]
adox r12, r13
adcx rcx, r11
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r9, [ rax + 0x0 ]
adcx r12, [ rsp - 0x10 ]
mov rdx, r8
adox rdx, rdi
adox rbx, r8
mov rdi, r8
adcx rdi, rdx
adcx rbx, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rbx
mulx rbx, r8, [ rax + 0x0 ]
test al, al
adox r9, rbx
adcx r9, [ rsp - 0x20 ]
adox r11, r10
adox r15, [ rsp - 0x18 ]
adox rcx, [ rsp - 0x28 ]
adcx r11, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
adcx rcx, [ rsp - 0x38 ]
adcx r14, r12
adox r13, rdi
adcx rbp, r13
mov rdx, 0x26 
mulx rdi, r10, r14
mov rbx, 0x0 
mov r12, rbx
adox r12, [ rsp - 0x8 ]
adcx r12, rbx
mulx r13, r14, rbp
add r10, r9
adcx r14, r11
mulx r11, r9, r12
mulx r12, rbp, rcx
adcx r9, r15
adc r11, 0x0
test al, al
adox rbp, r8
adox r12, r10
adox rdi, r14
adox r13, r9
adox r11, rbx
mulx r15, r8, r11
adcx r8, rbp
mov r15, rbx
adcx r15, r12
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r15
mov r10, rbx
adcx r10, rdi
mov r14, rbx
adcx r14, r13
mov [ rcx + 0x10 ], r10
mov [ rcx + 0x18 ], r14
mov r9, rbx
cmovc r9, rdx
mov rbp, -0x3 
inc rbp
adox r8, r9
mov [ rcx + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4101
; seed 0630983279847400 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1191917 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=354, initial num_batches=31): 131792 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11057145757632453
; number reverted permutation / tried permutation: 55818 / 89963 =62.046%
; number reverted decision / tried decision: 45853 / 90036 =50.927%
; validated in 0.706s
