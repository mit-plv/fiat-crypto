SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], r9
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r13, r14
adox r10, rbx
mov rdx, [ rax + 0x18 ]
mulx r14, rbx, [ rsi + 0x8 ]
adcx r8, r13
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r13, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r13, r12
adox rbx, r8
adcx rdi, r10
mov r12, 0x0 
mov r10, r12
adcx r10, r14
mov rdx, [ rax + 0x10 ]
mulx r14, r8, [ rsi + 0x10 ]
adox r8, rdi
adox rcx, r10
mov rdx, [ rax + 0x18 ]
mulx r10, rdi, [ rsi + 0x10 ]
adcx r10, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r14
mulx r14, r12, [ rax + 0x10 ]
clc
adcx r15, r13
adcx r12, rbx
adcx r9, r8
adcx r11, rcx
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, 0x0 
mov r8, rdx
adox r8, r10
mov rcx, rdx
adcx rcx, r8
mov rdx, [ rax + 0x18 ]
mulx r8, r10, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r10
mulx r10, r14, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
mov [ rsp - 0x8 ], r14
xor r14, r14
adox r13, r10
adcx rbp, r13
adox rbx, r15
adox r12, [ rsp - 0x30 ]
adox r9, [ rsp - 0x28 ]
adox rdi, r11
adcx rbx, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x18 ]
adcx rdi, [ rsp - 0x20 ]
adcx rcx, [ rsp - 0x48 ]
mov rdx, 0x26 
mulx r11, r15, r9
mulx r13, r10, rdi
adox r8, r14
mulx rdi, r9, rcx
adcx r8, r14
test al, al
adox r10, rbp
mulx rcx, rbp, r8
adcx r15, [ rsp - 0x8 ]
adcx r11, r10
adox r9, rbx
adox rbp, r12
adox rcx, r14
adcx r13, r9
adcx rdi, rbp
adc rcx, 0x0
mulx r12, rbx, rcx
test al, al
adox rbx, r15
mov r12, r14
adox r12, r11
mov r8, r14
adox r8, r13
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], r8
mov r15, r14
adox r15, rdi
mov r11, r14
cmovo r11, rdx
adcx rbx, r11
mov [ r10 + 0x0 ], rbx
mov [ r10 + 0x18 ], r15
mov [ r10 + 0x8 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4510
; seed 1164537953227510 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1331010 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=183, initial num_batches=31): 113520 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08528861541235604
; number reverted permutation / tried permutation: 56951 / 89983 =63.291%
; number reverted decision / tried decision: 46960 / 90016 =52.169%
; validated in 0.593s
