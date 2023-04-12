SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
add rbp, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rsi + 0x0 ]
adcx r14, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
adc r11, 0x0
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r13
mulx r13, r9, [ rsi + 0x10 ]
test al, al
adox r9, rdi
adcx rcx, rbp
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, [ rax + 0x10 ]
adcx r12, r14
adox r13, rcx
adox rbp, r12
mov rdx, [ rax + 0x18 ]
mulx rcx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r12, [ rax + 0x10 ]
mov rdx, 0x0 
mov [ rsp - 0x20 ], rdi
mov rdi, rdx
adcx rdi, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r14
mulx r14, r11, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r11, r9
adcx r12, r13
adcx r8, rbp
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x10 ]
adox r9, rdi
mov rdx, 0x0 
mov rbp, rdx
adox rbp, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rdi, [ rax + 0x18 ]
adcx r15, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r13
mulx r13, r9, [ rax + 0x0 ]
mov rdx, 0x0 
adox rcx, rdx
mov [ rsp - 0x8 ], r9
mov r9, rdx
adcx r9, rbp
adcx rcx, rdx
xor rbp, rbp
adox rbx, r13
adcx r10, rbx
adox r11, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
adox r14, r12
adcx r14, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
adox r15, [ rsp - 0x18 ]
adcx r8, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
adox rdi, r9
adcx rdi, [ rsp - 0x10 ]
adox rcx, rbp
mov rdx, 0x26 
mulx r13, r12, r8
mulx rbx, r9, rdi
adcx rcx, rbp
mulx rdi, r8, r15
mulx rbp, r15, rcx
xor rcx, rcx
adox r8, r10
adcx r12, [ rsp - 0x8 ]
adcx r13, r8
adox r9, r11
adox r15, r14
adcx rdi, r9
adcx rbx, r15
adox rbp, rcx
adc rbp, 0x0
mulx r11, r10, rbp
test al, al
adox r10, r12
mov r11, rcx
adox r11, r13
mov r14, rcx
adox r14, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], r11
mov r12, rcx
adox r12, rbx
mov r13, rcx
cmovo r13, rdx
adcx r10, r13
mov [ r8 + 0x0 ], r10
mov [ r8 + 0x18 ], r12
mov [ r8 + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7425
; seed 0297528345810900 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 601220 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=284, initial num_batches=31): 66750 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11102425069026313
; number reverted permutation / tried permutation: 70896 / 89976 =78.794%
; number reverted decision / tried decision: 50461 / 90023 =56.053%
; validated in 0.322s
