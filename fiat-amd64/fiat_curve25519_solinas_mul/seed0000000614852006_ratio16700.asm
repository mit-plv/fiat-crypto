SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
add rbp, r11
mov rdx, -0x2 
inc rdx
adox r9, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adcx r15, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mulx r14, rbp, [ rax + 0x18 ]
adox r12, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rcx
mulx rcx, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r14, rdx
clc
adcx r11, rcx
adcx r10, r9
mov r9, rdx
adox r9, r14
mov rdx, [ rax + 0x18 ]
mulx r14, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rcx
mov [ rsp - 0x20 ], rbp
mulx rbp, rcx, [ rax + 0x10 ]
adcx r13, r12
adcx rcx, r9
mov rdx, 0x0 
adox r14, rdx
mov r12, rdx
adcx r12, r14
adc r8, 0x0
mov rdx, [ rax + 0x8 ]
mulx r14, r9, [ rsi + 0x8 ]
add r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, r11, [ rax + 0x10 ]
adcx r11, r10
adcx rbx, r13
adcx rdi, rcx
mov rdx, 0x0 
mov r10, rdx
adcx r10, r12
mov rdx, [ rax + 0x0 ]
mulx rcx, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r13
mulx r13, r12, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
add r12, rcx
mov rcx, -0x3 
inc rcx
adox r15, r12
adcx r13, r9
adcx r14, r11
adcx rbx, [ rsp - 0x20 ]
adox r13, [ rsp - 0x30 ]
adox r14, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x40 ]
adox rbp, rbx
adcx r8, rdx
adox rdi, [ rsp - 0x48 ]
adox r10, [ rsp - 0x18 ]
adox r8, rdx
mov r9, 0x26 
mov rdx, r9
mulx r11, r9, r8
mulx rbx, r12, rbp
mulx r8, rbp, rdi
xor rdi, rdi
adox rbp, r15
mulx rdi, r15, r10
adox r15, r13
adcx r12, [ rsp - 0x10 ]
adcx rbx, rbp
adcx r8, r15
adox r9, r14
adcx rdi, r9
mov r13, 0x0 
adox r11, r13
adc r11, 0x0
mulx r10, r14, r11
xor r10, r10
adox r14, r12
mov r13, r10
adox r13, rbx
mov rbp, r10
adox rbp, r8
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], rbp
mov r12, r10
adox r12, rdi
mov rbx, r10
cmovo rbx, rdx
adcx r14, rbx
mov [ r15 + 0x0 ], r14
mov [ r15 + 0x18 ], r12
mov [ r15 + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6700
; seed 3947046610741624 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 554340 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=355, initial num_batches=31): 65690 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11850128080239564
; number reverted permutation / tried permutation: 70759 / 89865 =78.739%
; number reverted decision / tried decision: 49107 / 90134 =54.482%
; validated in 0.28s
