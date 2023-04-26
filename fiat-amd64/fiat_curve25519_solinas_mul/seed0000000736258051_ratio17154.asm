SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r13, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
adcx r10, r13
adox r12, r8
adcx r14, r12
mov rdx, 0x0 
adox rbx, rdx
mov r8, rdx
adcx r8, rbx
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rdi
mulx rdi, rbx, [ rax + 0x18 ]
adc rdi, 0x0
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rcx
mulx rcx, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, r12
adox rcx, r10
mov rdx, [ rax + 0x10 ]
mulx r12, r10, [ rsi + 0x18 ]
adox r9, r14
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r12
mulx r12, r14, [ rsi + 0x8 ]
adox r10, r8
adcx r14, rbx
mov rdx, [ rax + 0x10 ]
mulx rbx, r8, [ rsi + 0x8 ]
adcx r8, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rbx
mulx rbx, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], rbp
mulx rbp, rcx, [ rax + 0x0 ]
adcx r11, r9
mov rdx, 0x0 
mov r9, rdx
adox r9, rdi
adcx r15, r10
mov rdi, rdx
adcx rdi, r9
seto r10b
mov r9, -0x3 
inc r9
adox rcx, rbx
adox rbp, r14
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, [ rax + 0x18 ]
movzx rdx, r10b
lea rdx, [ rdx + rbx ]
mov r10, 0x0 
adcx rdx, r10
clc
adcx r13, rcx
adox r12, r8
adcx rbp, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x30 ]
adox r11, [ rsp - 0x40 ]
adox r15, [ rsp - 0x38 ]
adox r14, rdi
adcx r11, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x48 ]
adox rdx, r10
adcx r14, [ rsp - 0x28 ]
adcx rdx, r10
mov r8, 0x26 
mulx rcx, rdi, r8
mov rdx, r8
mulx rbx, r8, r11
mulx r10, r11, r15
mulx r9, r15, r14
xor r14, r14
adox r11, r13
adox r15, rbp
adcx r8, [ rsp - 0x18 ]
adcx rbx, r11
adox rdi, r12
adcx r10, r15
adcx r9, rdi
adox rcx, r14
adc rcx, 0x0
mulx rbp, r13, rcx
xor rbp, rbp
adox r13, r8
mov r14, rbp
adox r14, rbx
mov r12, rbp
adox r12, r10
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], r14
mov r15, rbp
adox r15, r9
mov [ r11 + 0x18 ], r15
mov r8, rbp
cmovo r8, rdx
adcx r13, r8
mov [ r11 + 0x10 ], r12
mov [ r11 + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7154
; seed 0288121036213902 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 751599 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=220, initial num_batches=31): 65607 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08728989793759705
; number reverted permutation / tried permutation: 67647 / 90148 =75.040%
; number reverted decision / tried decision: 51711 / 89851 =57.552%
; validated in 0.476s
