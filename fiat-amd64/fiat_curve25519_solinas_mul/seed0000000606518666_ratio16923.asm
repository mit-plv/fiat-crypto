SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rcx
mulx rcx, r15, [ rax + 0x8 ]
add r10, rbx
adcx r15, r8
mov rdx, [ rsi + 0x10 ]
mulx rbx, r8, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r8, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r9
mulx r9, r10, [ rax + 0x18 ]
mov rdx, 0x0 
adcx r9, rdx
adox r11, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r10
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r10
mov [ rsp - 0x20 ], rbp
mulx rbp, r10, [ rax + 0x18 ]
mov rdx, 0x0 
mov [ rsp - 0x18 ], r10
mov r10, rdx
adox r10, r9
adox rbp, rdx
test al, al
adox r13, r12
adox r14, r8
adox r15, r11
mov rdx, [ rax + 0x10 ]
mulx r8, r12, [ rsi + 0x18 ]
adox r12, r10
mov rdx, [ rax + 0x8 ]
mulx r11, r9, [ rsi + 0x8 ]
adcx r9, r13
mov rdx, [ rax + 0x10 ]
mulx r13, r10, [ rsi + 0x8 ]
adcx r10, r14
adcx rbx, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, [ rax + 0x18 ]
mov rdx, 0x0 
mov [ rsp - 0x10 ], r8
mov r8, rdx
adox r8, rbp
adox r15, rdx
adcx rcx, r12
mov rbp, rdx
adcx rbp, r8
adcx r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rax + 0x0 ]
test al, al
adox r12, rdi
adox r8, r9
adcx r12, [ rsp - 0x20 ]
adcx r8, [ rsp - 0x38 ]
adox r11, r10
adox rbx, [ rsp - 0x30 ]
adox rcx, [ rsp - 0x18 ]
adox r14, rbp
adcx r11, [ rsp - 0x40 ]
adcx r13, rbx
adcx rcx, [ rsp - 0x28 ]
mov rdx, 0x26 
mulx r9, rdi, rcx
adcx r14, [ rsp - 0x10 ]
mov r10, 0x0 
adox r15, r10
adcx r15, r10
mulx rbx, rbp, r13
mulx rcx, r13, r15
mulx r10, r15, r14
xor r14, r14
adox rdi, r12
adox r15, r8
adcx rbp, [ rsp - 0x48 ]
adcx rbx, rdi
adcx r9, r15
adox r13, r11
adcx r10, r13
adox rcx, r14
adc rcx, 0x0
mulx r8, r12, rcx
xor r8, r8
adox r12, rbp
mov r14, r8
adox r14, rbx
mov r11, r8
adox r11, r9
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], r11
mov r15, r8
adox r15, r10
mov [ rdi + 0x18 ], r15
mov rbp, r8
cmovo rbp, rdx
adcx r12, rbp
mov [ rdi + 0x8 ], r14
mov [ rdi + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6923
; seed 4330723312185845 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 575047 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=355, initial num_batches=31): 67410 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11722520072272354
; number reverted permutation / tried permutation: 72162 / 89855 =80.309%
; number reverted decision / tried decision: 52038 / 90144 =57.728%
; validated in 0.276s
