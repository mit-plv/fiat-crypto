SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
add r10, rbx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, rbx, [ rsi + 0x18 ]
adcx rbx, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rcx
mulx rcx, r12, [ rsi + 0x8 ]
adc rcx, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r12
mulx r12, r9, [ rax + 0x8 ]
test al, al
adox r9, r10
adox r11, rbx
adcx r13, rdi
adcx r14, r9
mov rdx, 0x0 
mov r10, rdx
adox r10, rcx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rax + 0x10 ]
adcx rbx, r11
mov rdx, [ rax + 0x18 ]
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
adcx r11, r10
mov rdx, -0x2 
inc rdx
adox rdi, r13
adox rbp, r14
mov r13, 0x0 
mov r14, r13
adcx r14, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r10, [ rsi + 0x18 ]
adcx r9, r13
adox r12, rbx
adox r15, r11
mov rdx, r13
adox rdx, r14
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mulx r14, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r10
mulx r10, r13, [ rax + 0x0 ]
mov rdx, 0x0 
adox r9, rdx
mov [ rsp - 0x8 ], r13
xor r13, r13
adox r11, r10
adox r14, rdi
adcx r8, r11
adox rcx, rbp
adox r12, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
adcx rcx, [ rsp - 0x40 ]
adox r15, [ rsp - 0x18 ]
adox rbx, [ rsp - 0x10 ]
adox r9, r13
adcx r12, [ rsp - 0x48 ]
adcx r15, [ rsp - 0x28 ]
adcx rbx, [ rsp - 0x20 ]
mov rdx, 0x26 
mulx rbp, rdi, r15
mulx r11, r10, rbx
adcx r9, r13
mulx rbx, r15, r12
mulx r13, r12, r9
xor r9, r9
adox r15, [ rsp - 0x8 ]
adcx rdi, r8
adcx r10, r14
adcx r12, rcx
adcx r13, r9
adox rbx, rdi
adox rbp, r10
adox r11, r12
adox r13, r9
mulx r14, r8, r13
test al, al
adox r8, r15
mov r14, r9
adox r14, rbx
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r14
mov r15, r9
adox r15, rbp
mov [ rcx + 0x10 ], r15
mov rdi, r9
adox rdi, r11
mov r10, r9
cmovo r10, rdx
adcx r8, r10
mov [ rcx + 0x0 ], r8
mov [ rcx + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6259
; seed 1469099617568744 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 607470 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=305, initial num_batches=31): 67120 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11049105305611799
; number reverted permutation / tried permutation: 72302 / 89832 =80.486%
; number reverted decision / tried decision: 50925 / 90167 =56.479%
; validated in 0.317s
