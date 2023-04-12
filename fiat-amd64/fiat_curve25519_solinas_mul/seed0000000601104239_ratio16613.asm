SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
test al, al
adox r13, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r11
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r9
mulx r9, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], rdi
mulx rdi, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r9
mulx r9, r8, [ rax + 0x8 ]
adcx rbp, r13
adox r8, rbx
mov rdx, [ rax + 0x18 ]
mulx r13, rbx, [ rsi + 0x8 ]
adcx r14, r8
mov rdx, 0x0 
adox r13, rdx
mov r8, rdx
adcx r8, r13
adc r12, 0x0
add rcx, r11
mov rdx, [ rax + 0x10 ]
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r15, rcx
adcx rdi, rbp
adcx r11, r14
adcx r10, r8
mov rbp, 0x0 
mov r14, rbp
adcx r14, r12
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x8 ]
adox r8, rdi
adox r11, [ rsp - 0x18 ]
adox r9, r10
mov rdx, rbp
adox rdx, r14
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rbp, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r13
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r10, rdx
adox r10, rdx
mov [ rsp + 0x0 ], r12
xor r12, r12
adox r14, rbp
adcx r14, [ rsp - 0x20 ]
adox r13, r15
adox r8, [ rsp - 0x28 ]
adcx r13, [ rsp - 0x30 ]
adcx r8, [ rsp - 0x38 ]
adox rbx, r11
adox r9, [ rsp - 0x40 ]
adox rdi, rcx
adox r10, r12
adcx rbx, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rdx, 0x26 
mulx r11, r15, r9
mulx rbp, rcx, rbx
adcx rdi, [ rsp - 0x48 ]
mulx r9, rbx, rdi
adcx r10, r12
mulx r12, rdi, r10
xor r10, r10
adox r15, r14
adox rbx, r13
adox rdi, r8
adcx rcx, [ rsp - 0x10 ]
adcx rbp, r15
adcx r11, rbx
adcx r9, rdi
adox r12, r10
adc r12, 0x0
mulx r13, r14, r12
xor r13, r13
adox r14, rcx
mov r10, r13
adox r10, rbp
mov r8, r13
adox r8, r11
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r10
mov [ r15 + 0x10 ], r8
mov rbx, r13
adox rbx, r9
mov rdi, r13
cmovo rdi, rdx
adcx r14, rdi
mov [ r15 + 0x18 ], rbx
mov [ r15 + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6613
; seed 0861115796630503 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 559645 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=355, initial num_batches=31): 66929 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11959188414083928
; number reverted permutation / tried permutation: 70613 / 89868 =78.574%
; number reverted decision / tried decision: 49508 / 90131 =54.929%
; validated in 0.286s
