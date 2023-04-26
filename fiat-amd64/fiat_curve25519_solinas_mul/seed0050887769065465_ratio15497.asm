SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r11
mulx r11, rbp, [ rax + 0x0 ]
add r15, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mulx r13, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r15
mulx r15, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r9
mulx r9, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r10
mulx r10, r13, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rcx, r8
setc r8b
clc
adcx r13, rcx
setc cl
clc
adcx rbp, r14
adcx r12, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rax + 0x8 ]
mov rdx, 0x0 
adcx rbx, rdx
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx r13, rdi
setc dil
clc
adcx r14, rbp
adox r15, r14
adcx r11, r12
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, [ rax + 0x10 ]
adox r8, r11
mov rdx, 0x0 
mov r12, rdx
adcx r12, rbx
mov rdx, [ rax + 0x18 ]
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r14, rdx
clc
mov r11, -0x1 
movzx rcx, cl
adcx rcx, r11
adcx r15, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x10 ]
adcx r9, r8
adox rcx, r12
mov rdx, 0x0 
mov r8, rdx
adox r8, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, [ rax + 0x18 ]
mov rdx, 0x0 
adox r14, rdx
dec rdx
movzx rdi, dil
adox rdi, rdx
adox r15, r10
adox r9, [ rsp - 0x18 ]
adcx rcx, [ rsp - 0x20 ]
adox rbx, rcx
mov r10, 0x0 
mov rdi, r10
adcx rdi, r8
adox r12, rdi
adcx r14, r10
mov r8, [ rsp - 0x30 ]
clc
adcx r8, [ rsp - 0x28 ]
adcx r13, [ rsp - 0x38 ]
adcx r15, [ rsp - 0x10 ]
adcx r9, [ rsp - 0x40 ]
mov rcx, 0x26 
mov rdx, rcx
mulx rdi, rcx, r9
adox r14, r10
adcx rbp, rbx
adcx r11, r12
adcx r14, r10
mulx r12, rbx, rbp
mulx rbp, r9, r11
test al, al
adox rbx, r8
adox r9, r13
mulx r13, r8, r14
adcx rcx, [ rsp - 0x48 ]
adcx rdi, rbx
adox r8, r15
adcx r12, r9
adcx rbp, r8
adox r13, r10
adc r13, 0x0
mulx r11, r15, r13
test al, al
adox r15, rcx
mov r11, r10
adox r11, rdi
mov r14, r10
adox r14, r12
mov rbx, r10
adox rbx, rbp
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], r14
mov rcx, r10
cmovo rcx, rdx
adcx r15, rcx
mov [ r9 + 0x0 ], r15
mov [ r9 + 0x18 ], rbx
mov [ r9 + 0x8 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5497
; seed 0050887769065465 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7531 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 596 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07913955649980083
; number reverted permutation / tried permutation: 327 / 497 =65.795%
; number reverted decision / tried decision: 191 / 502 =38.048%
; validated in 0.573s
