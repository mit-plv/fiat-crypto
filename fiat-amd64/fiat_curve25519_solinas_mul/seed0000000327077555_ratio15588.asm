SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
add r15, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rbp
mulx rbp, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r11, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], r10
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r14
mulx r14, r15, [ rsi + 0x18 ]
adcx r15, r10
mov rdx, 0x0 
adcx rbx, rdx
adox rdi, r15
mov r10, rdx
adox r10, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x8 ]
clc
adcx rcx, rbx
adcx r8, r11
mov rdx, [ rax + 0x10 ]
mulx rbx, r11, [ rsi + 0x10 ]
seto dl
mov [ rsp - 0x18 ], rbx
mov rbx, -0x2 
inc rbx
adox r9, rcx
adcx r11, rdi
mov dil, dl
mov rdx, [ rax + 0x10 ]
mulx rbx, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r15
mulx r15, rbx, [ rax + 0x10 ]
adox rbx, r8
adcx rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, [ rax + 0x18 ]
adox rbp, r11
movzx rdx, dil
lea rdx, [ rdx + r8 ]
adox r14, rcx
mov rdi, 0x0 
mov r11, rdi
adcx r11, rdx
setc cl
clc
adcx r13, r12
adcx r9, [ rsp - 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r8, r12, [ rsi + 0x18 ]
movzx rdx, cl
lea rdx, [ rdx + r8 ]
adcx rbx, [ rsp - 0x38 ]
adcx rbp, [ rsp - 0x30 ]
mov rcx, rdi
adox rcx, r11
adox rdx, rdi
mov r11, -0x3 
inc r11
adox r13, [ rsp - 0x8 ]
adox r9, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x28 ]
adox r15, rbp
adcx r10, r14
adox r10, [ rsp - 0x18 ]
adcx r12, rcx
adox r12, [ rsp - 0x10 ]
adcx rdx, rdi
adox rdx, rdi
mov r14, 0x26 
xchg rdx, r15
mulx rbp, r8, r14
mov rdx, r10
mulx rcx, r10, r14
mov rdx, r14
mulx rdi, r14, r12
add r10, r13
adcx r14, r9
inc r11
adox r8, [ rsp - 0x48 ]
adox rbp, r10
mulx r9, r13, r15
adcx r13, rbx
mov rbx, 0x0 
adcx r9, rbx
adox rcx, r14
adox rdi, r13
adox r9, rbx
mulx r15, r12, r9
test al, al
adox r12, r8
mov r15, rbx
adox r15, rbp
mov r10, rbx
adox r10, rcx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], r15
mov r8, rbx
adox r8, rdi
mov rbp, rbx
cmovo rbp, rdx
adcx r12, rbp
mov [ r14 + 0x0 ], r12
mov [ r14 + 0x10 ], r10
mov [ r14 + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5588
; seed 0204292457873445 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1236805 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 94316 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07625777709501498
; number reverted permutation / tried permutation: 63763 / 89916 =70.914%
; number reverted decision / tried decision: 31158 / 90083 =34.588%
; validated in 0.566s
