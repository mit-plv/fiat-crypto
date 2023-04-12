SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
add r13, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rdi
mulx rdi, rbx, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rcx
mulx rcx, r15, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rbp, rdi
mov rdi, 0x0 
adox r12, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, rdi, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rbx, r9
adcx rdi, r14
adox rbp, r13
mov rdx, [ rax + 0x18 ]
mulx r14, rbx, [ rsi + 0x0 ]
adcx rbx, rcx
mov rdx, 0x0 
adcx r14, rdx
adox r12, rdi
mov r13, 0xffffffff00000001 
mov rdx, r13
mulx rcx, r13, r9
mov rdx, [ rsi + 0x8 ]
mulx rdi, r9, [ rax + 0x10 ]
adox r13, rbx
clc
adcx r10, r8
adcx r9, r11
mov rdx, [ rax + 0x18 ]
mulx r8, r11, [ rsi + 0x8 ]
adox rcx, r14
adcx r11, rdi
seto dl
mov rbx, -0x2 
inc rbx
adox rbp, [ rsp - 0x38 ]
adox r10, r12
mov r14, 0xffffffffffffffff 
xchg rdx, rbp
mulx rdi, r12, r14
adox r9, r13
mov r13, 0x0 
adcx r8, r13
mov r13, 0xffffffff 
mulx r14, rbx, r13
adox r11, rcx
clc
adcx rbx, rdi
movzx rcx, bpl
adox rcx, r8
mov rbp, 0x0 
adcx r14, rbp
clc
adcx r12, rdx
adcx rbx, r10
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx rdi, r10, [ rsi + 0x10 ]
adcx r14, r9
mov rdx, [ rax + 0x0 ]
mulx r8, r9, [ rsi + 0x10 ]
seto dl
mov r13, -0x3 
inc r13
adox r9, rbx
mov rbx, 0xffffffff 
xchg rdx, r9
mulx r13, rbp, rbx
mov rbx, 0xffffffff00000001 
xchg rdx, r12
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, rbx
adcx r15, r11
adcx rdi, rcx
mov rdx, 0xffffffffffffffff 
mulx rcx, r11, r12
movzx rdx, r9b
mov rbx, 0x0 
adcx rdx, rbx
clc
adcx rbp, rcx
adcx r13, rbx
clc
adcx r8, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
adox r8, r14
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mulx rcx, r14, [ rsi + 0x10 ]
adox r10, r15
adcx r14, [ rsp - 0x20 ]
adox r14, rdi
adcx rcx, rbx
adox rcx, r9
clc
adcx r11, r12
adcx rbp, r8
mov rdx, [ rax + 0x0 ]
mulx r15, r11, [ rsi + 0x18 ]
seto dl
mov rdi, -0x3 
inc rdi
adox r11, rbp
mov r9, 0xffffffff00000001 
xchg rdx, r9
mulx rbp, r8, r12
mov r12, 0xffffffffffffffff 
mov rdx, r11
mulx rbx, r11, r12
adcx r13, r10
adcx r8, r14
adcx rbp, rcx
mov r10, 0xffffffff 
mulx rcx, r14, r10
movzx rdi, r9b
mov r10, 0x0 
adcx rdi, r10
clc
adcx r14, rbx
adcx rcx, r10
clc
adcx r15, [ rsp - 0x28 ]
adox r15, r13
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mulx r13, rbx, [ rsi + 0x18 ]
adcx rbx, [ rsp - 0x30 ]
adox rbx, r8
mov rdx, [ rax + 0x18 ]
mulx r10, r8, [ rsi + 0x18 ]
adcx r8, r13
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r11, r9
adcx r14, r15
mov r11, 0xffffffff00000001 
mov rdx, r9
mulx r15, r9, r11
adox r8, rbp
adcx rcx, rbx
adox r10, rdi
adcx r9, r8
adcx r15, r10
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbp, r14
sub rbp, r12
mov rdi, rcx
mov r13, 0xffffffff 
sbb rdi, r13
mov rbx, r9
sbb rbx, 0x00000000
mov r8, r15
sbb r8, r11
movzx r10, dl
sbb r10, 0x00000000
cmovc rbp, r14
cmovc rbx, r9
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], rbx
mov [ r10 + 0x0 ], rbp
cmovc r8, r15
cmovc rdi, rcx
mov [ r10 + 0x18 ], r8
mov [ r10 + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.6604
; seed 2698953957908821 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1681389 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 108766 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06468818340074783
; number reverted permutation / tried permutation: 70553 / 90307 =78.126%
; number reverted decision / tried decision: 39021 / 89692 =43.506%
; validated in 2.334s
