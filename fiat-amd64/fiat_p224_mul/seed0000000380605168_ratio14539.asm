SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
add rcx, r11
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r11, rbx, r9
mov [ rsp - 0x78 ], rbp
mov rbp, 0xffffffff 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffffffffffff 
mov rdx, r9
mov [ rsp - 0x60 ], r14
mulx r14, r9, r13
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r15, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r10
mulx r10, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], rdi
mulx rdi, r13, [ rax + 0x0 ]
adox rbx, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r13
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r10
mulx r10, rdi, [ rax + 0x18 ]
adcx rcx, r8
adcx rdi, r13
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r15, rbx
setc r8b
clc
adcx r9, r11
adox r9, rcx
adcx rbp, r14
adcx r12, rdx
adox rbp, rdi
mov rdx, [ rax + 0x8 ]
mulx r14, r11, [ rsi + 0x8 ]
clc
adcx r11, [ rsp - 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r13, rbx, [ rsi + 0x8 ]
adcx rbx, r14
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rax + 0x18 ]
adcx rcx, r13
mov rdx, 0x0 
adcx rdi, rdx
clc
mov r14, -0x1 
movzx r8, r8b
adcx r8, r14
adcx r9, r11
adcx rbx, rbp
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx rbp, r15, r8
adox r12, r10
adcx rcx, r12
seto bpl
movzx rbp, bpl
adcx rbp, rdi
mov r10, 0xffffffff00000000 
xchg rdx, r10
mulx r13, r11, r15
mov rdx, r8
mulx rdi, r8, r15
inc r14
adox r8, r13
mov r12, r15
setc r13b
clc
adcx r12, r10
adcx r11, r9
mov r12, 0xffffffff 
mov rdx, r12
mulx r10, r12, r15
adcx r8, rbx
adox r12, rdi
adcx r12, rcx
adox r10, r14
adcx r10, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, [ rax + 0x8 ]
movzx rdx, r13b
adc rdx, 0x0
xor r15, r15
adox r9, [ rsp - 0x10 ]
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rcx, [ rax + 0x10 ]
adox rcx, rbx
adcx r11, [ rsp - 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx rdi, r13, r11
mulx rbx, rdi, r13
adcx r9, r8
adox rbp, [ rsp - 0x20 ]
adcx rcx, r12
adcx rbp, r10
mov r8, [ rsp - 0x28 ]
adox r8, r15
adcx r8, r14
mov r12, 0xffffffff00000000 
mov rdx, r12
mulx r10, r12, r13
mov r14, -0x3 
inc r14
adox rdi, r10
mov r10, r13
setc r14b
clc
adcx r10, r11
adcx r12, r9
mov r10, 0xffffffff 
mov rdx, r13
mulx r11, r13, r10
adox r13, rbx
adox r11, r15
adcx rdi, rcx
adcx r13, rbp
adcx r11, r8
mov rdx, [ rsi + 0x18 ]
mulx r9, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, rcx, [ rax + 0x8 ]
movzx rdx, r14b
adc rdx, 0x0
test al, al
adox rcx, [ rsp - 0x30 ]
adox rbx, rbp
adcx r12, [ rsp - 0x38 ]
adox r9, [ rsp - 0x40 ]
adcx rcx, rdi
mov r14, 0xffffffffffffffff 
xchg rdx, r12
mulx rdi, r8, r14
adcx rbx, r13
adcx r9, r11
mov rdi, [ rsp - 0x48 ]
adox rdi, r15
adcx rdi, r12
xchg rdx, r8
mulx r11, r13, r14
mov rbp, 0xffffffff00000000 
mulx r15, r12, rbp
mov r10, -0x2 
inc r10
adox r13, r15
mov r15, 0xffffffff 
mulx rbp, r10, r15
adox r10, r11
setc r11b
clc
adcx rdx, r8
adcx r12, rcx
adcx r13, rbx
adcx r10, r9
mov rdx, 0x0 
adox rbp, rdx
adcx rbp, rdi
movzx r8, r11b
adc r8, 0x0
mov rcx, r12
sub rcx, 0x00000001
mov rbx, r13
mov r9, 0xffffffff00000000 
sbb rbx, r9
mov r11, r10
sbb r11, r14
mov rdi, rbp
sbb rdi, r15
sbb r8, 0x00000000
cmovc rbx, r13
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rbx
cmovc r11, r10
mov [ r8 + 0x10 ], r11
cmovc rdi, rbp
mov [ r8 + 0x18 ], rdi
cmovc rcx, r12
mov [ r8 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4539
; seed 2378999681916132 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 942311 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=126, initial num_batches=31): 66551 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07062530311118091
; number reverted permutation / tried permutation: 67758 / 89791 =75.462%
; number reverted decision / tried decision: 51417 / 90208 =56.998%
; validated in 2.318s
