SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
test al, al
adox r11, r10
mov rdx, 0xffffffff00000001 
mulx r9, r8, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
adox r10, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mulx rbp, rcx, rax
mov [ rsp - 0x70 ], r12
mov r12, 0xffffffff 
mov rdx, rax
mov [ rsp - 0x68 ], r13
mulx r13, rax, r12
adcx rax, rbp
mov rbp, 0x0 
adcx r13, rbp
clc
adcx rcx, rdx
adcx rax, r11
adcx r13, r10
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rsi + 0x18 ]
adox rcx, rbx
adcx r8, rcx
adox r11, rbp
mov rdx, [ rsi + 0x0 ]
mulx r10, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rcx, r10
adcx r9, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, r11, [ rsi + 0x8 ]
adox r14, rbp
adox r11, r15
setc dl
clc
adcx rbx, rax
xchg rdx, r12
mulx rbp, rax, rbx
adcx rcx, r13
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r15, r13, rbx
adcx r14, r8
mov r8, 0x0 
adox r10, r8
adcx r11, r9
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x8 ]
movzx rdx, r12b
adcx rdx, r10
mov r12, -0x2 
inc r12
adox rdi, r8
setc r10b
clc
adcx rax, r15
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx r13, rbx
adox r8, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r13, rdx
adcx rax, rcx
adox r13, r12
mov rdx, 0xffffffff00000001 
mulx r12, rcx, rbx
adcx rbp, r14
adcx rcx, r11
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r13
mulx r13, r11, [ rsi + 0x10 ]
adcx r12, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r8
mulx r8, r15, [ rsi + 0x18 ]
movzx rdx, r10b
mov [ rsp - 0x30 ], rdi
mov rdi, 0x0 
adcx rdx, rdi
clc
adcx rbx, r13
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r13, rdx
adcx r13, r14
adcx r15, rdi
mov rdx, 0x0 
adcx r8, rdx
adox r9, rdx
xor r14, r14
adox r11, rax
mov rdx, 0xffffffff00000001 
mulx rdi, rax, r11
adox rbx, rbp
adox r13, rcx
adox r15, r12
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx rcx, rbp, r11
mov r12, 0xffffffff 
mov rdx, r12
mulx r14, r12, r11
adcx r12, rcx
mov rcx, 0x0 
adcx r14, rcx
adox r8, r10
clc
adcx rbp, r11
adcx r12, rbx
seto bpl
mov r10, -0x3 
inc r10
adox r12, [ rsp - 0x48 ]
adcx r14, r13
adox r14, [ rsp - 0x30 ]
adcx rax, r15
adox rax, [ rsp - 0x38 ]
adcx rdi, r8
movzx r11, bpl
adcx r11, rcx
adox rdi, [ rsp - 0x40 ]
adox r9, r11
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r13, rbx, r12
clc
adcx rbx, r12
mov rbx, 0xffffffff 
mov rdx, r12
mulx r15, r12, rbx
seto bpl
mov r8, -0x3 
inc r8
adox r12, r13
adox r15, rcx
adcx r12, r14
adcx r15, rax
mov r8, 0xffffffff00000001 
mulx rax, r14, r8
adcx r14, rdi
adcx rax, r9
movzx rdx, bpl
adc rdx, 0x0
mov r11, r12
mov rdi, 0xffffffffffffffff 
sub r11, rdi
mov rbp, r15
sbb rbp, rbx
mov r9, r14
sbb r9, 0x00000000
mov r13, rax
sbb r13, r8
sbb rdx, 0x00000000
cmovc r11, r12
cmovc r9, r14
cmovc r13, rax
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r11
mov [ rdx + 0x18 ], r13
mov [ rdx + 0x10 ], r9
cmovc rbp, r15
mov [ rdx + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5749
; seed 2950670762749632 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1736991 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=95, initial num_batches=31): 110558 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06364914959260008
; number reverted permutation / tried permutation: 72585 / 90084 =80.575%
; number reverted decision / tried decision: 41041 / 89915 =45.644%
; validated in 1.941s
