SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r8, rax
mov r9, 0xffffffff00000000 
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r8
xor rdx, rdx
adox r15, rbx
mov rbx, 0xffffffff 
mov rdx, r8
mov [ rsp - 0x48 ], r12
mulx r12, r8, rbx
adox r8, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
adcx r13, r10
adcx r11, r14
adcx rbx, rcx
mov rdx, 0x0 
adcx rbp, rdx
adox r12, rdx
test al, al
adox rdi, rax
adox r9, r13
mov rdx, [ rsi + 0x8 ]
mulx rax, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rsi + 0x0 ]
adox r15, r11
adox r8, rbx
adcx rdi, rcx
adox r12, rbp
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, [ rsi + 0x8 ]
adcx r14, rax
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, [ rsi + 0x18 ]
seto dl
mov rbp, -0x2 
inc rbp
adox r10, r9
adox rdi, r15
mov r9, 0xffffffffffffffff 
xchg rdx, r10
mulx rcx, rax, r9
adcx r11, r13
adox r14, r8
mov rcx, 0x0 
adcx rbx, rcx
adox r11, r12
movzx r15, r10b
adox r15, rbx
mov r8, rax
clc
adcx r8, rdx
mov r8, 0xffffffff00000000 
mov rdx, rax
mulx r10, rax, r8
mulx r13, r12, r9
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rcx, [ rsi + 0x8 ]
seto dl
mov r8, -0x2 
inc r8
adox r12, r10
adcx rax, rdi
mov rdi, 0xffffffff 
xchg rdx, rbx
mulx r8, r10, rdi
adox r10, r13
adcx r12, r14
adcx r10, r11
mov rdx, 0x0 
adox r8, rdx
adcx r8, r15
mov rdx, [ rsi + 0x10 ]
mulx r11, r14, [ rsi + 0x0 ]
movzx rdx, bl
adc rdx, 0x0
add r14, rax
xchg rdx, r14
mulx r15, rbx, r9
xchg rdx, rbx
mulx r13, r15, r9
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rcx, r11
adcx rcx, r12
mov rdx, [ rsi + 0x10 ]
mulx r11, r12, rdx
adox r12, rbp
adox rdi, r11
mov rdx, 0x0 
adox r9, rdx
adcx r12, r10
adcx rdi, r8
adcx r9, r14
mov rbp, 0xffffffff00000000 
mov rdx, rax
mulx r10, rax, rbp
mov r8, rdx
mov r14, -0x2 
inc r14
adox r8, rbx
adox rax, rcx
setc r8b
clc
adcx r15, r10
mov rbx, 0xffffffff 
mulx r11, rcx, rbx
adox r15, r12
adcx rcx, r13
mov rdx, 0x0 
adcx r11, rdx
adox rcx, rdi
adox r11, r9
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rsi + 0x8 ]
movzx rdx, r8b
mov r10, 0x0 
adox rdx, r10
test al, al
adox r13, rax
mov r8, 0xffffffffffffffff 
xchg rdx, r13
mulx r10, rax, r8
adcx rdi, r12
adcx r9, [ rsp - 0x40 ]
adox rdi, r15
xchg rdx, rax
mulx r15, r10, rbx
adox r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, rdx
adcx r12, [ rsp - 0x48 ]
mov rdx, rcx
mulx rbx, rcx, r8
mov rbp, 0x0 
adcx r14, rbp
adox r12, r11
mov r11, 0xffffffff00000000 
mulx r8, rbp, r11
clc
adcx rdx, rax
adcx rbp, rdi
adox r14, r13
seto dl
mov r13, -0x2 
inc r13
adox rcx, r8
adox r10, rbx
mov rax, 0x0 
adox r15, rax
adcx rcx, r9
adcx r10, r12
adcx r15, r14
movzx rdi, dl
adc rdi, 0x0
mov r9, rbp
sub r9, 0x00000001
mov rbx, rcx
sbb rbx, r11
mov r12, r10
mov r8, 0xffffffffffffffff 
sbb r12, r8
mov rdx, r15
mov r14, 0xffffffff 
sbb rdx, r14
sbb rdi, 0x00000000
cmovc rdx, r15
cmovc r9, rbp
cmovc rbx, rcx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], rdx
mov [ rdi + 0x0 ], r9
cmovc r12, r10
mov [ rdi + 0x10 ], r12
mov [ rdi + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.4560
; seed 2998627536775192 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2026119 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 128971 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0636542078722918
; number reverted permutation / tried permutation: 74169 / 89946 =82.459%
; number reverted decision / tried decision: 46907 / 90053 =52.088%
; validated in 3.32s
