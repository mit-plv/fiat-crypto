SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
test al, al
adox rbp, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mulx r13, r8, rcx
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
mov [ rsp - 0x58 ], r15
mov r15, 0xffffffff00000000 
mov rdx, r8
mov [ rsp - 0x50 ], rdi
mulx rdi, r8, r15
adcx r13, rdi
mov rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r9
mulx r9, r15, [ rsi + 0x0 ]
adox r15, r12
adox r10, r9
mov rdx, 0x0 
adox r11, rdx
mov r12, 0xffffffff 
mov rdx, rdi
mulx r9, rdi, r12
mov r12, -0x2 
inc r12
adox rdx, rcx
adox r8, rbp
adox r13, r15
mov rdx, [ rax + 0x8 ]
mulx rbp, rcx, [ rsi + 0x8 ]
adcx rdi, r14
adox rdi, r10
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx rcx, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, [ rax + 0x18 ]
adcx r14, rbp
adcx rbx, r15
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r8, [ rsp - 0x48 ]
adcx rcx, r13
adcx r14, rdi
adox r9, r11
adcx rbx, r9
mov r11, 0xffffffffffffffff 
mov rdx, r8
mulx r13, r8, r11
mov r13, 0xffffffff00000000 
xchg rdx, r8
mulx rdi, rbp, r13
mulx r9, r15, r11
mov r12, 0xffffffff 
mulx r11, r13, r12
setc r12b
clc
adcx r15, rdi
adcx r13, r9
movzx rdi, r12b
adox rdi, r10
seto r10b
mov r12, -0x2 
inc r12
adox rdx, r8
adox rbp, rcx
adox r15, r14
adox r13, rbx
mov rdx, 0x0 
adcx r11, rdx
adox r11, rdi
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx rbx, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx rdi, r9, [ rsi + 0x10 ]
clc
adcx r8, rbx
adcx r9, rcx
movzx rdx, r10b
mov rcx, 0x0 
adox rdx, rcx
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbx, [ rax + 0x18 ]
inc r12
adox r14, rbp
adcx rbx, rdi
mov rdx, 0xffffffffffffffff 
mulx rdi, rbp, r14
adox r8, r15
adox r9, r13
mov rdx, [ rax + 0x8 ]
mulx r15, rdi, [ rsi + 0x18 ]
adox rbx, r11
adcx rcx, r12
adox rcx, r10
mov rdx, 0xffffffff00000000 
mulx r11, r13, rbp
mov r10, rbp
clc
adcx r10, r14
adcx r13, r8
mov r10, 0xffffffffffffffff 
mov rdx, rbp
mulx r14, rbp, r10
seto r8b
mov r10, -0x3 
inc r10
adox rbp, r11
mov r11, 0xffffffff 
mulx r10, r12, r11
adox r12, r14
adcx rbp, r9
adcx r12, rbx
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r9, r13
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r14, r13, r9
mov rdx, [ rax + 0x10 ]
mulx r11, r14, [ rsi + 0x18 ]
adcx r10, rcx
movzx rdx, r8b
mov rcx, 0x0 
adcx rdx, rcx
clc
adcx rdi, rbx
adox rdi, rbp
adcx r14, r15
adox r14, r12
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mulx rbp, r8, [ rsi + 0x18 ]
adcx r8, r11
adcx rbp, rcx
adox r8, r10
adox rbp, r15
mov rdx, 0xffffffffffffffff 
mulx rbx, r12, r13
mov r11, 0xffffffff00000000 
mov rdx, r13
mulx r10, r13, r11
clc
adcx r12, r10
mov r15, rdx
seto r10b
mov r11, -0x3 
inc r11
adox r15, r9
mov r15, 0xffffffff 
mulx rcx, r9, r15
adcx r9, rbx
mov rdx, 0x0 
adcx rcx, rdx
adox r13, rdi
adox r12, r14
adox r9, r8
adox rcx, rbp
movzx rdi, r10b
adox rdi, rdx
mov r14, r13
sub r14, 0x00000001
mov r8, r12
mov r10, 0xffffffff00000000 
sbb r8, r10
mov rbp, r9
mov rbx, 0xffffffffffffffff 
sbb rbp, rbx
mov rdx, rcx
sbb rdx, r15
sbb rdi, 0x00000000
cmovc rbp, r9
cmovc r14, r13
cmovc rdx, rcx
cmovc r8, r12
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x10 ], rbp
mov [ rdi + 0x0 ], r14
mov [ rdi + 0x18 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5952
; seed 4189333048515104 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1928901 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=84, initial num_batches=31): 119195 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06179425486326152
; number reverted permutation / tried permutation: 67648 / 90056 =75.118%
; number reverted decision / tried decision: 44623 / 89943 =49.613%
; validated in 3.871s
