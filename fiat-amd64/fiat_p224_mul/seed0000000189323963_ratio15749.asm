SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r9
mov r14, 0xffffffff 
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, r13
add r10, r8
adcx rbp, r11
mov rdx, [ rax + 0x18 ]
mulx r8, r11, [ rsi + 0x18 ]
adcx r11, r12
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x40 ], r11
mulx r11, r12, r13
adc r8, 0x0
test al, al
adox rdi, r11
adox r14, rcx
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbp
mulx rbp, r8, [ rsi + 0x0 ]
adcx r8, rbx
adcx rcx, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, rbx, [ rsi + 0x0 ]
adcx rbx, r11
mov rdx, 0x0 
adox r15, rdx
adc rbp, 0x0
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r10
mulx r10, r11, [ rsi + 0x8 ]
test al, al
adox r13, r9
adox r12, r8
adox rdi, rcx
mov rdx, [ rax + 0x0 ]
mulx r9, r13, [ rsi + 0x8 ]
adox r14, rbx
mov rdx, [ rax + 0x10 ]
mulx rcx, r8, [ rsi + 0x8 ]
adcx r13, r12
mov rdx, 0xffffffffffffffff 
mulx r12, rbx, r13
adox r15, rbp
seto r12b
mov rbp, -0x2 
inc rbp
adox r11, r9
adcx r11, rdi
adox r8, r10
mov rdx, [ rax + 0x18 ]
mulx rdi, r10, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx rbp, r9, rbx
adcx r8, r14
adox r10, rcx
mov r14, 0x0 
adox rdi, r14
mov rcx, 0xffffffff00000000 
mov rdx, rcx
mulx r14, rcx, rbx
adcx r10, r15
movzx r15, r12b
adcx r15, rdi
mov r12, rbx
mov rdi, -0x2 
inc rdi
adox r12, r13
setc r12b
clc
adcx r9, r14
mov rdx, [ rax + 0x8 ]
mulx r14, r13, [ rsi + 0x10 ]
adox rcx, r11
mov rdx, 0xffffffff 
mulx rdi, r11, rbx
adox r9, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rbx, [ rax + 0x10 ]
adcx r11, rbp
adox r11, r10
mov rdx, [ rax + 0x0 ]
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rdi, rdx
adox rdi, r15
clc
adcx r13, r10
movzx r15, r12b
adox r15, rdx
mov r12, -0x3 
inc r12
adox rbp, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rbp
mulx r10, rbp, rcx
xchg rdx, rcx
mulx r12, r10, rbp
adox r13, r9
adcx rbx, r14
mov rdx, [ rsi + 0x10 ]
mulx r9, r14, [ rax + 0x18 ]
adcx r14, r8
mov rdx, 0x0 
adcx r9, rdx
mov r8, rbp
clc
adcx r8, rcx
adox rbx, r11
adox r14, rdi
mov r8, 0xffffffff00000000 
mov rdx, rbp
mulx r11, rbp, r8
adox r9, r15
adcx rbp, r13
seto dil
mov r15, -0x2 
inc r15
adox r10, r11
adcx r10, rbx
mov rcx, 0xffffffff 
mulx rbx, r13, rcx
adox r13, r12
adcx r13, r14
mov rdx, 0x0 
adox rbx, rdx
adcx rbx, r9
movzx r12, dil
adc r12, 0x0
test al, al
adox rbp, [ rsp - 0x48 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r11, r14, rbp
adox r10, [ rsp - 0x28 ]
mov rdx, r8
mulx r8, r11, r14
adox r13, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x40 ]
adox r12, [ rsp - 0x38 ]
mov rdi, r14
adcx rdi, rbp
mov rdi, 0xffffffffffffffff 
mov rdx, r14
mulx r9, r14, rdi
adcx r11, r10
seto bpl
inc r15
adox r14, r8
adcx r14, r13
mulx r8, r10, rcx
adox r10, r9
adcx r10, rbx
adox r8, r15
adcx r8, r12
movzx rdx, bpl
adc rdx, 0x0
mov r13, r11
sub r13, 0x00000001
mov rbx, r14
mov rbp, 0xffffffff00000000 
sbb rbx, rbp
mov r12, r10
sbb r12, rdi
mov r9, r8
sbb r9, rcx
sbb rdx, 0x00000000
cmovc rbx, r14
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], rbx
cmovc r12, r10
cmovc r13, r11
mov [ rdx + 0x10 ], r12
mov [ rdx + 0x0 ], r13
cmovc r9, r8
mov [ rdx + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5749
; seed 2292702336105464 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1376014 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 86379 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06277479734944558
; number reverted permutation / tried permutation: 64374 / 89822 =71.668%
; number reverted decision / tried decision: 56833 / 90177 =63.024%
; validated in 3.761s
