SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r10
mov r8, 0xffffffff 
mov rdx, r8
mulx r9, r8, rcx
mov [ rsp - 0x80 ], rbx
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rcx
test al, al
adox rcx, r10
adcx rbx, r15
adcx r8, rbp
mov rcx, 0x0 
adcx r9, rcx
clc
adcx r12, r11
adox r14, r12
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
adcx r10, r13
adox rbx, r10
mov rdx, [ rax + 0x18 ]
mulx r13, rbp, [ rsi + 0x0 ]
adcx rbp, r11
adcx r13, rcx
adox r8, rbp
mov rdx, [ rax + 0x0 ]
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r10, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx rcx, rbp, [ rsi + 0x10 ]
clc
adcx rbp, r12
adcx r11, rcx
adox r9, r13
mov rdx, [ rax + 0x18 ]
mulx r12, r13, [ rsi + 0x10 ]
adcx r13, r10
mov rdx, [ rax + 0x0 ]
mulx rcx, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rax + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx r10, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r12
mulx r12, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], rbp
mulx rbp, r11, r10
mov [ rsp - 0x28 ], r15
mulx r15, rbp, r11
seto dl
mov [ rsp - 0x20 ], r15
mov r15, -0x2 
inc r15
adox rdi, rcx
adox r14, r13
adcx rdi, rbx
adcx r14, r8
mov bl, dl
mov rdx, [ rax + 0x18 ]
mulx rcx, r8, [ rsi + 0x8 ]
adox r8, r12
adcx r8, r9
mov rdx, 0x0 
adox rcx, rdx
movzx r9, bl
adcx r9, rcx
mov rdx, [ rax + 0x8 ]
mulx r13, rbx, [ rsi + 0x18 ]
mov rdx, r11
inc r15
adox rdx, r10
mov rdx, [ rsi + 0x18 ]
mulx r12, r10, [ rax + 0x0 ]
mov rdx, 0xffffffff00000000 
mulx r15, rcx, r11
adox rcx, rdi
setc dil
clc
adcx rbx, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
adcx r12, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r12
mulx r12, r13, [ rax + 0x18 ]
adcx r13, rbx
mov rdx, 0xffffffff 
mov [ rsp - 0x8 ], r13
mulx r13, rbx, r11
mov r11, 0x0 
adcx r12, r11
clc
adcx rbp, r15
adcx rbx, [ rsp - 0x20 ]
adcx r13, r11
adox rbp, r14
adox rbx, r8
clc
adcx rcx, [ rsp - 0x28 ]
adcx rbp, [ rsp - 0x30 ]
mov r14, 0xffffffffffffffff 
mov rdx, rcx
mulx r8, rcx, r14
adox r13, r9
movzx r8, dil
adox r8, r11
adcx rbx, [ rsp - 0x38 ]
mov rdi, rcx
mov r9, -0x3 
inc r9
adox rdi, rdx
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mulx r15, rcx, rdi
adox rcx, rbp
adcx r13, [ rsp - 0x48 ]
mulx r11, rbp, r14
adcx r8, [ rsp - 0x40 ]
setc r9b
clc
adcx rbp, r15
mov r15, 0xffffffff 
mulx r14, rdi, r15
adcx rdi, r11
adox rbp, rbx
mov rdx, 0x0 
adcx r14, rdx
adox rdi, r13
adox r14, r8
movzx rbx, r9b
adox rbx, rdx
add r10, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r13, rcx, r10
mov r13, rcx
mov r11, -0x2 
inc r11
adox r13, r10
adcx rbp, [ rsp - 0x18 ]
adcx rdi, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x8 ]
mov r13, 0xffffffff00000000 
mov rdx, rcx
mulx r9, rcx, r13
adcx r12, rbx
adox rcx, rbp
mov r8, 0xffffffffffffffff 
mulx r10, rbx, r8
setc bpl
clc
adcx rbx, r9
adox rbx, rdi
mulx r9, rdi, r15
adcx rdi, r10
mov rdx, 0x0 
adcx r9, rdx
adox rdi, r14
adox r9, r12
movzx r14, bpl
adox r14, rdx
mov rbp, rcx
sub rbp, 0x00000001
mov r12, rbx
sbb r12, r13
mov r10, rdi
sbb r10, r8
mov rdx, r9
sbb rdx, r15
sbb r14, 0x00000000
cmovc rdx, r9
cmovc r12, rbx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], r12
mov [ r14 + 0x18 ], rdx
cmovc rbp, rcx
cmovc r10, rdi
mov [ r14 + 0x10 ], r10
mov [ r14 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7614
; seed 1117979555226023 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1015827 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=183, initial num_batches=31): 78822 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07759392101214084
; number reverted permutation / tried permutation: 75328 / 89494 =84.171%
; number reverted decision / tried decision: 62523 / 90505 =69.082%
; validated in 1.996s
