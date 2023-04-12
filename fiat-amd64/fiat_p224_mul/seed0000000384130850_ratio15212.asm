SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
add r10, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mulx r13, r8, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
adcx r13, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mulx r15, r11, r8
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, r8
mov rdx, -0x2 
inc rdx
adox r11, r12
adcx r9, r14
mov r14, r8
setc r12b
clc
adcx r14, rcx
adcx rdi, r10
mov r14, 0xffffffff 
mov rdx, r8
mulx rcx, r8, r14
adox r8, r15
mov r10, 0x0 
adox rcx, r10
adcx r11, r13
movzx rdx, r12b
lea rdx, [ rdx + rbx ]
adcx r8, r9
adcx rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r15, [ rax + 0x8 ]
mov rdx, -0x3 
inc rdx
adox rbx, rdi
seto r9b
mov rdi, -0x3 
inc rdi
adox r15, r13
setc dil
clc
mov r13, -0x1 
movzx r9, r9b
adcx r9, r13
adcx r11, r15
adox rbp, r12
adcx rbp, r8
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x8 ]
adox r8, [ rsp - 0x48 ]
adox r12, r10
mov rdx, 0xffffffffffffffff 
mulx r15, r9, rbx
mov r15, r9
mov r13, -0x3 
inc r13
adox r15, rbx
adcx r8, rcx
movzx r15, dil
adcx r15, r12
mulx rcx, rdi, r9
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r12, rbx, r9
setc r13b
clc
adcx rdi, r12
adox rbx, r11
adox rdi, rbp
mov rdx, r14
mulx r11, r14, r9
adcx r14, rcx
mov rdx, [ rsi + 0x18 ]
mulx r9, rbp, [ rax + 0x0 ]
adox r14, r8
adcx r11, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r10, r12, [ rsi + 0x10 ]
adox r11, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
clc
adcx r8, r9
adcx r15, rcx
movzx rdx, r13b
mov r9, 0x0 
adox rdx, r9
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rax + 0x18 ]
adcx rcx, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r12, rbx
mov rbx, 0x0 
adcx r9, rbx
clc
adcx rbp, r10
mov rdx, [ rax + 0x18 ]
mulx rbx, r10, [ rsi + 0x10 ]
adox rbp, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
adcx rdi, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], r15
mulx r15, rcx, r12
mov [ rsp - 0x20 ], r8
mulx r8, r15, rcx
adcx r10, r9
adox rdi, r14
adox r10, r11
mov r14, 0x0 
adcx rbx, r14
adox rbx, r13
mov r11, rcx
clc
adcx r11, r12
mov r11, 0xffffffff00000000 
mov rdx, r11
mulx r13, r11, rcx
adcx r11, rbp
mov r12, 0xffffffff 
mov rdx, rcx
mulx rbp, rcx, r12
seto r9b
mov rdx, -0x3 
inc rdx
adox r15, r13
adox rcx, r8
adox rbp, r14
adcx r15, rdi
adcx rcx, r10
mov r8, -0x3 
inc r8
adox r11, [ rsp - 0x40 ]
adox r15, [ rsp - 0x20 ]
adcx rbp, rbx
movzx r8, r9b
adcx r8, r14
adox rcx, [ rsp - 0x28 ]
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r10, rdi, r11
mulx r9, r10, rdi
adox rbp, [ rsp - 0x38 ]
mov rbx, 0xffffffff00000000 
mov rdx, rbx
mulx r13, rbx, rdi
clc
adcx r10, r13
mov rdx, rdi
mulx r13, rdi, r12
adcx rdi, r9
adcx r13, r14
clc
adcx rdx, r11
adcx rbx, r15
adcx r10, rcx
adox r8, [ rsp - 0x30 ]
adcx rdi, rbp
adcx r13, r8
seto dl
adc dl, 0x0
movzx rdx, dl
mov r11, rbx
sub r11, 0x00000001
mov r15, r10
mov rcx, 0xffffffff00000000 
sbb r15, rcx
mov r9, rdi
mov rbp, 0xffffffffffffffff 
sbb r9, rbp
mov r8, r13
sbb r8, r12
movzx r12, dl
sbb r12, 0x00000000
cmovc r9, rdi
cmovc r8, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], r8
mov [ r12 + 0x10 ], r9
cmovc r15, r10
cmovc r11, rbx
mov [ r12 + 0x8 ], r15
mov [ r12 + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5212
; seed 0232927289140756 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1867152 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=208, initial num_batches=31): 145218 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07777513560759916
; number reverted permutation / tried permutation: 65461 / 90200 =72.573%
; number reverted decision / tried decision: 56680 / 89799 =63.119%
; validated in 4.86s
