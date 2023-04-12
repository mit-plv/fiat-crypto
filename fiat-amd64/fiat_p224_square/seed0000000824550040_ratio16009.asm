SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
add r11, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mulx r12, r9, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
mov r14, 0xffffffff00000000 
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, r14
mov r14, rdx
mov [ rsp - 0x50 ], rdi
mov rdi, -0x2 
inc rdi
adox r14, r8
adox r13, r11
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rsi + 0x0 ]
adcx r8, rcx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rsi + 0x18 ]
adcx rcx, r11
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rax
mulx rax, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rsi + 0x18 ]
clc
adcx r11, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r11
mulx r11, r10, rdx
adcx r10, rax
adcx r12, r11
mov rdx, 0xffffffffffffffff 
mulx r11, rax, r14
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r10
mulx r10, r12, r14
mov r14, 0x0 
adcx r9, r14
clc
adcx rax, r15
adcx r12, r11
adox rax, r8
adcx r10, r14
adox r12, rcx
mov rdx, [ rsi + 0x8 ]
mulx r8, r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ rsi + 0x8 ]
clc
adcx r15, rbp
adcx rcx, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, rbp, [ rsi + 0x18 ]
adcx rbp, r11
adcx r8, r14
adox r10, rdi
clc
adcx rbx, r13
mov rdx, [ rsi + 0x18 ]
mulx rdi, r13, [ rsi + 0x8 ]
adcx r15, rax
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, [ rsi + 0x0 ]
adcx rcx, r12
adcx rbp, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r12, rdx
setc dl
clc
adcx r13, r11
movzx r11, dl
adox r11, r8
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r14, r8, rbx
mov [ rsp - 0x18 ], r13
mulx r13, r14, r8
adcx rdi, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x40 ]
mov rdx, 0x0 
adcx r10, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r12
mulx r12, r10, r8
mov rdx, r8
clc
adcx rdx, rbx
adcx r10, r15
mov rdx, 0xffffffff 
mulx r15, rbx, r8
seto r8b
mov rdx, -0x2 
inc rdx
adox r14, r12
adox rbx, r13
adcx r14, rcx
adcx rbx, rbp
mov rcx, 0x0 
adox r15, rcx
adcx r15, r11
movzx rbp, r8b
adc rbp, 0x0
add r10, [ rsp - 0x48 ]
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r11, r8, r10
mulx r13, r11, r8
adcx r14, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
mov r12, 0xffffffff00000000 
mov rdx, r8
mulx rcx, r8, r12
adcx r9, rbp
mov rbp, -0x2 
inc rbp
adox r11, rcx
mov rcx, rdx
setc bpl
clc
adcx rcx, r10
adcx r8, r14
adcx r11, rbx
mov rcx, 0xffffffff 
mulx r14, r10, rcx
adox r10, r13
mov rdx, 0x0 
adox r14, rdx
mov r13, -0x3 
inc r13
adox rax, r8
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r8, rbx, rax
adox r11, [ rsp - 0x18 ]
adcx r10, r15
mov rdx, r12
mulx r12, r8, rbx
adcx r14, r9
mov r15, 0xffffffffffffffff 
mov rdx, rbx
mulx r9, rbx, r15
adox rdi, r10
movzx r10, bpl
mov r13, 0x0 
adcx r10, r13
mov rbp, rdx
clc
adcx rbp, rax
adox r14, [ rsp - 0x8 ]
adox r10, [ rsp - 0x10 ]
adcx r8, r11
seto bpl
mov rax, -0x3 
inc rax
adox rbx, r12
mulx r12, r11, rcx
adox r11, r9
adcx rbx, rdi
adcx r11, r14
adox r12, r13
adcx r12, r10
movzx rdx, bpl
adc rdx, 0x0
mov r9, r8
sub r9, 0x00000001
mov rdi, rbx
mov r14, 0xffffffff00000000 
sbb rdi, r14
mov rbp, r11
sbb rbp, r15
mov r10, r12
sbb r10, rcx
sbb rdx, 0x00000000
cmovc r10, r12
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r10
cmovc r9, r8
cmovc rbp, r11
cmovc rdi, rbx
mov [ rdx + 0x8 ], rdi
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6009
; seed 3133919066413167 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 895230 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=244, initial num_batches=31): 75128 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08392033332216302
; number reverted permutation / tried permutation: 75709 / 90130 =84.000%
; number reverted decision / tried decision: 63232 / 89869 =70.360%
; validated in 1.582s
