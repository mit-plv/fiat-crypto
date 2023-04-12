SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 168
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r8
mov r14, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp - 0x40 ], rbp
mulx rbp, rdi, r14
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], r13
mulx r13, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r11, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r11
mulx r11, r15, rdx
adox r12, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x10 ], r11
mulx r11, rcx, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], r12
mulx r12, r15, r14
adcx r15, rbp
adcx rcx, r12
mov rbp, 0x0 
adcx r11, rbp
adox rax, r13
adox r10, rbp
xor r13, r13
adox r14, r8
adcx rbx, r9
adox rdi, rbx
mov rbp, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov r14, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
adox r15, rbp
adox rcx, r14
mov r8, [ rsp - 0x40 ]
adcx r8, r13
clc
adcx rdi, [ rsp - 0x48 ]
adcx r15, [ rsp + 0x8 ]
mulx r12, r9, rdi
mov r12, 0xffffffff 
mov rdx, r9
mulx rbx, r9, r12
mov rbp, 0xffffffff00000000 
mulx r13, r14, rbp
adcx rcx, [ rsp + 0x20 ]
adox r11, r8
mov r8, 0xffffffffffffffff 
mulx rbp, r12, r8
adcx rax, r11
setc r11b
clc
adcx r12, r13
movzx r13, r11b
adox r13, r10
adcx r9, rbp
mov r10, 0x0 
adcx rbx, r10
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, [ rsi + 0x8 ]
clc
adcx rbp, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rsi + 0x10 ]
adcx r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, rdx
adcx r12, rcx
adcx r9, rax
seto dl
mov rcx, -0x2 
inc rcx
adox r11, rdi
adox r15, r10
adcx rbx, r13
adox r8, [ rsp - 0x10 ]
movzx rax, dl
mov r13, 0x0 
adcx rax, r13
clc
adcx rbp, r14
mov rdx, 0xffffffffffffffff 
mulx rdi, r10, rbp
adcx r11, r12
adcx r15, r9
adcx r8, rbx
mov rdi, [ rsp - 0x18 ]
adox rdi, r13
mulx r12, r14, r10
adcx rdi, rax
mov r9, r10
mov rbx, -0x3 
inc rbx
adox r9, rbp
mov r9, 0xffffffff00000000 
mov rdx, r9
mulx rax, r9, r10
adox r9, r11
mov rbp, 0xffffffff 
mov rdx, rbp
mulx r11, rbp, r10
setc r10b
clc
adcx r14, rax
adcx rbp, r12
adcx r11, r13
adox r14, r15
mov rdx, [ rsi + 0x18 ]
mulx r12, r15, [ rsi + 0x8 ]
adox rbp, r8
adox r11, rdi
movzx rdx, r10b
adox rdx, r13
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, r9
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx rax, r13, r10
adcx r15, rdi
adcx r12, [ rsp + 0x0 ]
mov rax, [ rsp + 0x18 ]
adcx rax, [ rsp - 0x8 ]
adox r15, r14
mov r9, r13
setc r14b
clc
adcx r9, r10
adox r12, rbp
adox rax, r11
movzx r9, r14b
mov rbp, [ rsp + 0x10 ]
lea r9, [ r9 + rbp ]
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx r11, rbp, r13
adcx rbp, r15
adox r9, r8
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx rdi, r8, r13
seto r10b
inc rcx
adox r8, r11
mov r14, 0xffffffff 
mov rdx, r13
mulx r15, r13, r14
adox r13, rdi
adox r15, rcx
adcx r8, r12
adcx r13, rax
adcx r15, r9
movzx rdx, r10b
adc rdx, 0x0
mov r12, rbp
sub r12, 0x00000001
mov rax, r8
mov r11, 0xffffffff00000000 
sbb rax, r11
mov r10, r13
mov r9, 0xffffffffffffffff 
sbb r10, r9
mov rdi, r15
sbb rdi, r14
sbb rdx, 0x00000000
cmovc r12, rbp
cmovc rax, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r12
cmovc r10, r13
cmovc rdi, r15
mov [ rdx + 0x10 ], r10
mov [ rdx + 0x18 ], rdi
mov [ rdx + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.4772
; seed 3665246789883111 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1219809 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=158, initial num_batches=31): 79757 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06538482664089214
; number reverted permutation / tried permutation: 69349 / 90137 =76.937%
; number reverted decision / tried decision: 61286 / 89862 =68.200%
; validated in 2.807s
