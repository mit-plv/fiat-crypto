SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
xor rdx, rdx
adox rdi, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r12
mulx r12, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r10
mulx r10, r12, [ rsi + 0x0 ]
adcx r14, rbp
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
clc
adcx rbx, rax
adox r12, r13
adox rbp, r10
mov rdx, 0x0 
adox rcx, rdx
adcx r14, rdi
mov rdx, [ rsi + 0x8 ]
mulx r13, rbx, [ rsi + 0x0 ]
adcx r15, r12
mov rdx, 0xffffffff00000001 
mulx r10, rdi, rax
mov rax, -0x2 
inc rax
adox rbx, r14
adcx rdi, rbp
mov r12, 0xffffffffffffffff 
mov rdx, rbx
mulx rbp, rbx, r12
mov r14, 0xffffffff00000001 
mulx r12, rax, r14
adcx r10, rcx
setc cl
clc
adcx r8, r13
adcx r11, r9
adox r8, r15
adox r11, rdi
mov r9, 0xffffffff 
mulx r15, r13, r9
mov rdi, [ rsp - 0x28 ]
adcx rdi, [ rsp - 0x40 ]
setc r14b
clc
adcx r13, rbp
movzx rbp, r14b
mov r9, [ rsp - 0x48 ]
lea rbp, [ rbp + r9 ]
mov r9, 0x0 
adcx r15, r9
clc
adcx rbx, rdx
adcx r13, r8
adox rdi, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rbx, [ rsi + 0x18 ]
adcx r15, r11
adcx rax, rdi
mov rdx, [ rsi + 0x18 ]
mulx r11, r8, [ rsi + 0x0 ]
movzx rdx, cl
adox rdx, rbp
adcx r12, rdx
setc cl
clc
adcx rbx, r11
adcx r10, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, [ rsi + 0x8 ]
movzx rdx, cl
adox rdx, r9
adcx r14, [ rsp - 0x38 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r14
mulx r14, r9, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r9, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r10
mulx r10, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r8
mulx r8, rbx, rdx
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx rdi, r14
adcx rbx, r11
adcx r13, r8
adox rdi, r15
adcx r10, rdx
adox rbx, rax
adox r13, r12
mov r15, 0xffffffff 
mov rdx, r15
mulx rax, r15, r9
mov r12, 0xffffffffffffffff 
mov rdx, r9
mulx r11, r9, r12
adox r10, rcx
clc
adcx r9, rdx
seto r9b
mov rcx, -0x2 
inc rcx
adox r15, r11
adcx r15, rdi
mov r14, 0x0 
adox rax, r14
adcx rax, rbx
mov r8, 0xffffffff00000001 
mulx rbx, rdi, r8
adcx rdi, r13
mov rdx, -0x3 
inc rdx
adox r15, [ rsp - 0x8 ]
adcx rbx, r10
adox rax, [ rsp - 0x10 ]
adox rdi, [ rsp - 0x18 ]
mov rdx, r12
mulx r13, r12, r15
movzx r11, r9b
adcx r11, r14
mov r9, 0xffffffff 
mov rdx, r15
mulx r10, r15, r9
adox rbx, [ rsp - 0x20 ]
clc
adcx r15, r13
adox rbp, r11
seto r13b
mov r11, -0x3 
inc r11
adox r12, rdx
adox r15, rax
mulx rax, r12, r8
setc dl
seto r11b
mov rcx, r15
mov r9, 0xffffffffffffffff 
sub rcx, r9
movzx r14, dl
lea r14, [ r14 + r10 ]
mov r10, -0x1 
inc r10
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox rdi, r14
adox r12, rbx
adox rax, rbp
movzx rbx, r13b
adox rbx, r10
mov r13, rdi
mov rbp, 0xffffffff 
sbb r13, rbp
mov r11, r12
sbb r11, 0x00000000
mov r14, rax
sbb r14, r8
sbb rbx, 0x00000000
cmovc r13, rdi
cmovc r11, r12
cmovc rcx, r15
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], rcx
mov [ rbx + 0x10 ], r11
cmovc r14, rax
mov [ rbx + 0x18 ], r14
mov [ rbx + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6471
; seed 2844284970207726 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1101514 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=153, initial num_batches=31): 74114 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06728375672029588
; number reverted permutation / tried permutation: 70328 / 89909 =78.221%
; number reverted decision / tried decision: 59664 / 90090 =66.227%
; validated in 1.676s
