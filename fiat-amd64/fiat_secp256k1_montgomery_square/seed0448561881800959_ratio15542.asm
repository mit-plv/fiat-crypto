SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 176
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rbp
mulx rbp, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r12
mulx r12, r13, [ rsi + 0x10 ]
test al, al
adox r13, rbp
adox r14, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r13
mulx r13, r14, rbp
adox rdi, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
adcx r13, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r13
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r8, rdx
adcx rbx, r15
adcx r11, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], rbx
mulx rbx, r11, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r8
mulx r8, rdi, r14
adc rcx, 0x0
xor r14, r14
adox r11, rbp
adcx r15, r9
mov r11, rdi
setc r9b
clc
adcx r11, rbx
mov rbp, rdi
adcx rbp, r8
setc bl
clc
adcx rax, r12
adox r11, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r12, [ rsi + 0x0 ]
adcx r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r14, r10, [ rsi + 0x10 ]
seto dl
mov [ rsp + 0x28 ], rcx
mov rcx, 0x0 
dec rcx
movzx r9, r9b
adox r9, rcx
adox r13, r10
adox r14, [ rsp - 0x8 ]
adcx rax, [ rsp - 0x28 ]
mov r9, [ rsp - 0x38 ]
mov r10, 0x0 
adox r9, r10
dec r10
movzx rdx, dl
adox rdx, r10
adox r12, rbp
mov rcx, r8
setc bpl
clc
movzx rbx, bl
adcx rbx, r10
adcx rcx, rdi
adox rcx, rax
movzx rdi, bpl
mov rbx, [ rsp - 0x40 ]
lea rdi, [ rdi + rbx ]
mov rbx, 0x0 
adcx r8, rbx
adox r8, rdi
clc
adcx r11, [ rsp - 0x48 ]
adcx r15, r12
adcx r13, rcx
mov rdx, 0xd838091dd2253531 
mulx rax, rbp, r11
mov rax, 0xfffffffefffffc2f 
mov rdx, rax
mulx r12, rax, rbp
adcx r14, r8
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rdi, rcx, rbp
setc r8b
movzx r8, r8b
adox r8, r9
mov r9, rcx
clc
adcx r9, r12
mov rbp, rcx
adcx rbp, rdi
adcx rcx, rdi
adcx rdi, rbx
clc
adcx rax, r11
adcx r9, r15
adcx rbp, r13
seto al
mov r11, -0x3 
inc r11
adox r9, [ rsp - 0x30 ]
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx r13, r15, r9
adox rbp, [ rsp - 0x18 ]
adcx rcx, r14
adox rcx, [ rsp - 0x20 ]
adcx rdi, r8
movzx r13, al
adcx r13, rbx
adox rdi, [ rsp - 0x10 ]
adox r13, [ rsp + 0x20 ]
mov r12, 0xfffffffefffffc2f 
mov rdx, r15
mulx r14, r15, r12
mov r8, 0xffffffffffffffff 
mulx rbx, rax, r8
mov rdx, rax
clc
adcx rdx, r14
mov r14, rax
adcx r14, rbx
adcx rax, rbx
seto r11b
inc r10
adox r15, r9
adox rdx, rbp
adox r14, rcx
adcx rbx, r10
clc
adcx rdx, [ rsp + 0x18 ]
mov r15, 0xd838091dd2253531 
mulx rbp, r9, r15
xchg rdx, r9
mulx rcx, rbp, r12
adox rax, rdi
adcx r14, [ rsp + 0x0 ]
adox rbx, r13
adcx rax, [ rsp + 0x10 ]
seto dil
mov r13, -0x3 
inc r13
adox rbp, r9
mulx r9, rbp, r8
mov rdx, rbp
setc r13b
clc
adcx rdx, rcx
mov rcx, rbp
adcx rcx, r9
adcx rbp, r9
adcx r9, r10
movzx r10, dil
movzx r11, r11b
lea r10, [ r10 + r11 ]
clc
mov r11, -0x1 
movzx r13, r13b
adcx r13, r11
adcx rbx, [ rsp + 0x8 ]
adcx r10, [ rsp + 0x28 ]
adox rdx, r14
adox rcx, rax
adox rbp, rbx
adox r9, r10
seto r14b
adc r14b, 0x0
movzx r14, r14b
mov rdi, rdx
sub rdi, r12
mov r13, rcx
sbb r13, r8
mov rax, rbp
sbb rax, r8
mov rbx, r9
sbb rbx, r8
movzx r10, r14b
sbb r10, 0x00000000
cmovc rbx, r9
cmovc rdi, rdx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rbx
mov [ r10 + 0x0 ], rdi
cmovc rax, rbp
mov [ r10 + 0x10 ], rax
cmovc r13, rcx
mov [ r10 + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5542
; seed 0448561881800959 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 13026 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=90, initial num_batches=31): 784 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06018731767234761
; number reverted permutation / tried permutation: 332 / 498 =66.667%
; number reverted decision / tried decision: 332 / 501 =66.267%
; validated in 4.119s
