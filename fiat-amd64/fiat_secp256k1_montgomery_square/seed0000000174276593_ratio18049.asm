SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, 0xd838091dd2253531 
mulx r9, r8, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r8
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
xor r8, r8
adox rbp, rax
mov rbp, r13
adcx rbp, r12
mov rax, r13
adcx rax, r14
adcx r13, r14
mov rdx, [ rsi + 0x18 ]
mulx r8, r12, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
clc
adcx r9, r10
adcx r15, rbx
adcx r12, rdi
mov rdx, [ rsi + 0x8 ]
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r8, rdx
clc
adcx r11, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, [ rsi + 0x10 ]
adcx rdi, rcx
adox rbp, r9
adox rax, r15
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, [ rsi + 0x18 ]
adcx rcx, rbx
adox r13, r12
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r10, rbp
mov r15, 0xd838091dd2253531 
mov rdx, r10
mulx r12, r10, r15
adox r14, r8
mov r12, 0xffffffffffffffff 
xchg rdx, r10
mulx rbx, r8, r12
adcx r11, rax
adcx rdi, r13
adcx rcx, r14
setc bpl
movzx rbp, bpl
adox rbp, r9
mov rax, 0xfffffffefffffc2f 
mulx r9, r13, rax
mov rdx, r8
clc
adcx rdx, r9
setc r14b
clc
adcx r13, r10
adcx rdx, r11
mov r13, rbx
seto r10b
mov r11, 0x0 
dec r11
movzx r14, r14b
adox r14, r11
adox r13, r8
adcx r13, rdi
adox r8, rbx
adcx r8, rcx
mov rdi, 0x0 
adox rbx, rdi
adcx rbx, rbp
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, [ rsi + 0x0 ]
mov rdx, -0x3 
inc rdx
adox rbp, rcx
movzx r14, r10b
adcx r14, rdi
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, rax, [ rsi + 0x10 ]
clc
adcx rdi, r9
mov rdx, r15
mulx r9, r15, rbp
adcx r10, r11
adox rdi, r13
mov r9, 0xfffffffefffffc2f 
mov rdx, r15
mulx r13, r15, r9
adcx rax, rcx
mov rcx, 0x0 
adcx r12, rcx
adox r10, r8
mov r8, 0xffffffffffffffff 
mulx rcx, r11, r8
mov rdx, r11
clc
adcx rdx, r13
adox rax, rbx
adox r12, r14
mov rbx, r11
adcx rbx, rcx
seto r14b
mov r13, -0x2 
inc r13
adox r15, rbp
adox rdx, rdi
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rsi + 0x18 ]
adcx r11, rcx
adox rbx, r10
adox r11, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r10, [ rsi + 0x18 ]
setc dl
clc
adcx rbp, r15
setc r15b
clc
adcx r13, rdi
adcx r10, r9
mov rdi, 0xd838091dd2253531 
xchg rdx, rdi
mulx r8, r9, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r10
mulx r10, r8, rdx
adcx r8, rax
mov rdx, 0x0 
adcx r10, rdx
movzx rax, dil
lea rax, [ rax + rcx ]
adox rax, r12
clc
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rbx, r13
movzx r12, r14b
adox r12, rdx
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx rdi, r9, r14
mov r15, 0xfffffffefffffc2f 
mulx rcx, r13, r15
mov rdx, r9
mov r15, -0x2 
inc r15
adox rdx, rcx
adcx r11, [ rsp - 0x48 ]
adcx r8, rax
adcx r10, r12
mov rax, r9
adox rax, rdi
setc r12b
clc
adcx r13, rbp
adcx rdx, rbx
adcx rax, r11
adox r9, rdi
mov r13, 0x0 
adox rdi, r13
adcx r9, r8
adcx rdi, r10
movzx rbp, r12b
adc rbp, 0x0
mov rbx, rdx
mov rcx, 0xfffffffefffffc2f 
sub rbx, rcx
mov r11, rax
sbb r11, r14
mov r8, r9
sbb r8, r14
mov r12, rdi
sbb r12, r14
sbb rbp, 0x00000000
cmovc r8, r9
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], r8
cmovc r11, rax
cmovc r12, rdi
mov [ rbp + 0x8 ], r11
mov [ rbp + 0x18 ], r12
cmovc rbx, rdx
mov [ rbp + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.8049
; seed 3496813804702011 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1192269 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=124, initial num_batches=31): 81894 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06868751934336965
; number reverted permutation / tried permutation: 71122 / 90273 =78.785%
; number reverted decision / tried decision: 46725 / 89726 =52.075%
; validated in 2.623s
