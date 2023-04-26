SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rax + 0x0 ]
adcx r10, r13
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
adcx r13, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r11, [ rax + 0x18 ]
adcx r11, r14
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, rcx
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r14
mov rdx, 0x0 
adcx r15, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r15
mulx r15, r9, r14
mov r14, r9
clc
adcx r14, rbp
mov rbp, r9
adcx rbp, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r13
mulx r13, r11, [ rsi + 0x10 ]
adox r11, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r11
mulx r11, r12, [ rax + 0x18 ]
adox r12, r13
mov rdx, 0x0 
adox r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], r11
mulx r11, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r12
mulx r12, r13, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r13, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r13
mulx r13, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r10
mov [ rsp + 0x10 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
adox r11, r12
adox r10, r13
mov rdx, 0x0 
adox rbx, rdx
adcx r9, r15
mov rdx, [ rax + 0x8 ]
mulx r13, r12, [ rsi + 0x0 ]
adc r15, 0x0
add r12, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, r8, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rdi, rcx
adcx r8, r13
adox r14, r12
adox rbp, r8
seto dil
inc rdx
adox r14, [ rsp + 0x10 ]
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r13, rcx, r14
mov rdx, [ rax + 0x18 ]
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x20 ], r10
mulx r10, r8, rcx
adcx r13, rbx
mov rbx, 0x0 
adcx r12, rbx
clc
mov rbx, -0x1 
movzx rdi, dil
adcx rdi, rbx
adcx r13, r9
adox rbp, [ rsp + 0x8 ]
adox r13, [ rsp - 0x28 ]
adcx r15, r12
adox r15, [ rsp - 0x30 ]
seto r9b
movzx r9, r9b
adcx r9, [ rsp - 0x38 ]
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mulx r12, rdi, rcx
mov rcx, rdi
inc rbx
adox rcx, r10
setc r10b
clc
adcx r8, r14
adcx rcx, rbp
mov r8, rdi
adox r8, r12
adox rdi, r12
adcx r8, r13
adox r12, rbx
adcx rdi, r15
adcx r12, r9
movzx r14, r10b
adc r14, 0x0
add rcx, [ rsp - 0x40 ]
mov rbp, 0xd838091dd2253531 
mov rdx, rbp
mulx r13, rbp, rcx
mov r13, 0xfffffffefffffc2f 
mov rdx, r13
mulx r15, r13, rbp
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r10, r9, rbp
adcx r8, [ rsp - 0x48 ]
adcx rdi, [ rsp - 0x20 ]
adcx r12, [ rsp - 0x8 ]
adcx r14, [ rsp - 0x18 ]
mov rbp, r9
mov rdx, -0x3 
inc rdx
adox rbp, r15
mov r15, r9
adox r15, r10
setc dl
clc
adcx r13, rcx
adcx rbp, r8
adcx r15, rdi
adox r9, r10
adox r10, rbx
adcx r9, r12
adcx r10, r14
movzx r13, dl
adc r13, 0x0
add rbp, [ rsp - 0x10 ]
adcx r15, [ rsp + 0x0 ]
adcx r11, r9
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r8, rcx, rbp
mov r8, 0xfffffffefffffc2f 
mov rdx, rcx
mulx rdi, rcx, r8
mov r12, 0xffffffffffffffff 
mulx r9, r14, r12
mov rdx, r14
mov r8, -0x3 
inc r8
adox rdx, rdi
mov rdi, r14
adox rdi, r9
adox r14, r9
adox r9, rbx
mov r8, -0x3 
inc r8
adox rcx, rbp
adox rdx, r15
adox rdi, r11
adcx r10, [ rsp + 0x20 ]
adcx r13, [ rsp + 0x18 ]
adox r14, r10
adox r9, r13
seto cl
adc cl, 0x0
movzx rcx, cl
mov rbp, rdx
mov r15, 0xfffffffefffffc2f 
sub rbp, r15
mov r11, rdi
sbb r11, r12
mov r10, r14
sbb r10, r12
mov r13, r9
sbb r13, r12
movzx r8, cl
sbb r8, 0x00000000
cmovc r10, r14
cmovc rbp, rdx
cmovc r13, r9
cmovc r11, rdi
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], r11
mov [ r8 + 0x10 ], r10
mov [ r8 + 0x0 ], rbp
mov [ r8 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8400
; seed 0808055205597316 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 957178 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=195, initial num_batches=31): 74081 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07739521802632321
; number reverted permutation / tried permutation: 76333 / 90430 =84.411%
; number reverted decision / tried decision: 64258 / 89569 =71.741%
; validated in 1.884s
