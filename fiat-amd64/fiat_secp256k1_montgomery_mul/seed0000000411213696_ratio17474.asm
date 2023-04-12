SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 192
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], rbp
mulx rbp, r15, r10
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
add rbp, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rbp
mulx rbp, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r13
mulx r13, r9, [ rax + 0x10 ]
adcx r9, r14
mov rdx, -0x2 
inc rdx
adox rdi, r12
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, [ rax + 0x18 ]
adcx r12, r13
mov rdx, 0x0 
adcx r14, rdx
adox r15, rbp
mov rdx, [ rax + 0x18 ]
mulx r13, rbp, [ rsi + 0x10 ]
adox rbp, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r14
mulx r14, rbx, [ rax + 0x0 ]
mov rdx, 0x0 
adox r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r12
mov [ rsp + 0x8 ], r9
mulx r9, r12, [ rax + 0x10 ]
xor rdx, rdx
adox rcx, r11
adox r12, r8
adox r9, [ rsp - 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, [ rax + 0x8 ]
adcx r11, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rsi + 0x8 ]
adcx r14, r8
adcx r13, [ rsp - 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], rbp
mulx rbp, r8, [ rsp - 0x28 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], rdi
mulx rdi, r15, [ rsp - 0x28 ]
mov rdx, [ rsp - 0x20 ]
mov [ rsp + 0x30 ], r13
mov r13, 0x0 
adcx rdx, r13
mov r13, [ rsp - 0x38 ]
mov [ rsp + 0x38 ], rdx
mov rdx, 0x0 
adox r13, rdx
add r15, r10
mov r15, r8
mov r10, -0x3 
inc r10
adox r15, rdi
adcx r15, rcx
mov rcx, r8
adox rcx, rbp
adox r8, rbp
adcx rcx, r12
adox rbp, rdx
mov r12, -0x3 
inc r12
adox rbx, r15
adcx r8, r9
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx r9, r12, rbx
mov r9, 0xfffffffefffffc2f 
mov rdx, r9
mulx rdi, r9, r12
adox r11, rcx
adox r14, r8
adcx rbp, r13
adox rbp, [ rsp + 0x30 ]
seto r13b
movzx r13, r13b
adcx r13, [ rsp + 0x38 ]
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r12
mov r8, r15
inc r10
adox r8, rdi
mov r12, r15
adox r12, rcx
setc dil
clc
adcx r9, rbx
adox r15, rcx
adcx r8, r11
seto r9b
inc r10
adox r8, [ rsp - 0x40 ]
mov rbx, 0xd838091dd2253531 
mov rdx, rbx
mulx r11, rbx, r8
adcx r12, r14
mov r11, 0xfffffffefffffc2f 
mov rdx, rbx
mulx r14, rbx, r11
adcx r15, rbp
movzx rbp, r9b
lea rbp, [ rbp + rcx ]
adcx rbp, r13
adox r12, [ rsp + 0x28 ]
adox r15, [ rsp + 0x20 ]
movzx r13, dil
adcx r13, r10
mov rdi, 0xffffffffffffffff 
mulx r9, rcx, rdi
clc
adcx rbx, r8
mov rbx, rcx
seto r8b
mov rdx, -0x3 
inc rdx
adox rbx, r14
mov r14, rcx
adox r14, r9
adcx rbx, r12
setc r12b
clc
adcx rbx, [ rsp - 0x48 ]
setc r10b
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx rbp, [ rsp + 0x18 ]
adcx r13, [ rsp + 0x10 ]
setc r8b
clc
movzx r12, r12b
adcx r12, rdx
adcx r15, r14
adox rcx, r9
adcx rcx, rbp
mov r14, 0x0 
adox r9, r14
adcx r9, r13
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rbp, r12, rbx
mov rdx, r11
mulx rbp, r11, r12
movzx r13, r8b
adc r13, 0x0
mov rdx, r12
mulx r8, r12, rdi
add r10b, 0xFF
adcx r15, [ rsp - 0x30 ]
adcx rcx, [ rsp + 0x8 ]
mov r10, r12
adox r10, rbp
adcx r9, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
mov rdx, r12
adox rdx, r8
setc bpl
clc
adcx r11, rbx
adcx r10, r15
adox r12, r8
adcx rdx, rcx
adcx r12, r9
adox r8, r14
adcx r8, r13
movzx r11, bpl
adc r11, 0x0
mov rbx, r10
mov r15, 0xfffffffefffffc2f 
sub rbx, r15
mov rcx, rdx
sbb rcx, rdi
mov r9, r12
sbb r9, rdi
mov rbp, r8
sbb rbp, rdi
sbb r11, 0x00000000
cmovc rbx, r10
cmovc rbp, r8
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], rbp
cmovc r9, r12
cmovc rcx, rdx
mov [ r11 + 0x8 ], rcx
mov [ r11 + 0x0 ], rbx
mov [ r11 + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7474
; seed 2971779418686176 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1061352 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=165, initial num_batches=31): 80062 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07543397477933805
; number reverted permutation / tried permutation: 78484 / 90016 =87.189%
; number reverted decision / tried decision: 68314 / 89983 =75.919%
; validated in 2.135s
