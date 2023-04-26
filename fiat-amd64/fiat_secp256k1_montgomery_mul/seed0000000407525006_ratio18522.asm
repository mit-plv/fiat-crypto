SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rax + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rcx
mov rcx, rdi
add rcx, rbp
mov rbp, rdi
adcx rbp, r13
mov rdx, -0x2 
inc rdx
adox r14, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r12
mulx r12, r11, [ rax + 0x10 ]
adox r11, r15
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rbp
mulx rbp, r15, [ rsi + 0x10 ]
adcx rdi, r13
mov rdx, 0x0 
adcx r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r13
mulx r13, r15, [ rsi + 0x10 ]
clc
adcx r15, rbp
adcx r8, r13
mov rdx, [ rax + 0x18 ]
mulx r13, rbp, [ rsi + 0x10 ]
adcx rbp, r9
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], r15
mulx r15, r8, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r8
mov [ rsp + 0x0 ], r13
mulx r13, r8, [ rsi + 0x18 ]
adox r9, r12
clc
adcx r8, r15
mov rdx, 0x0 
adox rbp, rdx
mov r12, -0x3 
inc r12
adox rbx, r10
adox rcx, r14
adox r11, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mulx r10, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r14, [ rsi + 0x18 ]
adcx r14, r13
mov rdx, [ rsi + 0x18 ]
mulx r12, r13, [ rax + 0x18 ]
adcx r13, r15
adox rdi, r9
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r13
mulx r13, r12, [ rsi + 0x8 ]
clc
adcx r9, r13
adcx r15, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r12, rcx
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r13, rcx, r12
mov r13, 0xfffffffefffffc2f 
mov rdx, rcx
mov [ rsp + 0x18 ], r14
mulx r14, rcx, r13
adcx r9, r11
mov r11, 0xffffffffffffffff 
mov [ rsp + 0x20 ], r8
mulx r8, r13, r11
adox rbp, [ rsp - 0x28 ]
adcx r15, rdi
adcx rbx, rbp
mov rdi, r13
seto dl
mov rbp, -0x2 
inc rbp
adox rdi, r14
mov r14, r13
adox r14, r8
movzx rbp, dl
adcx rbp, r10
setc r10b
clc
adcx rcx, r12
adcx rdi, r9
adox r13, r8
mov rcx, 0x0 
adox r8, rcx
mov r12, -0x3 
inc r12
adox rdi, [ rsp - 0x30 ]
adcx r14, r15
adcx r13, rbx
adcx r8, rbp
movzx r9, r10b
adcx r9, rcx
adox r14, [ rsp - 0x10 ]
adox r13, [ rsp - 0x18 ]
mov rdx, 0xd838091dd2253531 
mulx rbx, r15, rdi
mov rbx, 0xfffffffefffffc2f 
mov rdx, r15
mulx r10, r15, rbx
adox r8, [ rsp - 0x20 ]
adox r9, [ rsp + 0x0 ]
clc
adcx r15, rdi
mulx rbp, r15, r11
mov rdi, r15
seto dl
mov r12, -0x3 
inc r12
adox rdi, r10
mov r10, r15
adox r10, rbp
adcx rdi, r14
adcx r10, r13
adox r15, rbp
adox rbp, rcx
adcx r15, r8
adcx rbp, r9
mov r14, -0x3 
inc r14
adox rdi, [ rsp - 0x8 ]
movzx r14, dl
adcx r14, rcx
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx r8, r13, rdi
adox r10, [ rsp + 0x20 ]
adox r15, [ rsp + 0x18 ]
mov rdx, rbx
mulx rbx, r8, r13
adox rbp, [ rsp + 0x10 ]
mov rdx, r11
mulx r9, r11, r13
mov r13, r11
clc
adcx r13, rbx
mov rbx, r11
adcx rbx, r9
adcx r11, r9
adcx r9, rcx
clc
adcx r8, rdi
adcx r13, r10
adox r14, [ rsp + 0x8 ]
adcx rbx, r15
adcx r11, rbp
adcx r9, r14
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rdi, r13
mov r10, 0xfffffffefffffc2f 
sub rdi, r10
mov r15, rbx
sbb r15, rdx
mov rbp, r11
sbb rbp, rdx
mov r14, r9
sbb r14, rdx
movzx r12, r8b
sbb r12, 0x00000000
cmovc r15, rbx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r15
cmovc rdi, r13
cmovc r14, r9
mov [ r12 + 0x18 ], r14
cmovc rbp, r11
mov [ r12 + 0x10 ], rbp
mov [ r12 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.8522
; seed 2863148597540012 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1002436 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=161, initial num_batches=31): 75674 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07549010610153666
; number reverted permutation / tried permutation: 77279 / 90007 =85.859%
; number reverted decision / tried decision: 63831 / 89992 =70.930%
; validated in 2.134s
