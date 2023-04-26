SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rax + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x40 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
add r12, r11
adcx r14, r13
mov rdx, [ rax + 0x18 ]
mulx r13, r11, [ rsi + 0x0 ]
adcx r11, r15
adc r13, 0x0
add rbx, r10
mov rdx, rdi
mov rbx, -0x2 
inc rbx
adox rdx, rbp
mov r10, rdi
adox r10, r9
adcx rdx, r12
adox rdi, r9
adcx r10, r14
adcx rdi, r11
mov rbp, 0x0 
adox r9, rbp
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mulx r14, r12, [ rsi + 0x8 ]
mov rdx, -0x3 
inc rdx
adox r12, r15
adcx r9, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r9
mulx r9, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], rdi
mulx rdi, rbx, [ rax + 0x8 ]
setc dl
clc
adcx rbx, r14
adcx r15, rdi
adox rbx, r10
seto r10b
mov r14, -0x2 
inc r14
adox r11, r9
adcx rcx, rbp
adox r13, [ rsp - 0x40 ]
mov rbp, 0x0 
adcx r8, rbp
mov r9b, dl
mov rdx, [ rsi + 0x10 ]
mulx rbp, rdi, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rax + 0x18 ]
adox r14, [ rsp - 0x48 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r11
mulx r11, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r13, rdx
add rdi, [ rsp - 0x30 ]
adcx r14, rbp
mov rbp, 0xd838091dd2253531 
mov rdx, rbp
mov [ rsp + 0x8 ], r13
mulx r13, rbp, r12
mov r13, 0xfffffffefffffc2f 
mov rdx, rbp
mov [ rsp + 0x10 ], r14
mulx r14, rbp, r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], rbx
mulx rbx, rdi, [ rax + 0x18 ]
adcx rdi, r11
adc rbx, 0x0
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x28 ], rbx
mulx rbx, r11, r13
add r10b, 0x7F
adox r15, [ rsp - 0x18 ]
adox rcx, [ rsp - 0x28 ]
mov r10, r11
adcx r10, r14
mov r13, r11
adcx r13, rbx
adcx r11, rbx
movzx r14, r9b
adox r14, r8
seto r9b
mov r8, -0x2 
inc r8
adox rbp, r12
adox r10, [ rsp + 0x20 ]
mov rbp, 0x0 
adcx rbx, rbp
clc
adcx r10, [ rsp - 0x38 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rbp, r12, r10
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mulx r8, rbp, r12
adox r13, r15
adcx r13, [ rsp + 0x18 ]
adox r11, rcx
adox rbx, r14
adcx r11, [ rsp + 0x10 ]
adcx rdi, rbx
movzx r15, r9b
mov rcx, 0x0 
adox r15, rcx
adcx r15, [ rsp + 0x28 ]
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r14, r9, r12
mov r12, -0x3 
inc r12
adox rbp, r10
mov rbp, r9
setc r10b
clc
adcx rbp, r8
mov r8, r9
adcx r8, r14
adcx r9, r14
adox rbp, r13
adox r8, r11
adcx r14, rcx
clc
adcx rbp, [ rsp - 0x20 ]
adox r9, rdi
adox r14, r15
adcx r8, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x10 ]
adcx r14, [ rsp - 0x8 ]
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx rbx, r13, rbp
movzx rbx, r10b
adox rbx, rcx
mov r11, 0xfffffffefffffc2f 
mov rdx, r13
mulx rdi, r13, r11
adcx rbx, [ rsp + 0x8 ]
mov r10, -0x3 
inc r10
adox r13, rbp
mov r10, 0xffffffffffffffff 
mulx r15, r13, r10
mov rbp, r13
setc dl
clc
adcx rbp, rdi
adox rbp, r8
mov r8, r13
adcx r8, r15
adox r8, r9
adcx r13, r15
adcx r15, rcx
adox r13, r14
adox r15, rbx
movzx r9, dl
adox r9, rcx
mov r14, rbp
sub r14, r11
mov rdi, r8
sbb rdi, r10
mov rdx, r13
sbb rdx, r10
mov rbx, r15
sbb rbx, r10
sbb r9, 0x00000000
cmovc rdi, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], rdi
cmovc rdx, r13
cmovc r14, rbp
mov [ r9 + 0x10 ], rdx
mov [ r9 + 0x0 ], r14
cmovc rbx, r15
mov [ r9 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.8483
; seed 0795352270601647 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 895872 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=196, initial num_batches=31): 73035 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08152392306043721
; number reverted permutation / tried permutation: 76242 / 89896 =84.811%
; number reverted decision / tried decision: 66252 / 90103 =73.529%
; validated in 1.901s
