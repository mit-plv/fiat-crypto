SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
add rax, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x8 ]
adcx rcx, r10
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
adcx rbp, rbx
adc r12, 0x0
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x68 ], r13
mulx r13, rbx, r10
mov [ rsp - 0x60 ], r14
mov r14, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp - 0x58 ], r15
mulx r15, r10, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
add r14, r9
mov rdx, r10
mov r9, -0x2 
inc r9
adox rdx, r13
mov r13, r10
adox r13, r15
adox r10, r15
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], rax
mulx rax, rcx, [ rsi + 0x0 ]
adcx r12, rdi
mov rdx, 0x0 
adox r15, rdx
adcx rcx, rbp
adc rax, 0x0
add rbx, r8
adcx r9, r14
mov rbx, -0x3 
inc rbx
adox r11, r9
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx rdi, r8, r11
mov rdi, 0xfffffffefffffc2f 
mov rdx, r8
mulx r14, r8, rdi
adcx r13, r12
adcx r10, rcx
adcx r15, rax
adox r13, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
mov rbp, 0xffffffffffffffff 
mulx rcx, r12, rbp
mov rax, r12
setc r9b
clc
adcx rax, r14
adox r15, [ rsp - 0x40 ]
mov rdx, r12
adcx rdx, rcx
movzx r9, r9b
movzx r14, r9b
adox r14, [ rsp - 0x48 ]
seto r9b
inc rbx
adox r8, r11
adox rax, r13
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, [ rsi + 0x10 ]
adox r8, r10
adcx r12, rcx
adox r12, r15
mov rdx, [ rsi + 0x0 ]
mulx r15, r10, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rcx, rdx
adox rcx, r14
movzx r14, r9b
adox r14, rdx
add rbx, r15
adcx r11, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, [ rsi + 0x18 ]
adcx r9, r13
adc rbp, 0x0
add r10, rax
mov rdx, 0xd838091dd2253531 
mulx r13, rax, r10
adcx rbx, r8
adcx r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rsi + 0x0 ]
mov rdx, rdi
mulx r12, rdi, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r13
mulx r13, r15, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r15, r8
adcx r9, rcx
adcx rbp, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r15
mulx r15, r9, rax
mov rax, r9
setc dl
clc
adcx rax, r12
mov r12, r9
adcx r12, r15
adcx r9, r15
adox rcx, r13
adox r8, r14
mov r13, 0x0 
adox rbp, r13
adc r15, 0x0
xor r14, r14
adox rdi, r10
adox rax, rbx
adox r12, r11
adcx rax, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x10 ]
adox r9, [ rsp - 0x18 ]
adox r15, [ rsp - 0x20 ]
adcx rcx, r9
adcx r8, r15
movzx rdi, dl
adox rdi, r14
adcx rbp, rdi
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx r10, r13, rax
mov r10, 0xfffffffefffffc2f 
mov rdx, r10
mulx rbx, r10, r13
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r9, r11, r13
mov r15, r11
mov rdi, -0x3 
inc rdi
adox r15, rbx
mov r13, r11
adox r13, r9
adox r11, r9
setc bl
clc
adcx r10, rax
adcx r15, r12
adox r9, r14
adcx r13, rcx
adcx r11, r8
adcx r9, rbp
movzx r10, bl
adc r10, 0x0
mov rax, r15
mov r12, 0xfffffffefffffc2f 
sub rax, r12
mov rcx, r13
sbb rcx, rdx
mov r8, r11
sbb r8, rdx
mov rbx, r9
sbb rbx, rdx
sbb r10, 0x00000000
cmovc rcx, r13
cmovc rax, r15
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], rcx
cmovc rbx, r9
mov [ r10 + 0x18 ], rbx
cmovc r8, r11
mov [ r10 + 0x10 ], r8
mov [ r10 + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 2.1487
; seed 3768542997591284 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 903204 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=181, initial num_batches=31): 74950 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08298236057413386
; number reverted permutation / tried permutation: 75412 / 89855 =83.926%
; number reverted decision / tried decision: 64356 / 90144 =71.392%
; validated in 1.74s
