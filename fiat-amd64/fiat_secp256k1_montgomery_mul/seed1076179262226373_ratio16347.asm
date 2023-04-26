SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 208
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rbp
mulx rbp, r13, r10
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mov [ rsp - 0x28 ], r14
mulx r14, rbp, r13
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
add rbp, r11
mov rdx, -0x2 
inc rdx
adox r9, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, [ rax + 0x10 ]
adox rcx, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, rbx, [ rax + 0x18 ]
adox rbx, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
adcx r8, r14
adcx r15, rbx
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rax + 0x8 ]
mulx rbx, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r9
mulx r9, rcx, [ rax + 0x8 ]
adc rdi, 0x0
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r15
mulx r15, rdi, [ rax + 0x0 ]
xor rdx, rdx
adox rcx, r15
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x20 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
adcx r14, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r14
mulx r14, rdi, [ rax + 0x18 ]
adcx r15, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], r15
mulx r15, rbx, r13
mov r13, rbx
setc dl
clc
adcx r13, [ rsp - 0x18 ]
adox r11, r9
adox rdi, r12
mov r12, rbx
adcx r12, r15
adcx rbx, r15
seto r9b
mov [ rsp + 0x40 ], rdi
mov rdi, -0x2 
inc rdi
adox r10, [ rsp - 0x20 ]
mov r10, 0x0 
adcx r15, r10
adox r13, rbp
adox r12, r8
adox rbx, [ rsp + 0x18 ]
adox r15, [ rsp + 0x10 ]
movzx rbp, r9b
lea rbp, [ rbp + r14 ]
clc
movzx rdx, dl
adcx rdx, rdi
adcx rcx, [ rsp - 0x30 ]
mov r8, [ rsp - 0x40 ]
adcx r8, r10
clc
adcx r13, [ rsp - 0x48 ]
adcx r12, [ rsp + 0x30 ]
adcx rbx, [ rsp + 0x38 ]
mov r14, 0xd838091dd2253531 
mov rdx, r14
mulx r9, r14, r13
mov r9, 0xfffffffefffffc2f 
mov rdx, r9
mulx r10, r9, r14
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp + 0x48 ], rbp
mulx rbp, rdi, r14
adcx rcx, r15
mov r15, rdi
setc r14b
clc
adcx r15, r10
movzx r10, r14b
adox r10, r8
mov r8, rdi
adcx r8, rbp
adcx rdi, rbp
seto r14b
mov rdx, -0x2 
inc rdx
adox r9, r13
adox r15, r12
mov r9, 0x0 
adcx rbp, r9
adox r8, rbx
adox rdi, rcx
adox rbp, r10
movzx r13, r14b
adox r13, r9
add r15, [ rsp - 0x38 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rbx, r12, r15
mov rbx, 0xffffffffffffffff 
mov rdx, r12
mulx rcx, r12, rbx
mov r14, 0xfffffffefffffc2f 
mulx r9, r10, r14
mov rdx, -0x2 
inc rdx
adox r10, r15
adcx r8, [ rsp + 0x8 ]
adcx rdi, [ rsp - 0x10 ]
adcx rbp, [ rsp - 0x8 ]
adcx r13, [ rsp + 0x0 ]
mov r10, r12
setc r15b
clc
adcx r10, r9
mov r9, r12
adcx r9, rcx
adcx r12, rcx
adox r10, r8
adox r9, rdi
mov r8, 0x0 
adcx rcx, r8
adox r12, rbp
adox rcx, r13
movzx rdi, r15b
adox rdi, r8
xor rbp, rbp
adox r10, [ rsp + 0x28 ]
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r15, r8, r10
adox r9, [ rsp + 0x20 ]
adox r11, r12
mov rdx, r8
mulx r15, r8, r14
adox rcx, [ rsp + 0x40 ]
adcx r8, r10
mulx r13, r8, rbx
adox rdi, [ rsp + 0x48 ]
mov r12, r8
seto r10b
mov rdx, -0x3 
inc rdx
adox r12, r15
mov r15, r8
adox r15, r13
adox r8, r13
adox r13, rbp
adcx r12, r9
adcx r15, r11
adcx r8, rcx
adcx r13, rdi
setc r9b
mov r11, r12
sub r11, r14
mov rcx, r15
sbb rcx, rbx
movzx rdi, r9b
movzx r10, r10b
lea rdi, [ rdi + r10 ]
mov r10, r8
sbb r10, rbx
mov r9, r13
sbb r9, rbx
sbb rdi, 0x00000000
cmovc rcx, r15
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], rcx
cmovc r11, r12
mov [ rdi + 0x0 ], r11
cmovc r10, r8
cmovc r9, r13
mov [ rdi + 0x18 ], r9
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 208
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.6347
; seed 1076179262226373 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 14007 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=84, initial num_batches=31): 772 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05511529949311059
; number reverted permutation / tried permutation: 347 / 491 =70.672%
; number reverted decision / tried decision: 332 / 508 =65.354%
; validated in 4.523s
