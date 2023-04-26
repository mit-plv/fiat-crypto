SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r15
mulx r15, rbp, [ rax + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rbp
mulx rbp, r15, r12
xor rdx, rdx
adox r15, rcx
mov r15, 0xffffffffffffffff 
mov rdx, r12
mulx rcx, r12, r15
mov rdx, r12
adcx rdx, rbp
mov rbp, r12
adcx rbp, rcx
adcx r12, rcx
setc r15b
clc
adcx r14, r8
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
adcx rdi, r13
adcx r10, rbx
mov rdx, 0x0 
adcx r11, rdx
adox r8, r14
clc
adcx r9, r8
mov r13, 0xd838091dd2253531 
mov rdx, r9
mulx r14, r9, r13
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rbx, [ rax + 0x8 ]
adox rbp, rdi
mov rdx, 0xffffffffffffffff 
mulx r13, rdi, r9
movzx rdx, r15b
lea rdx, [ rdx + rcx ]
adox r12, r10
adox rdx, r11
seto cl
mov r15, -0x2 
inc r15
adox rbx, [ rsp - 0x8 ]
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mulx r15, r11, [ rsi + 0x8 ]
adox r11, r8
adcx rbx, rbp
adcx r11, r12
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, [ rax + 0x18 ]
adox r8, r15
adcx r8, r10
mov rdx, 0xfffffffefffffc2f 
mulx r10, r12, r9
mov r9, 0x0 
adox rbp, r9
mov r15, rdi
mov rdx, -0x3 
inc rdx
adox r15, r10
movzx r10, cl
adcx r10, rbp
mov rcx, rdi
adox rcx, r13
setc bpl
clc
adcx r12, r14
adcx r15, rbx
adcx rcx, r11
adox rdi, r13
adcx rdi, r8
adox r13, r9
adcx r13, r10
mov rdx, [ rax + 0x8 ]
mulx r14, r12, [ rsi + 0x10 ]
movzx rdx, bpl
adc rdx, 0x0
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mulx r8, r11, [ rsi + 0x10 ]
test al, al
adox r12, [ rsp - 0x10 ]
adox r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r10, rbp, [ rax + 0x18 ]
adcx r15, [ rsp - 0x28 ]
adcx r12, rcx
mov rdx, 0xd838091dd2253531 
mulx r14, rcx, r15
adox rbp, r8
mov r14, 0xfffffffefffffc2f 
mov rdx, r14
mulx r8, r14, rcx
adcx r11, rdi
adox r10, r9
adcx rbp, r13
adcx r10, rbx
mov rdx, [ rsi + 0x18 ]
mulx r13, rdi, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r9, rbx, rcx
mov rcx, -0x2 
inc rcx
adox r14, r15
mov r14, rbx
setc r15b
clc
adcx r14, r8
mov r8, rbx
adcx r8, r9
adcx rbx, r9
adox r14, r12
adox r8, r11
adox rbx, rbp
mov r12, 0x0 
adcx r9, r12
adox r9, r10
clc
adcx rdi, r14
movzx r11, r15b
adox r11, r12
mov rbp, 0xd838091dd2253531 
mov rdx, rbp
mulx r15, rbp, rdi
mov r15, 0xfffffffefffffc2f 
mov rdx, r15
mulx r10, r15, rbp
mov r14, -0x3 
inc r14
adox r13, [ rsp - 0x30 ]
adcx r13, r8
mov r8, [ rsp - 0x40 ]
adox r8, [ rsp - 0x38 ]
mov r12, [ rsp - 0x48 ]
adox r12, [ rsp - 0x18 ]
mov r14, [ rsp - 0x20 ]
mov rcx, 0x0 
adox r14, rcx
adcx r8, rbx
adcx r12, r9
mov rbx, 0xffffffffffffffff 
mov rdx, rbp
mulx r9, rbp, rbx
adcx r14, r11
mov r11, rbp
mov rdx, -0x3 
inc rdx
adox r11, r10
mov r10, rbp
adox r10, r9
adox rbp, r9
setc dl
clc
adcx r15, rdi
adcx r11, r13
adcx r10, r8
adcx rbp, r12
adox r9, rcx
adcx r9, r14
movzx r15, dl
adc r15, 0x0
mov rdi, r11
mov r13, 0xfffffffefffffc2f 
sub rdi, r13
mov r8, r10
sbb r8, rbx
mov r12, rbp
sbb r12, rbx
mov rdx, r9
sbb rdx, rbx
sbb r15, 0x00000000
cmovc rdi, r11
cmovc r8, r10
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r8
cmovc rdx, r9
mov [ r15 + 0x18 ], rdx
cmovc r12, rbp
mov [ r15 + 0x10 ], r12
mov [ r15 + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.9608
; seed 2480396588749158 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1187682 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=108, initial num_batches=31): 81321 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0684703481234876
; number reverted permutation / tried permutation: 66414 / 89855 =73.912%
; number reverted decision / tried decision: 44971 / 90144 =49.888%
; validated in 2.963s
