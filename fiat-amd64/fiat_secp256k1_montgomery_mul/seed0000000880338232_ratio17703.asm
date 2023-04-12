SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, rbx
mov rbx, 0xd838091dd2253531 
mov rdx, rbx
mov [ rsp - 0x68 ], r13
mulx r13, rbx, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbx
adcx r15, r9
mov rdx, [ rax + 0x10 ]
mulx r9, r15, [ rsi + 0x0 ]
adox r15, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r14
mulx r14, r12, rbx
mov rbx, r12
setc dl
clc
adcx rbx, rdi
mov rdi, r12
adcx rdi, r14
adcx r12, r14
mov [ rsp - 0x40 ], r13
mov r13b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
adox r8, r9
mov rdx, 0x0 
adox rcx, rdx
adc r14, 0x0
add r13b, 0xFF
adcx rbp, rbx
adcx rdi, r15
adcx r12, r8
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r8, [ rax + 0x10 ]
adox r13, r11
adox r8, r9
adox r15, rbx
seto dl
mov r11, -0x2 
inc r11
adox r10, rbp
adox r13, rdi
adcx r14, rcx
mov rcx, 0xd838091dd2253531 
xchg rdx, r10
mulx rdi, rbp, rcx
adox r8, r12
mov rdi, 0xfffffffefffffc2f 
xchg rdx, rbp
mulx r9, r12, rdi
adox r15, r14
mov rbx, 0xffffffffffffffff 
mulx r11, r14, rbx
movzx rdx, r10b
mov rbx, [ rsp - 0x28 ]
lea rdx, [ rdx + rbx ]
mov rbx, r14
setc r10b
clc
adcx rbx, r9
mov r9, r14
adcx r9, r11
adcx r14, r11
mov rcx, 0x0 
adcx r11, rcx
movzx rcx, r10b
adox rcx, rdx
clc
adcx r12, rbp
adcx rbx, r13
adcx r9, r8
adcx r14, r15
adcx r11, rcx
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x10 ]
seto dl
mov r13, -0x2 
inc r13
adox r12, rbx
mov r10, 0xd838091dd2253531 
xchg rdx, r10
mulx r15, r8, r12
mov rdx, [ rax + 0x8 ]
mulx rcx, r15, [ rsi + 0x10 ]
mov rdx, r8
mulx rbx, r8, rdi
movzx r13, r10b
mov rdi, 0x0 
adcx r13, rdi
clc
adcx r15, rbp
adox r15, r9
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, [ rax + 0x18 ]
adcx rcx, [ rsp - 0x30 ]
adox rcx, r14
adcx r9, [ rsp - 0x38 ]
adox r9, r11
adcx rbp, rdi
adox rbp, r13
mov rdx, 0xffffffffffffffff 
mulx r11, r14, r10
mov r10, r14
clc
adcx r10, rbx
mov rbx, r14
adcx rbx, r11
seto r13b
mov rdx, -0x3 
inc rdx
adox r8, r12
adox r10, r15
adcx r14, r11
adcx r11, rdi
adox rbx, rcx
mov rdx, [ rax + 0x0 ]
mulx r12, r8, [ rsi + 0x18 ]
clc
adcx r12, [ rsp - 0x40 ]
mov rdx, [ rax + 0x10 ]
mulx rcx, r15, [ rsi + 0x18 ]
adox r14, r9
adcx r15, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx rdi, r9, [ rax + 0x18 ]
adcx r9, rcx
adox r11, rbp
movzx rdx, r13b
mov rbp, 0x0 
adox rdx, rbp
mov r13, -0x3 
inc r13
adox r8, r10
adox r12, rbx
mov r10, 0xd838091dd2253531 
xchg rdx, r8
mulx rcx, rbx, r10
adcx rdi, rbp
mov rcx, 0xfffffffefffffc2f 
xchg rdx, rcx
mulx r13, rbp, rbx
clc
adcx rbp, rcx
adox r15, r14
adox r9, r11
adox rdi, r8
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r14, rbp, rbx
mov r11, rbp
seto r8b
mov rcx, -0x2 
inc rcx
adox r11, r13
mov rbx, rbp
adox rbx, r14
adcx r11, r12
adox rbp, r14
mov r12, 0x0 
adox r14, r12
adcx rbx, r15
adcx rbp, r9
adcx r14, rdi
movzx r13, r8b
adc r13, 0x0
mov r15, r11
mov r9, 0xfffffffefffffc2f 
sub r15, r9
mov r8, rbx
sbb r8, rdx
mov rdi, rbp
sbb rdi, rdx
mov r12, r14
sbb r12, rdx
sbb r13, 0x00000000
cmovc r15, r11
cmovc r12, r14
cmovc rdi, rbp
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rdi
mov [ r13 + 0x0 ], r15
cmovc r8, rbx
mov [ r13 + 0x8 ], r8
mov [ r13 + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.7703
; seed 1308685251301711 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1887300 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=75, initial num_batches=31): 116008 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.061467705187304614
; number reverted permutation / tried permutation: 59673 / 89663 =66.553%
; number reverted decision / tried decision: 38135 / 90336 =42.215%
; validated in 3.662s
