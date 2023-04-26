SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
mov rdi, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, r15
xor rdx, rdx
adox rbp, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rbp
mulx rbp, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
adcx r9, r14
adcx r8, rbx
mov rdx, [ rsi + 0x0 ]
mulx r14, rbx, [ rax + 0x18 ]
adcx rbx, rcx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], rbx
mulx rbx, rcx, r15
mov r15, 0x0 
adcx r14, r15
mov rdx, rdi
clc
adcx rdx, rbx
mov rbx, rdi
adcx rbx, r10
mov r15, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
adox r11, r12
adox r14, rbp
adcx rdi, r10
mov rdx, 0x0 
adox rbx, rdx
mov r12, -0x3 
inc r12
adox rcx, r13
adox r15, r9
adox r8, [ rsp - 0x18 ]
adox rdi, [ rsp - 0x28 ]
adcx r10, rdx
adox r10, [ rsp - 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r13, rcx, [ rsi + 0x8 ]
clc
adcx rcx, r15
mov rdx, [ rsi + 0x8 ]
mulx r9, rbp, [ rax + 0x10 ]
seto dl
inc r12
adox r13, [ rsp - 0x30 ]
mov r15, 0xd838091dd2253531 
xchg rdx, r15
mov [ rsp - 0x10 ], rbx
mulx rbx, r12, rcx
adox rbp, [ rsp - 0x38 ]
mov rbx, 0xffffffffffffffff 
mov rdx, r12
mov [ rsp - 0x8 ], r14
mulx r14, r12, rbx
adcx r13, r8
adcx rbp, rdi
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mulx rbx, rdi, [ rsi + 0x8 ]
adox rdi, r9
adcx rdi, r10
mov rdx, 0xfffffffefffffc2f 
mulx r9, r10, r8
mov r8, 0x0 
adox rbx, r8
mov rdx, -0x3 
inc rdx
adox r10, rcx
movzx r10, r15b
adcx r10, rbx
mov r15, r12
setc cl
clc
adcx r15, r9
mov r9, r12
adcx r9, r14
adcx r12, r14
adox r15, r13
adcx r14, r8
adox r9, rbp
adox r12, rdi
clc
adcx r15, [ rsp - 0x48 ]
adcx r9, [ rsp - 0x40 ]
mov r13, 0xd838091dd2253531 
mov rdx, r15
mulx rbp, r15, r13
mov rbp, 0xfffffffefffffc2f 
xchg rdx, r15
mulx rbx, rdi, rbp
adcx r11, r12
adox r14, r10
adcx r14, [ rsp - 0x8 ]
movzx r10, cl
adox r10, r8
mov rcx, 0xffffffffffffffff 
mulx r8, r12, rcx
mov rdx, r12
mov rcx, -0x2 
inc rcx
adox rdx, rbx
mov rbx, r12
adox rbx, r8
adox r12, r8
adcx r10, [ rsp - 0x10 ]
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r13, [ rax + 0x0 ]
setc dl
clc
adcx rdi, r15
adcx rcx, r9
adcx rbx, r11
mov rdi, 0x0 
adox r8, rdi
adcx r12, r14
adcx r8, r10
mov r15, -0x3 
inc r15
adox r13, rcx
mov r9, 0xd838091dd2253531 
xchg rdx, r13
mulx r14, r11, r9
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r10, [ rsi + 0x18 ]
setc dl
clc
adcx r10, rbp
mov rbp, 0xffffffffffffffff 
xchg rdx, r11
mulx r15, rdi, rbp
adox r10, rbx
movzx rbx, r11b
movzx r13, r13b
lea rbx, [ rbx + r13 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r11, [ rax + 0x10 ]
adcx r11, rcx
adox r11, r12
mov rdx, [ rax + 0x18 ]
mulx rcx, r12, [ rsi + 0x18 ]
adcx r12, rbp
adox r12, r8
mov rdx, 0xfffffffefffffc2f 
mulx rbp, r8, r13
mov r13, 0x0 
adcx rcx, r13
adox rcx, rbx
clc
adcx r8, r14
mov r8, rdi
seto r14b
mov rbx, -0x3 
inc rbx
adox r8, rbp
adcx r8, r10
mov r10, rdi
adox r10, r15
adox rdi, r15
adox r15, r13
adcx r10, r11
adcx rdi, r12
adcx r15, rcx
movzx r11, r14b
adc r11, 0x0
mov r12, r8
sub r12, rdx
mov rbp, r10
mov r14, 0xffffffffffffffff 
sbb rbp, r14
mov rcx, rdi
sbb rcx, r14
mov r13, r15
sbb r13, r14
sbb r11, 0x00000000
cmovc rbp, r10
cmovc r12, r8
cmovc r13, r15
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], r13
cmovc rcx, rdi
mov [ r11 + 0x10 ], rcx
mov [ r11 + 0x0 ], r12
mov [ r11 + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.6594
; seed 3968543174890881 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 972879 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=110, initial num_batches=31): 64566 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06636590984079212
; number reverted permutation / tried permutation: 66258 / 90466 =73.241%
; number reverted decision / tried decision: 49214 / 89533 =54.967%
; validated in 2.326s
