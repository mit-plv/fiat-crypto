SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
mov r12, 0xfffffffefffffc2f 
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rax + 0x0 ]
test al, al
adox r12, r9
mov rdx, 0xffffffffffffffff 
mulx r9, r12, rbp
mov rbp, r12
adcx rbp, r13
mov r13, r12
adcx r13, r9
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r15
mulx r15, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r8
mulx r8, r14, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r10, rbx
adcx r14, r15
adox rbp, r10
adox r13, r14
mov rdx, [ rax + 0x18 ]
mulx r15, rbx, [ rsi + 0x0 ]
adcx rbx, r8
mov rdx, 0x0 
adcx r15, rdx
clc
adcx rdi, rbp
adox r12, rbx
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r10, r8, rdi
adox r9, r15
seto r10b
mov r14, -0x2 
inc r14
adox rcx, r11
mov rdx, [ rsi + 0x8 ]
mulx rbp, r11, [ rax + 0x10 ]
adcx rcx, r13
adox r11, [ rsp - 0x28 ]
adox rbp, [ rsp - 0x30 ]
adcx r11, r12
adcx rbp, r9
mov rdx, [ rsp - 0x38 ]
mov r13, 0x0 
adox rdx, r13
mov rbx, 0xfffffffefffffc2f 
xchg rdx, r8
mulx r12, r15, rbx
mov r9, 0xffffffffffffffff 
mulx r14, r13, r9
movzx rdx, r10b
adcx rdx, r8
mov r10, r13
mov r8, -0x2 
inc r8
adox r10, r12
mov r12, r13
adox r12, r14
adox r13, r14
mov r8, 0x0 
adox r14, r8
mov rbx, -0x3 
inc rbx
adox r15, rdi
adox r10, rcx
adox r12, r11
adox r13, rbp
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mulx rcx, rdi, [ rsi + 0x10 ]
setc dl
clc
adcx rdi, r10
mov r11, 0xd838091dd2253531 
xchg rdx, r11
mulx r10, rbp, rdi
mov rdx, r9
mulx r9, r10, rbp
adox r14, r15
movzx r15, r11b
adox r15, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, r11, [ rax + 0x8 ]
inc rbx
adox r11, rcx
adcx r11, r12
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, [ rax + 0x10 ]
adox r12, r8
adcx r12, r13
mov rdx, [ rsi + 0x10 ]
mulx r8, r13, [ rax + 0x18 ]
adox r13, rcx
adcx r13, r14
mov rdx, 0xfffffffefffffc2f 
mulx rcx, r14, rbp
seto bpl
inc rbx
adox r14, rdi
movzx r14, bpl
lea r14, [ r14 + r8 ]
adcx r14, r15
mov rdi, r10
setc r15b
clc
adcx rdi, rcx
adox rdi, r11
mov r11, r10
adcx r11, r9
adcx r10, r9
adcx r9, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r8, [ rax + 0x0 ]
clc
adcx r8, rdi
adox r11, r12
adox r10, r13
adox r9, r14
mov rdx, 0xd838091dd2253531 
mulx r13, r12, r8
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x18 ]
movzx rdx, r15b
adox rdx, rbx
mov r15, -0x3 
inc r15
adox r13, rbp
adcx r13, r11
adox rcx, [ rsp - 0x40 ]
adcx rcx, r10
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, rdi, [ rax + 0x18 ]
adox rdi, [ rsp - 0x48 ]
adox rbp, rbx
adcx rdi, r9
adcx rbp, r14
mov rdx, 0xfffffffefffffc2f 
mulx r10, r11, r12
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r14, r9, r12
mov r12, r9
mov r15, -0x3 
inc r15
adox r12, r10
setc r10b
clc
adcx r11, r8
mov r11, r9
adox r11, r14
adcx r12, r13
adcx r11, rcx
adox r9, r14
adox r14, rbx
adcx r9, rdi
adcx r14, rbp
movzx r8, r10b
adc r8, 0x0
mov r13, r12
mov rcx, 0xfffffffefffffc2f 
sub r13, rcx
mov rdi, r11
sbb rdi, rdx
mov r10, r9
sbb r10, rdx
mov rbp, r14
sbb rbp, rdx
sbb r8, 0x00000000
cmovc rdi, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rdi
cmovc r13, r12
cmovc rbp, r14
mov [ r8 + 0x0 ], r13
cmovc r10, r9
mov [ r8 + 0x10 ], r10
mov [ r8 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.8082
; seed 4262072099900711 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1872020 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=74, initial num_batches=31): 115923 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.061924017905791606
; number reverted permutation / tried permutation: 61550 / 90164 =68.264%
; number reverted decision / tried decision: 38377 / 89835 =42.719%
; validated in 3.879s
