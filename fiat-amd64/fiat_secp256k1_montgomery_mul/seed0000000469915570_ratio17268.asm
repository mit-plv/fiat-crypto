SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rax + 0x8 ]
xor rdx, rdx
adox rdi, r11
adcx rcx, rbx
mov r11, 0xfffffffefffffc2f 
mov rdx, r11
mulx rbx, r11, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r9
mulx r9, rcx, r15
adcx r13, r8
mov r8, rcx
setc r15b
clc
adcx r8, rbx
mov rbx, rcx
adcx rbx, r9
adcx rcx, r9
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r11, r10
adcx r8, rdi
adox rbp, r14
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rax + 0x18 ]
adox r11, r12
adcx rbx, rbp
mov rdx, 0x0 
adox r10, rdx
mov r12, -0x3 
inc r12
adox r8, [ rsp - 0x38 ]
adcx rcx, r11
adox rbx, [ rsp - 0x40 ]
mov r14, 0xd838091dd2253531 
mov rdx, r14
mulx rdi, r14, r8
mov rdx, [ rax + 0x18 ]
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mulx r12, r11, r14
adox r13, rcx
adcx r9, r10
setc r10b
clc
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx rdi, [ rsp - 0x48 ]
adox rdi, r9
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r9, r15, r14
mov r14, 0x0 
adcx rbp, r14
mov rcx, r15
clc
adcx rcx, r12
mov r12, r15
adcx r12, r9
adcx r15, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r11, r8
adcx rcx, rbx
mov rdx, [ rax + 0x0 ]
mulx r8, r11, [ rsi + 0x10 ]
adcx r12, r13
setc dl
clc
adcx r11, rcx
mov rbx, 0xd838091dd2253531 
xchg rdx, r11
mulx rcx, r13, rbx
movzx rcx, r10b
adox rcx, rbp
seto r10b
mov rbp, -0x1 
inc rbp
mov rbp, -0x1 
movzx r11, r11b
adox r11, rbp
adox rdi, [ rsp - 0x30 ]
adox r9, rcx
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rcx, [ rax + 0x18 ]
movzx rdx, r10b
mov rbx, 0x0 
adox rdx, rbx
mov r10, -0x3 
inc r10
adox r14, r8
adcx r14, r12
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx rbx, r12, [ rsi + 0x10 ]
adox r12, r15
adox rcx, rbx
adcx r12, rdi
mov rdx, 0x0 
adox rbp, rdx
mov r15, 0xfffffffefffffc2f 
mov rdx, r13
mulx rdi, r13, r15
inc r10
adox r13, r11
mov r13, 0xffffffffffffffff 
mulx rbx, r11, r13
mov rdx, r11
setc r10b
clc
adcx rdx, rdi
mov rdi, r11
adcx rdi, rbx
adcx r11, rbx
setc r15b
clc
mov r13, -0x1 
movzx r10, r10b
adcx r10, r13
adcx r9, rcx
adox rdx, r14
adox rdi, r12
adcx rbp, r8
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
setc dl
clc
adcx r14, r8
setc r8b
clc
adcx r10, rcx
adcx r13, r12
movzx rcx, r15b
lea rcx, [ rcx + rbx ]
adox r11, r9
adox rcx, rbp
movzx rbx, dl
mov r15, 0x0 
adox rbx, r15
mov rdx, [ rax + 0x18 ]
mulx rbp, r9, [ rsi + 0x18 ]
adcx r9, rdi
adc rbp, 0x0
mov rdx, 0xd838091dd2253531 
mulx rdi, r12, r14
mov rdi, 0xfffffffefffffc2f 
mov rdx, r12
mulx r15, r12, rdi
add r8b, 0x7F
adox r10, [ rsp - 0x28 ]
adox r13, r11
adox r9, rcx
mov r8, 0xffffffffffffffff 
mulx rcx, r11, r8
mov rdx, r11
adcx rdx, r15
mov r15, r11
adcx r15, rcx
adcx r11, rcx
setc r8b
clc
adcx r12, r14
adcx rdx, r10
adcx r15, r13
adcx r11, r9
movzx r12, r8b
lea r12, [ r12 + rcx ]
adox rbp, rbx
adcx r12, rbp
seto r14b
adc r14b, 0x0
movzx r14, r14b
mov rbx, rdx
sub rbx, rdi
mov r10, r15
mov r13, 0xffffffffffffffff 
sbb r10, r13
mov r9, r11
sbb r9, r13
mov rcx, r12
sbb rcx, r13
movzx r8, r14b
sbb r8, 0x00000000
cmovc rbx, rdx
cmovc r10, r15
cmovc rcx, r12
cmovc r9, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r9
mov [ r8 + 0x18 ], rcx
mov [ r8 + 0x8 ], r10
mov [ r8 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7268
; seed 0394875760845083 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1180454 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=120, initial num_batches=31): 78354 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06637615697011488
; number reverted permutation / tried permutation: 68027 / 89960 =75.619%
; number reverted decision / tried decision: 59725 / 90039 =66.332%
; validated in 3.53s
