SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov r8, 0xfffffffefffffc2f 
mov rdx, rcx
mulx r9, rcx, r8
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mulx r8, r15, rbx
mov rbx, r15
xor rdx, rdx
adox rbx, r9
mov r9, r15
adox r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rax + 0x8 ]
adox r15, r8
mov rdx, 0x0 
adox r8, rdx
adcx rdi, r11
mov r11, -0x3 
inc r11
adox rcx, r10
adox rbx, rdi
mov rdx, [ rax + 0x10 ]
mulx r10, rcx, [ rsi + 0x0 ]
adcx rcx, r14
adcx rbp, r10
adox r9, rcx
adox r15, rbp
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x0 ]
adox r8, r12
clc
adcx r10, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, [ rax + 0x8 ]
mov rdx, 0xd838091dd2253531 
mulx r11, r12, r10
seto r11b
mov rdx, -0x2 
inc rdx
adox rbx, rcx
adox r14, rbp
adox r13, rdi
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mulx rcx, rdi, r12
adcx rbx, r9
mov r9, 0xffffffffffffffff 
mov rdx, r12
mulx rbp, r12, r9
mov rdx, r12
seto r9b
mov byte [ rsp - 0x40 ], r11b
mov r11, -0x2 
inc r11
adox rdx, rcx
movzx rcx, r9b
mov r11, [ rsp - 0x48 ]
lea rcx, [ rcx + r11 ]
mov r11, r12
adox r11, rbp
adox r12, rbp
mov r9, 0x0 
adox rbp, r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], rcx
mulx rcx, rbp, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rdi, r10
adox r9, rbx
mov rdx, [ rax + 0x8 ]
mulx r10, rdi, [ rsi + 0x10 ]
adcx r14, r15
adcx r13, r8
adox r11, r14
adox r12, r13
mov rdx, [ rsp - 0x30 ]
movzx r15, byte [ rsp - 0x40 ]
adcx r15, rdx
adox r15, [ rsp - 0x38 ]
setc r8b
clc
adcx rbp, r9
movzx rbx, r8b
mov rdx, 0x0 
adox rbx, rdx
mov r9, 0xd838091dd2253531 
mov rdx, rbp
mulx r14, rbp, r9
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rdi, rcx
adcx rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r8
mulx r8, r9, [ rax + 0x10 ]
adox r9, r10
adcx r9, r12
adox rcx, r8
mov rdx, 0xfffffffefffffc2f 
mulx r12, r10, rbp
adcx rcx, r15
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r8, r15, rbp
mov rbp, 0x0 
adox r11, rbp
mov rdx, r15
mov [ rsp - 0x20 ], r13
mov r13, -0x3 
inc r13
adox rdx, r12
mov r12, r15
adox r12, r8
adcx r11, rbx
adox r15, r8
adox r8, rbp
mov rbx, -0x3 
inc rbx
adox r10, r14
adox rdx, rdi
adox r12, r9
mov r10, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, rbx, [ rsi + 0x18 ]
adox r15, rcx
setc dl
clc
adcx r10, [ rsp - 0x20 ]
mov rdi, 0xd838091dd2253531 
xchg rdx, rdi
mulx rcx, r9, r10
mov rdx, [ rsi + 0x18 ]
mulx rbp, rcx, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, r13, [ rsi + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov byte [ rsp - 0x10 ], dil
mov [ rsp - 0x8 ], r15
mulx r15, rdi, r9
adox r8, r11
seto r11b
mov rdx, -0x2 
inc rdx
adox rbx, [ rsp - 0x28 ]
adox r13, r14
adox rcx, rbp
adcx rbx, r12
adcx r13, [ rsp - 0x8 ]
adcx rcx, r8
mov r12, 0xffffffffffffffff 
mov rdx, r9
mulx r14, r9, r12
movzx rdx, r11b
movzx rbp, byte [ rsp - 0x10 ]
lea rdx, [ rdx + rbp ]
mov rbp, r9
seto r11b
mov r8, -0x2 
inc r8
adox rbp, r15
movzx r15, r11b
mov r8, [ rsp - 0x18 ]
lea r15, [ r15 + r8 ]
adcx r15, rdx
mov r8, r9
adox r8, r14
adox r9, r14
mov r11, 0x0 
adox r14, r11
mov rdx, -0x3 
inc rdx
adox rdi, r10
adox rbp, rbx
adox r8, r13
adox r9, rcx
adox r14, r15
seto dil
adc dil, 0x0
movzx rdi, dil
mov r10, rbp
mov rbx, 0xfffffffefffffc2f 
sub r10, rbx
mov r13, r8
sbb r13, r12
mov rcx, r9
sbb rcx, r12
mov r15, r14
sbb r15, r12
movzx rdx, dil
sbb rdx, 0x00000000
cmovc rcx, r9
cmovc r10, rbp
cmovc r13, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rcx
mov [ rdx + 0x8 ], r13
cmovc r15, r14
mov [ rdx + 0x0 ], r10
mov [ rdx + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.8429
; seed 0440471727845612 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1169900 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=100, initial num_batches=31): 76536 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06542097615180785
; number reverted permutation / tried permutation: 67161 / 90119 =74.525%
; number reverted decision / tried decision: 45351 / 89880 =50.457%
; validated in 2.963s
