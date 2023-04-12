SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, r11, [ rax + 0x10 ]
adox r11, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rcx
adox rbp, r12
mov rcx, rdi
adcx rcx, r15
mov r12, rdi
adcx r12, r9
adcx rdi, r9
mov r15, 0x0 
adox r13, r15
adc r9, 0x0
test al, al
adox r14, r10
mov rdx, [ rax + 0x0 ]
mulx r10, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r14
mulx r14, r15, [ rsi + 0x18 ]
adcx r15, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mulx r15, r10, [ rax + 0x10 ]
adcx r10, r14
adox rcx, rbx
adox r12, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r10
mulx r10, r14, [ rax + 0x0 ]
adox rdi, rbp
adcx rbx, r15
seto dl
mov rbp, -0x2 
inc rbp
adox r14, rcx
mov r15, 0x0 
adcx r11, r15
mov cl, dl
mov rdx, [ rax + 0x10 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
clc
adcx r8, r10
adox r8, r12
adcx r15, [ rsp - 0x48 ]
adox r15, rdi
adcx r11, rbp
mov rdx, 0xd838091dd2253531 
mulx r10, r12, r14
mov r10, 0xfffffffefffffc2f 
mov rdx, r12
mulx rdi, r12, r10
mov rbp, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r11
mulx r11, r10, rbp
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r12, r14
mov r12, r10
seto r14b
mov rbp, -0x3 
inc rbp
adox r12, rdi
mov rdi, r10
adox rdi, r11
adox r10, r11
adcx r12, r8
adcx rdi, r15
seto r8b
dec rdx
movzx rcx, cl
adox rcx, rdx
adox r13, r9
seto r9b
inc rdx
mov rcx, -0x1 
movzx r14, r14b
adox r14, rcx
adox r13, [ rsp - 0x18 ]
adcx r10, r13
movzx r14, r9b
adox r14, rbx
movzx r15, r8b
lea r15, [ r15 + r11 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r9, r8, [ rsi + 0x10 ]
adcx r15, r14
mov rdx, [ rax + 0x10 ]
mulx r14, r13, [ rsi + 0x10 ]
seto dl
inc rcx
adox r8, rbx
movzx rbx, dl
adcx rbx, rcx
clc
adcx r11, r12
adox r13, r9
adcx r8, rdi
mov rdx, [ rax + 0x18 ]
mulx rdi, r12, [ rsi + 0x10 ]
adox r12, r14
adox rdi, rcx
mov rdx, 0xd838091dd2253531 
mulx r14, r9, r11
mov r14, 0xffffffffffffffff 
mov rdx, r9
mulx rcx, r9, r14
adcx r13, r10
mov r10, 0xfffffffefffffc2f 
mulx r14, rbp, r10
mov rdx, r9
mov r10, -0x2 
inc r10
adox rdx, r14
mov r14, r9
adox r14, rcx
adcx r12, r15
adox r9, rcx
adcx rdi, rbx
mov r15, 0x0 
adox rcx, r15
mov rbx, -0x3 
inc rbx
adox rbp, r11
adox rdx, r8
setc bpl
clc
adcx rdx, [ rsp - 0x40 ]
adox r14, r13
adox r9, r12
adox rcx, rdi
adcx r14, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x20 ]
movzx r11, bpl
adox r11, r15
mov r8, 0xd838091dd2253531 
mulx r12, r13, r8
adcx r11, [ rsp - 0x28 ]
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mulx rdi, rbp, r13
mov r15, 0xfffffffefffffc2f 
mov rdx, r13
mulx rbx, r13, r15
mov rdx, rbp
inc r10
adox rdx, rbx
mov rbx, rbp
adox rbx, rdi
adox rbp, rdi
setc r15b
clc
adcx r13, r12
adcx rdx, r14
adcx rbx, r9
adcx rbp, rcx
adox rdi, r10
adcx rdi, r11
movzx r13, r15b
adc r13, 0x0
mov r12, rdx
mov r14, 0xfffffffefffffc2f 
sub r12, r14
mov r9, rbx
mov rcx, 0xffffffffffffffff 
sbb r9, rcx
mov r15, rbp
sbb r15, rcx
mov r11, rdi
sbb r11, rcx
sbb r13, 0x00000000
cmovc r9, rbx
cmovc r15, rbp
cmovc r12, rdx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], r12
mov [ r13 + 0x10 ], r15
cmovc r11, rdi
mov [ r13 + 0x18 ], r11
mov [ r13 + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.7076
; seed 4107542008421555 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1394036 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 81731 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05862904544789374
; number reverted permutation / tried permutation: 65330 / 90142 =72.475%
; number reverted decision / tried decision: 59548 / 89857 =66.270%
; validated in 3.71s
