SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r13
mulx r13, r11, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r12
mulx r12, r13, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, rbp
adox rax, r12
mov rbp, 0xffffffffffffffff 
mov rdx, r11
mulx r12, r11, rbp
adox r14, r10
mov r10, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], rcx
mulx rcx, rbp, r10
adcx rbp, rbx
mov rbp, r11
seto bl
mov rdx, -0x2 
inc rdx
adox rbp, rcx
mov rcx, r11
adox rcx, r12
adox r11, r12
mov rdx, 0x0 
adox r12, rdx
adcx rbp, r13
adcx rcx, rax
movzx r13, bl
lea r13, [ r13 + r15 ]
adcx r11, r14
mov rdx, [ rsi + 0x8 ]
mulx rax, r15, rdx
adcx r12, r13
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbx, rbp
setc bpl
clc
adcx r15, r14
adcx r13, rax
mov rax, 0xd838091dd2253531 
mov rdx, rax
mulx r14, rax, rbx
adcx r8, r10
mov r14, 0x0 
adcx r9, r14
adox r15, rcx
adox r13, r11
adox r8, r12
mov rcx, 0xfffffffefffffc2f 
mov rdx, rax
mulx r11, rax, rcx
movzx r12, bpl
adox r12, r9
mov rbp, 0xffffffffffffffff 
mulx r9, r10, rbp
clc
adcx rax, rbx
mov rax, r10
seto bl
mov rdx, -0x3 
inc rdx
adox rax, r11
mov r11, r10
adox r11, r9
adox r10, r9
adcx rax, r15
adcx r11, r13
adcx r10, r8
adox r9, r14
adcx r9, r12
mov rdx, [ rsi + 0x0 ]
mulx r13, r15, [ rsi + 0x10 ]
movzx rdx, bl
adc rdx, 0x0
xor r8, r8
adox rdi, r13
mov r14, [ rsp - 0x28 ]
adox r14, [ rsp - 0x30 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rsi + 0x10 ]
adcx r15, rax
adox r12, [ rsp - 0x38 ]
adcx rdi, r11
mov rdx, 0xd838091dd2253531 
mulx r11, rax, r15
adcx r14, r10
mov rdx, rax
mulx r11, rax, rcx
mulx r8, r10, rbp
adcx r12, r9
mov r9, 0x0 
adox r13, r9
adcx r13, rbx
mov rbx, -0x3 
inc rbx
adox rax, r15
mov rax, r10
setc r15b
clc
adcx rax, r11
mov rdx, r10
adcx rdx, r8
adcx r10, r8
adcx r8, r9
adox rax, rdi
adox rdx, r14
adox r10, r12
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r14, [ rsi + 0x18 ]
adox r8, r13
clc
adcx rax, [ rsp - 0x40 ]
movzx rdx, r15b
adox rdx, r9
mov r12, -0x3 
inc r12
adox r14, [ rsp - 0x48 ]
mov r12, 0xd838091dd2253531 
xchg rdx, r12
mulx r13, r15, rax
adcx r14, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, r13, [ rsi + 0x18 ]
adox r13, r11
adcx r13, r10
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, rdx
adox r10, rdi
adcx r10, r8
adox r11, r9
adcx r11, r12
mov rdx, r15
mulx r8, r15, rcx
mov r12, -0x3 
inc r12
adox r15, rax
mulx r15, r12, rbp
mov rax, r12
setc dl
clc
adcx rax, r8
mov rdi, r12
adcx rdi, r15
adox rax, r14
adox rdi, r13
adcx r12, r15
adcx r15, r9
adox r12, r10
adox r15, r11
movzx r14, dl
adox r14, r9
mov r13, rax
sub r13, rcx
mov r10, rdi
sbb r10, rbp
mov rdx, r12
sbb rdx, rbp
mov r11, r15
sbb r11, rbp
sbb r14, 0x00000000
cmovc r13, rax
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], r13
cmovc r11, r15
cmovc rdx, r12
mov [ r14 + 0x18 ], r11
mov [ r14 + 0x10 ], rdx
cmovc r10, rdi
mov [ r14 + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7371
; seed 0264053644739726 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1844441 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=84, initial num_batches=31): 122588 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06646349761255578
; number reverted permutation / tried permutation: 66865 / 89895 =74.381%
; number reverted decision / tried decision: 57377 / 90104 =63.679%
; validated in 3.964s
