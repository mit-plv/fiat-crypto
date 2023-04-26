SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov r13, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov [ rsp - 0x58 ], r15
mov r15, 0xfffffffefffffc2f 
mov rdx, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r10
mov r10, r13
adcx r10, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
adox rdi, rbp
adox r8, rbx
mov rdx, r13
adcx rdx, r14
adcx r13, r14
mov rbp, 0x0 
adcx r14, rbp
adox r9, rbp
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, rax
adox r10, r12
adcx rbp, r10
adox rbx, rdi
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx rax, r15, rbp
adox r13, r8
mov rdx, [ rsi + 0x8 ]
mulx r12, rax, rdx
adox r14, r9
mov rdx, 0xffffffffffffffff 
mulx r8, rdi, r15
seto r9b
mov r10, -0x2 
inc r10
adox rax, rcx
adox r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, [ rsi + 0x8 ]
adox rcx, [ rsp - 0x38 ]
adcx rax, rbx
adcx r11, r13
adcx rcx, r14
mov rdx, 0xfffffffefffffc2f 
mulx r13, rbx, r15
mov r15, 0x0 
adox r12, r15
mov r14, -0x3 
inc r14
adox rbx, rbp
movzx rbx, r9b
adcx rbx, r12
mov rbp, rdi
setc r9b
clc
adcx rbp, r13
mov r13, rdi
adcx r13, r8
adcx rdi, r8
adox rbp, rax
adox r13, r11
adcx r8, r15
adox rdi, rcx
adox r8, rbx
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rcx, [ rsi + 0x10 ]
movzx rdx, r9b
adox rdx, r15
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, r15
adox rax, r12
adcx rbx, rbp
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ rsi + 0x10 ]
adox rbp, r11
mov rdx, 0xd838091dd2253531 
mulx r15, r11, rbx
adcx rcx, r13
adcx rax, rdi
mov r15, 0xfffffffefffffc2f 
mov rdx, r15
mulx r13, r15, r11
adcx rbp, r8
mov rdi, 0x0 
adox r12, rdi
adcx r12, r9
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r9, r8, r11
mov rdx, [ rsi + 0x18 ]
mulx rdi, r11, [ rsi + 0x8 ]
mov rdx, r8
inc r10
adox rdx, r13
mov r13, r8
adox r13, r9
adox r8, r9
setc r14b
clc
adcx r15, rbx
adcx rdx, rcx
adox r9, r10
adcx r13, rax
adcx r8, rbp
mov r15, -0x3 
inc r15
adox rdx, [ rsp - 0x40 ]
adcx r9, r12
movzx rbx, r14b
adcx rbx, r10
clc
adcx r11, [ rsp - 0x48 ]
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rax, [ rsi + 0x18 ]
adcx rax, rdi
adox r11, r13
adox rax, r8
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, rdx
adcx r14, rbp
adcx r12, r10
mov rdx, 0xd838091dd2253531 
mulx r13, rdi, rcx
mov r13, 0xfffffffefffffc2f 
mov rdx, r13
mulx r8, r13, rdi
mov rbp, 0xffffffffffffffff 
mov rdx, rdi
mulx r10, rdi, rbp
adox r14, r9
adox r12, rbx
clc
adcx r13, rcx
mov r13, rdi
seto cl
inc r15
adox r13, r8
mov r9, rdi
adox r9, r10
adox rdi, r10
adcx r13, r11
adcx r9, rax
mov rbx, 0x0 
adox r10, rbx
adcx rdi, r14
adcx r10, r12
movzx r11, cl
adc r11, 0x0
mov rax, r13
mov rdx, 0xfffffffefffffc2f 
sub rax, rdx
mov r8, r9
sbb r8, rbp
mov r14, rdi
sbb r14, rbp
mov rcx, r10
sbb rcx, rbp
sbb r11, 0x00000000
cmovc r14, rdi
cmovc r8, r9
cmovc rcx, r10
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], r14
cmovc rax, r13
mov [ r11 + 0x18 ], rcx
mov [ r11 + 0x0 ], rax
mov [ r11 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.8602
; seed 2127043702865305 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1153402 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=129, initial num_batches=31): 76594 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06640702894567549
; number reverted permutation / tried permutation: 71220 / 90104 =79.042%
; number reverted decision / tried decision: 61382 / 89895 =68.282%
; validated in 2.968s
