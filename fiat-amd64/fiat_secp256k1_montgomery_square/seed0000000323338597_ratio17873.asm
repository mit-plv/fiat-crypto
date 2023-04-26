SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 152
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
xor rdx, rdx
adox rax, rcx
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r9, r8, r11
mov r9, 0xfffffffefffffc2f 
mov rdx, r9
mulx rcx, r9, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r8
mov r8, r12
adcx r8, rcx
mov rcx, r12
adcx rcx, r13
adcx r12, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r13, rdx
adox r14, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rcx
mulx rcx, r13, rdx
clc
adcx r10, r12
adcx r13, rdi
mov rdx, [ rsi + 0x0 ]
mulx r12, rdi, [ rsi + 0x18 ]
adox rdi, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r13
mulx r13, r15, [ rsi + 0x18 ]
adcx r15, rcx
mov rdx, 0x0 
adox r12, rdx
adc r13, 0x0
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r13
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rcx
mov [ rsp - 0x10 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r12
mulx r12, r10, [ rsi + 0x10 ]
add rcx, r13
adcx r10, r15
adcx rbx, r12
mov rdx, [ rsi + 0x8 ]
mulx r15, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rbx
mulx rbx, r12, [ rsi + 0x0 ]
adc rbp, 0x0
xor rdx, rdx
adox r13, rbx
adcx r9, r11
adcx r8, rax
adcx r14, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r9, [ rsi + 0x10 ]
adox r9, r15
adcx rdi, [ rsp - 0x40 ]
mov rdx, [ rsp + 0x0 ]
adcx rdx, [ rsp - 0x48 ]
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, [ rsi + 0x18 ]
adox r15, r11
mov rdx, 0x0 
adox rbx, rdx
mov r11, -0x3 
inc r11
adox r12, r8
adox r13, r14
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r14, r8, r12
mov r14, 0xffffffffffffffff 
mov rdx, r8
mulx r11, r8, r14
adox r9, rdi
mov rdi, 0xfffffffefffffc2f 
mov [ rsp + 0x10 ], rbp
mulx rbp, r14, rdi
adox r15, rax
setc al
clc
adcx r14, r12
movzx r14, al
adox r14, rbx
mov rax, r8
seto bl
mov r12, -0x2 
inc r12
adox rax, rbp
adcx rax, r13
mov r13, r8
adox r13, r11
adox r8, r11
adcx r13, r9
mov rdx, 0x0 
adox r11, rdx
mov r9, -0x3 
inc r9
adox rax, [ rsp - 0x38 ]
adox r13, [ rsp - 0x8 ]
adcx r8, r15
adox r8, [ rsp - 0x28 ]
adcx r11, r14
movzx rbp, bl
adcx rbp, rdx
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx rbx, r15, rax
mov rdx, rdi
mulx rbx, rdi, r15
adox r11, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x20 ]
clc
adcx rdi, rax
mov rdi, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, rdi
mov rax, r15
seto dl
inc r12
adox rax, rbx
mov rbx, r15
adox rbx, r14
adox r15, r14
adcx rax, r13
adcx rbx, r8
adox r14, r12
adcx r15, r11
adcx r14, rbp
movzx r13, dl
adc r13, 0x0
xor r8, r8
adox rax, [ rsp - 0x18 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx r11, r12, rax
mov rdx, r12
mulx r12, r11, rdi
mov rbp, 0xfffffffefffffc2f 
mulx r9, r8, rbp
mov rdx, r11
adcx rdx, r9
mov r9, r11
adcx r9, r12
adcx r11, r12
adox rcx, rbx
adox r10, r15
adox r14, [ rsp + 0x8 ]
mov rbx, 0x0 
adcx r12, rbx
clc
adcx r8, rax
adcx rdx, rcx
adcx r9, r10
adcx r11, r14
adox r13, [ rsp + 0x10 ]
adcx r12, r13
setc r8b
seto r15b
mov rax, rdx
sub rax, rbp
mov rcx, r9
sbb rcx, rdi
mov r10, r11
sbb r10, rdi
movzx r14, r8b
movzx r15, r15b
lea r14, [ r14 + r15 ]
mov r15, r12
sbb r15, rdi
sbb r14, 0x00000000
cmovc rax, rdx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rax
cmovc r10, r11
cmovc r15, r12
mov [ r14 + 0x10 ], r10
mov [ r14 + 0x18 ], r15
cmovc rcx, r9
mov [ r14 + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7873
; seed 3558727933559628 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1060292 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=171, initial num_batches=31): 79046 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07455116137818639
; number reverted permutation / tried permutation: 77247 / 89791 =86.030%
; number reverted decision / tried decision: 65600 / 90208 =72.721%
; validated in 1.968s
