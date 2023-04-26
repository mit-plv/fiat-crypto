SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r9
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rbx
mulx rbx, r15, r9
xor r9, r9
adox rdi, rcx
mov rdi, r15
adcx rdi, r14
mov rcx, r15
adcx rcx, rbx
adcx r15, rbx
mov rdx, [ rsi + 0x18 ]
mulx r9, r14, [ rax + 0x18 ]
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r14
mulx r14, r9, [ rsi + 0x0 ]
clc
adcx r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r8, [ rax + 0x10 ]
adcx r8, r14
adcx r10, rbp
adox rdi, r9
adox rcx, r8
adox r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r14, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r14, rdi
adox rbx, r11
mov rdx, [ rsi + 0x8 ]
mulx r8, rbp, [ rax + 0x8 ]
seto dl
mov r10, -0x2 
inc r10
adox rbp, r9
mov dil, dl
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x8 ]
adox r9, r8
adcx rbp, rcx
adcx r9, r15
adox r12, r11
adcx r12, rbx
mov rdx, 0xd838091dd2253531 
mulx r15, rcx, r14
mov r15, 0xfffffffefffffc2f 
mov rdx, rcx
mulx rbx, rcx, r15
mov r8, 0xffffffffffffffff 
mulx r10, r11, r8
mov rdx, 0x0 
adox r13, rdx
mov r8, r11
mov r15, -0x3 
inc r15
adox r8, rbx
mov rdx, [ rax + 0x10 ]
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, r11
adox rdx, r10
adox r11, r10
mov [ rsp - 0x18 ], r15
movzx r15, dil
adcx r15, r13
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mulx r15, r13, [ rax + 0x8 ]
setc dl
clc
adcx rcx, r14
adcx r8, rbp
adcx rdi, r9
adcx r11, r12
seto cl
mov r14, -0x2 
inc r14
adox r13, [ rsp - 0x20 ]
movzx rbp, cl
lea rbp, [ rbp + r10 ]
adox rbx, r15
adcx rbp, [ rsp - 0x10 ]
movzx r9, dl
mov r12, 0x0 
adcx r9, r12
clc
adcx r8, [ rsp - 0x38 ]
mov r10, 0xd838091dd2253531 
mov rdx, r10
mulx rcx, r10, r8
mov rcx, 0xffffffffffffffff 
mov rdx, r10
mulx r15, r10, rcx
adcx r13, rdi
mov rdi, 0xfffffffefffffc2f 
mulx r14, r12, rdi
adcx rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rax + 0x18 ]
adox r11, [ rsp - 0x18 ]
mov rdx, 0x0 
adox rcx, rdx
adcx r11, rbp
adcx rcx, r9
mov rbp, r10
mov r9, -0x3 
inc r9
adox rbp, r14
setc r14b
clc
adcx r12, r8
adcx rbp, r13
mov r12, r10
adox r12, r15
adox r10, r15
adcx r12, rbx
mov rdx, [ rax + 0x10 ]
mulx r13, r8, [ rsi + 0x18 ]
adcx r10, r11
mov rdx, 0x0 
adox r15, rdx
adcx r15, rcx
movzx rbx, r14b
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r14, r11, [ rax + 0x8 ]
add r11, [ rsp - 0x40 ]
adcx r8, r14
inc r9
adox rbp, [ rsp - 0x48 ]
adox r11, r12
mov rdx, 0xd838091dd2253531 
mulx r12, rcx, rbp
mov rdx, rcx
mulx r12, rcx, rdi
mov r14, 0xffffffffffffffff 
mulx rdi, r9, r14
adox r8, r10
adcx r13, [ rsp - 0x28 ]
mov r10, [ rsp - 0x30 ]
mov rdx, 0x0 
adcx r10, rdx
mov r14, r9
clc
adcx r14, r12
mov r12, r9
adcx r12, rdi
adcx r9, rdi
adox r13, r15
adox r10, rbx
seto r15b
mov rbx, -0x3 
inc rbx
adox rcx, rbp
adox r14, r11
adox r12, r8
adcx rdi, rdx
adox r9, r13
adox rdi, r10
movzx rcx, r15b
adox rcx, rdx
mov rbp, r14
mov r11, 0xfffffffefffffc2f 
sub rbp, r11
mov r8, r12
mov r13, 0xffffffffffffffff 
sbb r8, r13
mov r15, r9
sbb r15, r13
mov r10, rdi
sbb r10, r13
sbb rcx, 0x00000000
cmovc r15, r9
cmovc r8, r12
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r8
cmovc r10, rdi
mov [ rcx + 0x10 ], r15
mov [ rcx + 0x18 ], r10
cmovc rbp, r14
mov [ rcx + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.7659
; seed 3981897717504057 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1834269 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 139985 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07631650537625616
; number reverted permutation / tried permutation: 64593 / 89932 =71.824%
; number reverted decision / tried decision: 57177 / 90067 =63.483%
; validated in 5.056s
