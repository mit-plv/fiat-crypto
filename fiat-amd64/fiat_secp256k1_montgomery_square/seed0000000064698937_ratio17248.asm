SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0xd838091dd2253531 
mov rdx, r11
mulx rcx, r11, rax
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
test al, al
adox r9, rax
mov rdx, [ rsi + 0x8 ]
mulx rax, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], r12
mulx r12, rbp, r11
adcx r13, r10
adcx r15, r14
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
adcx r10, rdi
mov rdx, 0x0 
adcx r11, rdx
mov r14, rbp
clc
adcx r14, rbx
mov rbx, rbp
adcx rbx, r12
adcx rbp, r12
adox r14, r13
adox rbx, r15
mov rdx, [ rsi + 0x8 ]
mulx r13, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r15, [ rsi + 0x18 ]
adox rbp, r10
mov rdx, 0x0 
adcx r12, rdx
adox r12, r11
clc
adcx rdi, rax
adcx rcx, r13
adcx r15, r8
adcx rbx, rdx
clc
adcx r9, r14
adcx rdi, [ rsp - 0x38 ]
adcx rcx, rbp
mov rdx, [ rsi + 0x18 ]
mulx rax, r8, [ rsi + 0x8 ]
adcx r15, r12
setc dl
clc
adcx r8, [ rsp - 0x40 ]
mov r10b, dl
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mulx rbp, r13, r9
adcx r11, rax
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x30 ], r11
mulx r11, rax, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], r12
mulx r12, r8, r13
adcx rbp, r14
mov r14, r8
setc r13b
clc
adcx r14, r11
mov r11, r8
adcx r11, r12
adcx r8, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rbp
mov byte [ rsp - 0x10 ], r13b
mulx r13, rbp, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rax, r9
adcx r14, rdi
adcx r11, rcx
adcx r8, r15
movzx rax, r10b
adox rax, rbx
movzx rbx, byte [ rsp - 0x10 ]
mov r9, [ rsp - 0x20 ]
lea rbx, [ rbx + r9 ]
adcx r12, rax
seto dil
adc dil, 0x0
movzx rdi, dil
mov rdx, [ rsi + 0x10 ]
mulx r10, rcx, [ rsi + 0x8 ]
adox rcx, r13
mov rdx, [ rsi + 0x10 ]
mulx r9, r15, rdx
adox r15, r10
mov rdx, [ rsi + 0x18 ]
mulx rax, r13, [ rsi + 0x10 ]
adox r13, r9
adcx rbp, r14
mov rdx, 0xd838091dd2253531 
mulx r10, r14, rbp
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, r14
mov rdx, 0x0 
adox rax, rdx
adcx rcx, r11
adcx r15, r8
mov r11, 0xfffffffefffffc2f 
mov rdx, r11
mulx r8, r11, r14
adcx r13, r12
mov r12, r10
mov r14, -0x2 
inc r14
adox r12, r8
mov r8, r10
adox r8, r9
movzx r14, dil
adcx r14, rax
adox r10, r9
seto dil
mov rax, -0x2 
inc rax
adox r11, rbp
adox r12, rcx
adox r8, r15
setc r11b
clc
adcx r12, [ rsp - 0x48 ]
mov rbp, 0xd838091dd2253531 
mov rdx, rbp
mulx rcx, rbp, r12
adox r10, r13
movzx rcx, dil
lea rcx, [ rcx + r9 ]
mov r9, 0xfffffffefffffc2f 
mov rdx, rbp
mulx r15, rbp, r9
adox rcx, r14
movzx r13, r11b
mov r14, 0x0 
adox r13, r14
adcx r8, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x30 ]
mov r11, 0xffffffffffffffff 
mulx r14, rdi, r11
mov rdx, rdi
inc rax
adox rdx, r15
adcx rcx, [ rsp - 0x18 ]
mov r15, rdi
adox r15, r14
adcx rbx, r13
adox rdi, r14
setc r13b
clc
adcx rbp, r12
adcx rdx, r8
adcx r15, r10
adox r14, rax
adcx rdi, rcx
adcx r14, rbx
movzx rbp, r13b
adc rbp, 0x0
mov r12, rdx
sub r12, r9
mov r8, r15
sbb r8, r11
mov r10, rdi
sbb r10, r11
mov rcx, r14
sbb rcx, r11
sbb rbp, 0x00000000
cmovc rcx, r14
cmovc r12, rdx
cmovc r10, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x0 ], r12
mov [ rbp + 0x18 ], rcx
cmovc r8, r15
mov [ rbp + 0x8 ], r8
mov [ rbp + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.7248
; seed 1520455461385314 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1320391 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=99, initial num_batches=31): 80033 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06061310626927933
; number reverted permutation / tried permutation: 67417 / 89996 =74.911%
; number reverted decision / tried decision: 59060 / 90003 =65.620%
; validated in 3.5s
