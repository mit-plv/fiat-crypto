SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r9
mulx r9, r10, [ rsi + 0x10 ]
adox r10, rdi
adox r11, r9
mov rdx, 0xfffffffefffffc2f 
mulx r9, rdi, rbx
adcx rdi, rax
mov rdi, 0x0 
adox rcx, rdi
mov rax, r13
mov rbx, -0x3 
inc rbx
adox rax, r9
mov r9, r13
adox r9, r14
adcx rax, r15
adox r13, r14
adcx r9, r10
adox r14, rdi
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r9
mulx r9, r15, [ rsi + 0x18 ]
adcx r13, r11
mov rdx, -0x2 
inc rdx
adox rbp, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r11, [ rsi + 0x10 ]
adcx r14, rcx
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, rdx
adox r12, r9
setc dl
clc
adcx rdi, r10
adcx r8, rbx
mov bl, dl
mov rdx, [ rsi + 0x18 ]
mulx r10, r9, [ rsi + 0x10 ]
adcx r9, [ rsp - 0x48 ]
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r12
mulx r12, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rbp
mulx rbp, r15, rdx
adc r10, 0x0
xor rdx, rdx
adox r15, r12
adcx rcx, rax
adcx r15, [ rsp - 0x38 ]
mov rax, 0xd838091dd2253531 
mov rdx, rcx
mulx r12, rcx, rax
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r10
mulx r10, rax, [ rsi + 0x8 ]
adox rax, rbp
adcx rax, r13
mov rdx, [ rsi + 0x8 ]
mulx rbp, r13, [ rsi + 0x18 ]
adox r13, r10
adcx r13, r14
mov rdx, 0x0 
adox rbp, rdx
mov r14, 0xffffffffffffffff 
mov rdx, rcx
mulx r10, rcx, r14
movzx r14, bl
adcx r14, rbp
mov rbx, 0xfffffffefffffc2f 
mov [ rsp - 0x8 ], r9
mulx r9, rbp, rbx
mov rdx, rcx
mov rbx, -0x2 
inc rbx
adox rdx, r9
setc r9b
clc
adcx rbp, r12
adcx rdx, r15
mov rbp, rcx
adox rbp, r10
adcx rbp, rax
adox rcx, r10
mov r12, 0x0 
adox r10, r12
adcx rcx, r13
adcx r10, r14
movzx r15, r9b
adc r15, 0x0
add r11, rdx
mov rax, 0xd838091dd2253531 
mov rdx, r11
mulx r13, r11, rax
adcx rdi, rbp
mov r13, 0xfffffffefffffc2f 
xchg rdx, r13
mulx r14, r9, r11
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r12, rbp, r11
mov r11, rbp
inc rbx
adox r11, r14
mov r14, rbp
adox r14, r12
adcx r8, rcx
adcx r10, [ rsp - 0x8 ]
adcx r15, [ rsp - 0x10 ]
setc cl
clc
adcx r9, r13
adox rbp, r12
adcx r11, rdi
seto r9b
mov r13, -0x3 
inc r13
adox r11, [ rsp - 0x40 ]
adcx r14, r8
adcx rbp, r10
mov rdx, rax
mulx rdi, rax, r11
mov rdi, 0xffffffffffffffff 
mov rdx, rax
mulx r8, rax, rdi
adox r14, [ rsp - 0x18 ]
movzx r10, r9b
lea r10, [ r10 + r12 ]
adcx r10, r15
movzx r12, cl
adcx r12, rbx
adox rbp, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
adox r12, [ rsp - 0x30 ]
mov rcx, 0xfffffffefffffc2f 
mulx r9, r15, rcx
clc
adcx r15, r11
mov r15, rax
seto r11b
mov rdx, -0x3 
inc rdx
adox r15, r9
adcx r15, r14
mov rdx, rax
adox rdx, r8
adox rax, r8
adcx rdx, rbp
adcx rax, r10
adox r8, rbx
adcx r8, r12
movzx r14, r11b
adc r14, 0x0
mov rbp, r15
sub rbp, rcx
mov r10, rdx
sbb r10, rdi
mov r11, rax
sbb r11, rdi
mov r12, r8
sbb r12, rdi
sbb r14, 0x00000000
cmovc r12, r8
cmovc r10, rdx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], r12
cmovc r11, rax
mov [ r14 + 0x10 ], r11
cmovc rbp, r15
mov [ r14 + 0x0 ], rbp
mov [ r14 + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.7212
; seed 3395647694481984 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1329826 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=101, initial num_batches=31): 79860 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.060052969335837925
; number reverted permutation / tried permutation: 67726 / 89939 =75.302%
; number reverted decision / tried decision: 59253 / 90060 =65.793%
; validated in 3.544s
