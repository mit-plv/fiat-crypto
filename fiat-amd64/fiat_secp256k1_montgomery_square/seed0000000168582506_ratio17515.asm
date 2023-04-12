SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, r12
mov rcx, 0xffffffffffffffff 
mov rdx, rdi
mov [ rsp - 0x40 ], r11
mulx r11, rdi, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r14
mulx r14, r15, [ rsi + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r15
mulx r15, r14, rcx
xor rcx, rcx
adox r14, r12
mov r14, rdi
adcx r14, r15
mov r12, rdi
adcx r12, r11
adcx rdi, r11
adcx r11, rcx
clc
adcx rax, r13
adox r14, rax
mov rdx, [ rsi + 0x10 ]
mulx r15, r13, [ rsi + 0x0 ]
adcx r13, r10
adox r12, r13
mov rdx, [ rsi + 0x18 ]
mulx rax, r10, [ rsi + 0x0 ]
adcx r10, r15
adcx rax, rcx
adox rdi, r10
clc
adcx r8, r14
mov rdx, 0xd838091dd2253531 
mulx r15, r14, r8
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, rdx
adox r11, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r10, [ rsi + 0x8 ]
seto dl
mov [ rsp - 0x18 ], rbp
mov rbp, -0x3 
inc rbp
adox r15, r9
adox r10, r13
adcx r15, r12
mov r9, 0xffffffffffffffff 
xchg rdx, r14
mulx r13, r12, r9
adox rbx, rax
adcx r10, rdi
adcx rbx, r11
mov rdi, [ rsp - 0x18 ]
adox rdi, rcx
mov r11, 0xfffffffefffffc2f 
mulx rcx, rax, r11
movzx rdx, r14b
adcx rdx, rdi
mov r14, r12
inc rbp
adox r14, rcx
setc dil
clc
adcx rax, r8
mov rax, r12
adox rax, r13
adcx r14, r15
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r15, [ rsi + 0x10 ]
adcx rax, r10
adox r12, r13
seto dl
inc rbp
adox r15, r14
movzx r10, dl
lea r10, [ r10 + r13 ]
adcx r12, rbx
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx rbx, r13, r15
mov rdx, r13
mulx r13, rbx, r11
adcx r10, r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, rdx
movzx rdx, dil
mov r9, 0x0 
adcx rdx, r9
clc
adcx rcx, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
adcx rbp, [ rsp - 0x20 ]
adox rcx, rax
mov rdi, [ rsp - 0x28 ]
adcx rdi, r9
adox r14, r12
mov rax, 0xffffffffffffffff 
xchg rdx, r8
mulx r9, r12, rax
adox rbp, r10
mov rdx, r12
clc
adcx rdx, r13
mov r13, r12
adcx r13, r9
adcx r12, r9
mov r10, 0x0 
adcx r9, r10
clc
adcx rbx, r15
adcx rdx, rcx
adcx r13, r14
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, r14, [ rsi + 0x10 ]
adox rdi, r8
adcx r12, rbp
adcx r9, rdi
setc dl
clc
adcx rcx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
seto r8b
mov rbp, -0x2 
inc rbp
adox r15, rbx
adox rcx, r13
adox r14, r12
mov rbx, 0xd838091dd2253531 
xchg rdx, rbx
mulx rdi, r13, r15
mov rdx, [ rsi + 0x18 ]
mulx r12, rdi, rdx
mov rdx, r13
mulx rbp, r13, r11
adcx rdi, r10
adox rdi, r9
mulx r9, r10, rax
mov rdx, 0x0 
adcx r12, rdx
movzx rdx, bl
movzx r8, r8b
lea rdx, [ rdx + r8 ]
adox r12, rdx
mov r8, r10
clc
adcx r8, rbp
setc bl
clc
adcx r13, r15
adcx r8, rcx
mov r13, r9
seto r15b
mov rcx, 0x0 
dec rcx
movzx rbx, bl
adox rbx, rcx
adox r13, r10
adcx r13, r14
adox r10, r9
adcx r10, rdi
mov r14, 0x0 
adox r9, r14
adcx r9, r12
movzx rbp, r15b
adc rbp, 0x0
mov rdi, r8
sub rdi, r11
mov rdx, r13
sbb rdx, rax
mov r15, r10
sbb r15, rax
mov r12, r9
sbb r12, rax
sbb rbp, 0x00000000
cmovc rdx, r13
cmovc r15, r10
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], r15
cmovc r12, r9
mov [ rbp + 0x18 ], r12
cmovc rdi, r8
mov [ rbp + 0x8 ], rdx
mov [ rbp + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.7515
; seed 1000094118739888 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1071028 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 79599 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0743201858401461
; number reverted permutation / tried permutation: 71306 / 90101 =79.140%
; number reverted decision / tried decision: 43724 / 89898 =48.637%
; validated in 2.726s
