SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, r12
add r15, r8
mov r15, r14
mov r8, -0x2 
inc r8
adox r15, rdi
mov r12, r14
adox r12, r13
adox r14, r13
mov rdx, [ rsi + 0x8 ]
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r13, rdx
mov [ rsp - 0x38 ], rcx
mov rcx, -0x3 
inc rcx
adox rdi, r9
mov rdx, [ rsi + 0x0 ]
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], r10
mulx r10, r11, [ rsi + 0x0 ]
adcx r15, rdi
adox r11, r8
adox r9, r10
mov rdx, 0x0 
adox rcx, rdx
adcx r12, r11
adcx r14, r9
adcx r13, rcx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rbx, r15
mov r10, 0xd838091dd2253531 
mov rdx, r10
mulx r15, r10, rbx
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r11, r15, r10
setc r9b
clc
adcx rax, rbp
mov rbp, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x38 ]
mov rcx, 0x0 
adcx rdi, rcx
adox rax, r12
adox rbp, r14
adox r8, r13
mov r12, 0xfffffffefffffc2f 
mov rdx, r10
mulx r14, r10, r12
mov r13, r15
clc
adcx r13, r14
mov rdx, r15
adcx rdx, r11
adcx r15, r11
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, rcx, [ rsi + 0x10 ]
movzx rdx, r9b
adox rdx, rdi
mov r9, 0x0 
adcx r11, r9
clc
adcx r10, rbx
adcx r13, rax
seto r10b
mov rbx, -0x3 
inc rbx
adox rcx, r13
adcx r14, rbp
mov rdi, 0xd838091dd2253531 
xchg rdx, rdi
mulx rbp, rax, rcx
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rsi + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mulx rbx, r9, rax
adcx r15, r8
adcx r11, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, [ rsi + 0x10 ]
movzx rdx, r10b
mov [ rsp - 0x20 ], r11
mov r11, 0x0 
adcx rdx, r11
clc
adcx r8, r12
adcx rdi, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
mov r12, 0xffffffffffffffff 
xchg rdx, rax
mulx r11, r10, r12
mov rdx, 0x0 
adcx r13, rdx
mov r12, r10
clc
adcx r12, rbx
mov rbx, r10
adcx rbx, r11
adcx r10, r11
adox r8, r14
adcx r11, rdx
clc
adcx r9, rcx
adcx r12, r8
adox rdi, r15
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, [ rsi + 0x8 ]
adox rbp, [ rsp - 0x20 ]
adcx rbx, rdi
adcx r10, rbp
adox r13, rax
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, [ rsi + 0x0 ]
seto dl
mov rax, -0x2 
inc rax
adox r14, r12
mov r8, 0xd838091dd2253531 
xchg rdx, r14
mulx rdi, r12, r8
mov rdi, 0xfffffffefffffc2f 
xchg rdx, rdi
mulx rax, rbp, r12
setc dl
clc
adcx r9, r15
adox r9, rbx
seto bl
mov r15, 0x0 
dec r15
movzx rdx, dl
adox rdx, r15
adox r13, r11
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rsi + 0x10 ]
adcx r11, rcx
movzx rdx, r14b
mov rcx, 0x0 
adox rdx, rcx
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, rdx
adcx rcx, r15
adc r8, 0x0
add bl, 0xFF
adcx r10, r11
mov rdx, 0xffffffffffffffff 
mulx r15, rbx, r12
adcx rcx, r13
mov r12, rbx
adox r12, rax
adcx r8, r14
mov rax, rbx
adox rax, r15
adox rbx, r15
setc r13b
clc
adcx rbp, rdi
adcx r12, r9
mov rbp, 0x0 
adox r15, rbp
adcx rax, r10
adcx rbx, rcx
adcx r15, r8
setc dil
mov r9, r12
mov r11, 0xfffffffefffffc2f 
sub r9, r11
movzx r14, dil
movzx r13, r13b
lea r14, [ r14 + r13 ]
mov r10, rax
sbb r10, rdx
mov rcx, rbx
sbb rcx, rdx
mov r13, r15
sbb r13, rdx
sbb r14, 0x00000000
cmovc r9, r12
cmovc rcx, rbx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], r9
mov [ r14 + 0x10 ], rcx
cmovc r13, r15
cmovc r10, rax
mov [ r14 + 0x8 ], r10
mov [ r14 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5843
; seed 3821962705149226 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1823652 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=83, initial num_batches=31): 112354 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06160934213325788
; number reverted permutation / tried permutation: 66629 / 90086 =73.962%
; number reverted decision / tried decision: 38406 / 89913 =42.715%
; validated in 3.533s
