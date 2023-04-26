SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r10
adox r11, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, rbx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r10
mulx r10, rdi, rbx
mov rbx, r12
adcx rbx, r10
mov r10, r12
adcx r10, rbp
adcx r12, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, [ rsi + 0x0 ]
adox r9, rcx
mov rdx, 0x0 
adcx rbp, rdx
adox r8, rdx
xor rcx, rcx
adox rdi, rax
adox rbx, r15
adcx r14, rbx
mov rdi, 0xd838091dd2253531 
mov rdx, r14
mulx rax, r14, rdi
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, rdx
mov rdx, 0xfffffffefffffc2f 
mulx rdi, rcx, r14
adox r10, r11
adox r12, r9
mov r11, 0xffffffffffffffff 
mov rdx, r14
mulx r9, r14, r11
adox rbp, r8
seto r8b
mov rdx, -0x2 
inc rdx
adox r15, r13
adcx r15, r10
adox rbx, [ rsp - 0x10 ]
adcx rbx, r12
mov rdx, [ rsi + 0x18 ]
mulx r10, r13, [ rsi + 0x8 ]
adox r13, [ rsp - 0x18 ]
mov rdx, 0x0 
adox r10, rdx
adcx r13, rbp
mov r12, r14
mov rbp, -0x3 
inc rbp
adox r12, rdi
mov rdi, r14
adox rdi, r9
movzx rdx, r8b
adcx rdx, r10
setc r8b
clc
adcx rcx, rax
adox r14, r9
mov rcx, 0x0 
adox r9, rcx
adcx r12, r15
adcx rdi, rbx
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ rsi + 0x8 ]
adcx r14, r13
adcx r9, rax
mov rdx, -0x3 
inc rdx
adox r12, [ rsp - 0x20 ]
movzx rdx, r8b
adcx rdx, rcx
clc
adcx r15, [ rsp - 0x28 ]
mov r10, 0xd838091dd2253531 
xchg rdx, r12
mulx r8, r13, r10
adox r15, rdi
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rax, rdx
adcx rax, rbx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbx, [ rsi + 0x10 ]
adcx rbx, rdi
mov rdx, 0x0 
adcx rcx, rdx
mov rdi, 0xfffffffefffffc2f 
mov rdx, r13
mulx rbp, r13, rdi
clc
adcx r13, r8
adox rax, r14
adox rbx, r9
mulx r14, r13, r11
adox rcx, r12
mov r9, r13
seto r8b
mov r12, -0x2 
inc r12
adox r9, rbp
mov rdx, r13
adox rdx, r14
adox r13, r14
adcx r9, r15
mov r15, 0x0 
adox r14, r15
adcx rdx, rax
adcx r13, rbx
adcx r14, rcx
mov rbp, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbx, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, rdx
movzx rdx, r8b
adc rdx, 0x0
add r9, [ rsp - 0x30 ]
mov r8, [ rsp - 0x38 ]
inc r12
adox r8, [ rsp - 0x40 ]
xchg rdx, r9
mulx r11, r12, r10
adox rax, [ rsp - 0x48 ]
xchg rdx, rdi
mulx r10, r11, r12
adcx r8, rbp
adcx rax, r13
adox rcx, rbx
adcx rcx, r14
mov rbp, 0xffffffffffffffff 
mov rdx, r12
mulx r13, r12, rbp
mov r14, r12
seto bl
mov rdx, -0x2 
inc rdx
adox r14, r10
mov r10, r12
adox r10, r13
adox r12, r13
mov rdx, 0x0 
adox r13, rdx
mov rbp, -0x3 
inc rbp
adox r11, rdi
adox r14, r8
adox r10, rax
movzx r11, bl
lea r11, [ r11 + r15 ]
adcx r11, r9
adox r12, rcx
adox r13, r11
setc r15b
seto r9b
mov rdi, r14
mov r8, 0xfffffffefffffc2f 
sub rdi, r8
mov rax, r10
mov rbx, 0xffffffffffffffff 
sbb rax, rbx
mov rcx, r12
sbb rcx, rbx
movzx r11, r9b
movzx r15, r15b
lea r11, [ r11 + r15 ]
mov r15, r13
sbb r15, rbx
sbb r11, 0x00000000
cmovc r15, r13
cmovc rcx, r12
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], r15
mov [ r11 + 0x10 ], rcx
cmovc rdi, r14
mov [ r11 + 0x0 ], rdi
cmovc rax, r10
mov [ r11 + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5868
; seed 3390454552599296 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1710950 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=82, initial num_batches=31): 105827 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.061852771851895146
; number reverted permutation / tried permutation: 67172 / 90446 =74.268%
; number reverted decision / tried decision: 37714 / 89553 =42.114%
; validated in 3.664s
