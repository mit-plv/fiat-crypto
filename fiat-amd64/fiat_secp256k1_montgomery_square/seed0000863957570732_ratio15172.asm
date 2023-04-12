SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 200
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rdi
mulx rdi, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r14
mulx r14, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox r8, r14
adox rbx, r9
adox r11, r13
adox rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rsi + 0x0 ]
adcx rbp, r15
adcx r12, rdi
mov rdx, -0x2 
inc rdx
adox rax, r14
mov rdx, [ rsi + 0x10 ]
mulx rdi, r15, rdx
adox r15, r10
mov rdx, [ rsi + 0x0 ]
mulx r13, r10, [ rsi + 0x18 ]
adcx r10, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r13, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], rbx
mulx rbx, r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r8
mulx r8, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], rax
mulx rax, r15, [ rsi + 0x8 ]
clc
adcx rcx, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
adcx rdx, [ rsp - 0x48 ]
adcx r15, [ rsp - 0x40 ]
mov [ rsp + 0x20 ], r9
mov r9, 0xfffffffefffffc2f 
xchg rdx, r11
mov [ rsp + 0x28 ], r15
mov [ rsp + 0x30 ], r13
mulx r13, r15, r9
adox rbx, rdi
mov rdi, 0xffffffffffffffff 
mov [ rsp + 0x38 ], rbx
mulx rbx, r9, rdi
mov rdx, 0x0 
adox r8, rdx
mov rdi, r9
mov [ rsp + 0x40 ], r8
mov r8, -0x3 
inc r8
adox rdi, r13
adcx rax, rdx
clc
adcx r15, [ rsp - 0x28 ]
adcx rdi, rbp
mov r15, r9
adox r15, rbx
adox r9, rbx
adcx r15, r12
adox rbx, rdx
adcx r9, r10
mov rbp, -0x3 
inc rbp
adox r14, rdi
adox rcx, r15
mov rbp, 0xd838091dd2253531 
mov rdx, r14
mulx r12, r14, rbp
mov r12, 0xffffffffffffffff 
xchg rdx, r14
mulx r13, r10, r12
adox r11, r9
adcx rbx, [ rsp + 0x30 ]
mov rdi, 0xfffffffefffffc2f 
mulx r9, r15, rdi
mov rdx, r10
setc r8b
clc
adcx rdx, r9
mov r9, r10
adcx r9, r13
adcx r10, r13
adox rbx, [ rsp + 0x28 ]
seto r12b
mov rdi, -0x2 
inc rdi
adox r15, r14
adox rdx, rcx
setc r15b
clc
movzx r8, r8b
movzx r12, r12b
adcx r12, rdi
adcx rax, r8
setc r14b
clc
adcx rdx, [ rsp + 0x20 ]
adox r9, r11
adcx r9, [ rsp + 0x18 ]
mulx r11, rcx, rbp
mov r11, 0xfffffffefffffc2f 
xchg rdx, r11
mulx r12, r8, rcx
movzx rdi, r15b
lea rdi, [ rdi + r13 ]
adox r10, rbx
adcx r10, [ rsp + 0x10 ]
adox rdi, rax
movzx r13, r14b
mov r15, 0x0 
adox r13, r15
adcx rdi, [ rsp + 0x38 ]
mov rbx, -0x3 
inc rbx
adox r8, r11
adcx r13, [ rsp + 0x40 ]
mov r8, 0xffffffffffffffff 
mov rdx, rcx
mulx rax, rcx, r8
mov r14, rcx
setc r11b
clc
adcx r14, r12
mov rdx, rcx
adcx rdx, rax
adcx rcx, rax
adox r14, r9
adox rdx, r10
adox rcx, rdi
seto r9b
mov r12, -0x3 
inc r12
adox r14, [ rsp - 0x20 ]
adcx rax, r15
adox rdx, [ rsp + 0x8 ]
adox rcx, [ rsp + 0x0 ]
xchg rdx, rbp
mulx r10, r12, r14
clc
mov r10, -0x1 
movzx r9, r9b
adcx r9, r10
adcx r13, rax
mov rdi, 0xfffffffefffffc2f 
mov rdx, r12
mulx r9, r12, rdi
adox r13, [ rsp - 0x8 ]
movzx rax, r11b
adcx rax, r15
adox rax, [ rsp - 0x10 ]
mulx r15, r11, r8
mov rdx, r11
clc
adcx rdx, r9
seto r9b
inc r10
adox r12, r14
adox rdx, rbp
mov r12, r11
adcx r12, r15
adox r12, rcx
adcx r11, r15
adox r11, r13
adcx r15, r10
adox r15, rax
seto r14b
mov rbp, rdx
sub rbp, rdi
mov rcx, r12
sbb rcx, r8
mov r13, r11
sbb r13, r8
movzx rax, r14b
movzx r9, r9b
lea rax, [ rax + r9 ]
mov r9, r15
sbb r9, r8
sbb rax, 0x00000000
cmovc r13, r11
cmovc rbp, rdx
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x10 ], r13
cmovc r9, r15
cmovc rcx, r12
mov [ rax + 0x8 ], rcx
mov [ rax + 0x18 ], r9
mov [ rax + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5172
; seed 0000863957570732 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5580 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=115, initial num_batches=31): 381 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06827956989247312
; number reverted permutation / tried permutation: 357 / 497 =71.831%
; number reverted decision / tried decision: 289 / 502 =57.570%
; validated in 2.153s
