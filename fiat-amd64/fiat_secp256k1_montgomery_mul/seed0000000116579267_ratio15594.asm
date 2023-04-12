SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r9, r8, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rbp
mulx rbp, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
xor rdx, rdx
adox r8, r10
adcx rbx, r11
mov rdx, [ rax + 0x10 ]
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
adcx r8, rbp
adcx r11, r10
mov rdx, 0x0 
adcx rdi, rdx
mov rbp, r12
clc
adcx rbp, r9
adox rbp, rbx
mov r9, r12
adcx r9, r13
adcx r12, r13
adcx r13, rdx
adox r9, r8
adox r12, r11
clc
adcx rcx, rbp
adox r13, rdi
mov rbx, 0xd838091dd2253531 
mov rdx, rcx
mulx r10, rcx, rbx
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mulx rbp, rdi, rcx
seto dl
mov rbx, -0x2 
inc rbx
adox r14, [ rsp - 0x20 ]
adcx r14, r9
mov r9, 0xfffffffefffffc2f 
xchg rdx, rcx
mov [ rsp - 0x10 ], r14
mulx r14, rbx, r9
adox r8, [ rsp - 0x28 ]
adcx r8, r12
mov rdx, [ rax + 0x18 ]
mulx r9, r12, [ rsi + 0x8 ]
adox r12, r11
adcx r12, r13
mov rdx, 0x0 
adox r9, rdx
mov r13, rdi
mov r11, -0x3 
inc r11
adox r13, r14
movzx r14, cl
adcx r14, r9
mov rcx, rdi
adox rcx, rbp
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r12
mulx r12, r14, [ rax + 0x8 ]
setc dl
clc
adcx r14, [ rsp - 0x30 ]
adcx r9, r12
adcx r15, r11
mov r11, [ rsp - 0x18 ]
mov r12, 0x0 
adcx r11, r12
clc
adcx rbx, r10
adcx r13, [ rsp - 0x10 ]
adcx rcx, r8
setc bl
clc
adcx r13, [ rsp - 0x38 ]
adox rdi, rbp
adox rbp, r12
mov r10, 0xd838091dd2253531 
xchg rdx, r13
mulx r12, r8, r10
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rbx, bl
adox rbx, r12
adox rdi, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, r8
mulx r10, r12, rbx
movzx rbx, r13b
mov [ rsp + 0x8 ], r10
mov r10, 0x0 
adox rbx, r10
mov r13, 0xfffffffefffffc2f 
mov [ rsp + 0x10 ], r11
mulx r11, r10, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbx
mulx rbx, r13, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r10, r8
adcx r14, rcx
adcx r9, rdi
mov rdx, [ rax + 0x8 ]
mulx rcx, r10, [ rsi + 0x18 ]
adcx r15, rbp
mov rdx, [ rax + 0x18 ]
mulx rdi, r8, [ rsi + 0x18 ]
mov rdx, r12
seto bpl
mov [ rsp + 0x20 ], rdi
mov rdi, -0x2 
inc rdi
adox rdx, r11
mov r11, [ rsp + 0x18 ]
adcx r11, [ rsp + 0x10 ]
setc dil
clc
adcx r10, rbx
mov rbx, r12
adox rbx, [ rsp + 0x8 ]
adox r12, [ rsp + 0x8 ]
adcx rcx, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
mov [ rsp + 0x28 ], r8
setc r8b
clc
mov byte [ rsp + 0x30 ], dil
mov rdi, -0x1 
movzx rbp, bpl
adcx rbp, rdi
adcx r14, rdx
adcx rbx, r9
seto bpl
inc rdi
adox r13, r14
adox r10, rbx
movzx r9, bpl
mov rdx, [ rsp + 0x8 ]
lea r9, [ r9 + rdx ]
adcx r12, r15
adcx r9, r11
adox rcx, r12
mov rdx, 0xd838091dd2253531 
mulx r11, r15, r13
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rbp, r11, r15
mov r14, 0xfffffffefffffc2f 
mov rdx, r15
mulx rbx, r15, r14
movzx r12, byte [ rsp + 0x30 ]
adcx r12, rdi
mov rdx, r11
clc
adcx rdx, rbx
mov rbx, r11
adcx rbx, rbp
adcx r11, rbp
adcx rbp, rdi
clc
adcx r15, r13
movzx r15, r8b
mov r13, [ rsp + 0x20 ]
lea r15, [ r15 + r13 ]
adcx rdx, r10
adox r9, [ rsp + 0x28 ]
adox r15, r12
adcx rbx, rcx
adcx r11, r9
adcx rbp, r15
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov r8, rdx
sub r8, r14
mov r10, rbx
mov rcx, 0xffffffffffffffff 
sbb r10, rcx
mov r12, r11
sbb r12, rcx
mov r9, rbp
sbb r9, rcx
movzx r15, r13b
sbb r15, 0x00000000
cmovc r9, rbp
cmovc r12, r11
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], r12
mov [ r15 + 0x18 ], r9
cmovc r8, rdx
cmovc r10, rbx
mov [ r15 + 0x0 ], r8
mov [ r15 + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5594
; seed 2814447780171214 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 979126 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 63945 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06530824429133737
; number reverted permutation / tried permutation: 67043 / 90224 =74.307%
; number reverted decision / tried decision: 50447 / 89775 =56.193%
; validated in 2.272s
