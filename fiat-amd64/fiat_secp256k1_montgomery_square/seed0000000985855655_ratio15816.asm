SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, r8
mov r15, 0xfffffffefffffc2f 
mov rdx, rdi
mov [ rsp - 0x40 ], r14
mulx r14, rdi, r15
mov r15, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, r15
xor rdx, rdx
adox rdi, r8
mov rdi, r13
adcx rdi, r14
mov r8, r13
adcx r8, r12
setc r14b
clc
adcx r11, r9
adcx rbx, rcx
adcx rax, rbp
mov rcx, r12
setc r9b
clc
mov rbp, -0x1 
movzx r14, r14b
adcx r14, rbp
adcx rcx, r13
adcx r12, rdx
adox rdi, r11
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rsi + 0x0 ]
movzx rdx, r9b
lea rdx, [ rdx + r10 ]
adox r8, rbx
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, rdx
clc
adcx r11, r14
adcx rbx, [ rsp - 0x30 ]
adox rcx, rax
adox r12, r10
mov rdx, [ rsi + 0x8 ]
mulx rax, r9, [ rsi + 0x18 ]
adcx r9, [ rsp - 0x38 ]
mov rdx, 0x0 
adcx rax, rdx
clc
adcx r13, rdi
mov rdi, 0xd838091dd2253531 
mov rdx, rdi
mulx r14, rdi, r13
adcx r11, r8
adcx rbx, rcx
mov r14, 0xfffffffefffffc2f 
mov rdx, r14
mulx r10, r14, rdi
mov rdx, rdi
mulx r8, rdi, r15
adcx r9, r12
mov rcx, rdi
seto r12b
inc rbp
adox rcx, r10
movzx rdx, r12b
adcx rdx, rax
mov r12, rdi
adox r12, r8
adox rdi, r8
setc al
clc
adcx r14, r13
adcx rcx, r11
adox r8, rbp
adcx r12, rbx
adcx rdi, r9
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r9, rcx
adcx r8, r14
mov rdx, [ rsi + 0x10 ]
mulx rcx, r14, [ rsi + 0x18 ]
setc dl
clc
adcx r13, rbp
adox r13, r12
mov r12b, dl
mov rdx, [ rsi + 0x0 ]
mulx r15, rbp, [ rsi + 0x18 ]
adcx rbx, r11
adcx r10, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
movzx rdx, r12b
movzx rax, al
lea rdx, [ rdx + rax ]
setc al
clc
adcx r11, r15
adox rbx, rdi
adcx r14, rbp
movzx rdi, al
mov r12, [ rsp - 0x48 ]
lea rdi, [ rdi + r12 ]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r15, rdx
adox r10, r8
mov rdx, 0xd838091dd2253531 
mulx rbp, r8, r9
adox rdi, r12
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mulx r12, rbp, r8
adcx r15, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp - 0x20 ], r15
mulx r15, rcx, r8
mov r8, 0x0 
adcx rax, r8
mov rdx, rcx
clc
adcx rdx, r12
mov r12, rcx
adcx r12, r15
adcx rcx, r15
adcx r15, r8
clc
adcx rbp, r9
adcx rdx, r13
adcx r12, rbx
seto bpl
mov r9, -0x3 
inc r9
adox rdx, [ rsp - 0x28 ]
adcx rcx, r10
mov r13, 0xd838091dd2253531 
mulx r10, rbx, r13
mov r10, 0xffffffffffffffff 
xchg rdx, rbx
mulx r9, r8, r10
mov r10, 0xfffffffefffffc2f 
mov [ rsp - 0x18 ], rax
mulx rax, r13, r10
adcx r15, rdi
movzx rdi, bpl
mov rdx, 0x0 
adcx rdi, rdx
adox r11, r12
mov rbp, r8
clc
adcx rbp, rax
mov r12, r8
adcx r12, r9
adcx r8, r9
adcx r9, rdx
adox r14, rcx
clc
adcx r13, rbx
adox r15, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x18 ]
adcx rbp, r11
adcx r12, r14
adcx r8, r15
adcx r9, rdi
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov rbx, rbp
sub rbx, r10
mov rcx, r12
mov rax, 0xffffffffffffffff 
sbb rcx, rax
mov r11, r8
sbb r11, rax
mov r14, r9
sbb r14, rax
movzx r15, r13b
sbb r15, 0x00000000
cmovc r14, r9
cmovc r11, r8
cmovc rbx, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], r14
cmovc rcx, r12
mov [ r15 + 0x0 ], rbx
mov [ r15 + 0x8 ], rcx
mov [ r15 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5816
; seed 3166956192067621 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 941820 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=115, initial num_batches=31): 63286 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06719543012465228
; number reverted permutation / tried permutation: 69727 / 89888 =77.571%
; number reverted decision / tried decision: 52081 / 90111 =57.796%
; validated in 2.157s
