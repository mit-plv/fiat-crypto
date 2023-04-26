SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov [ rsp - 0x68 ], r13
mov r13, 0xfffffffefffffc2f 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
test al, al
adox r13, r11
mov r13, rbp
adcx r13, r14
mov r11, rbp
adcx r11, r12
adcx rbp, r12
mov rdx, [ rsi + 0x18 ]
mulx r14, rbx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rax, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, rcx, [ rsi + 0x0 ]
adox r13, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, [ rsi + 0x10 ]
adcx rax, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rcx
mulx rcx, r10, [ rsi + 0x18 ]
adcx r10, rdi
mov rdx, 0x0 
adcx rcx, rdx
adox r11, rax
adox rbp, r10
mov rdx, [ rsi + 0x8 ]
mulx rax, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r14
mulx r14, r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r15
mulx r15, rbx, [ rsi + 0x0 ]
clc
adcx r10, r15
adcx rdi, r14
adcx r8, rax
mov rdx, 0x0 
adcx r9, rdx
clc
adcx rbx, r13
adcx r10, r11
mov r13, 0xd838091dd2253531 
mov rdx, rbx
mulx r11, rbx, r13
mov r11, 0xfffffffefffffc2f 
xchg rdx, r11
mulx r14, rax, rbx
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, rbx
adox r12, rcx
adcx rdi, rbp
adcx r8, r12
setc cl
movzx rcx, cl
adox rcx, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rbx, [ rsi + 0x0 ]
clc
adcx rbp, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rbp
mulx rbp, r12, rdx
adcx r12, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r12
mulx r12, r9, [ rsi + 0x10 ]
adcx r9, rbp
mov rdx, r15
setc bpl
clc
adcx rdx, r14
mov r14, r15
adcx r14, r13
adcx r15, r13
mov [ rsp - 0x18 ], r9
setc r9b
clc
adcx rax, r11
adcx rdx, r10
adcx r14, rdi
seto al
mov r11, -0x2 
inc r11
adox rbx, rdx
mov r10, 0xd838091dd2253531 
mov rdx, r10
mulx rdi, r10, rbx
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mulx r11, rdi, r10
movzx rdx, bpl
lea rdx, [ rdx + r12 ]
adcx r15, r8
movzx r8, r9b
lea r8, [ r8 + r13 ]
adcx r8, rcx
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, rdx
movzx rdx, al
mov rbp, 0x0 
adcx rdx, rbp
adox r14, [ rsp - 0x28 ]
mov rax, [ rsp - 0x30 ]
clc
adcx rax, [ rsp - 0x38 ]
adox r15, [ rsp - 0x20 ]
seto r9b
mov [ rsp - 0x10 ], r12
mov r12, -0x3 
inc r12
adox rdi, rbx
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x8 ], rax
mulx rax, r12, r10
adcx rbx, [ rsp - 0x40 ]
adcx rcx, rbp
mov r10, r12
setc bpl
clc
adcx r10, r11
mov r11, r12
adcx r11, rax
adox r10, r14
adcx r12, rax
adox r11, r15
mov r14, 0x0 
adcx rax, r14
clc
mov r15, -0x1 
movzx r9, r9b
adcx r9, r15
adcx r8, [ rsp - 0x18 ]
adcx r13, rdi
setc dil
clc
adcx r10, [ rsp - 0x48 ]
mov r9, 0xd838091dd2253531 
mov rdx, r9
mulx r14, r9, r10
adox r12, r8
adcx r11, [ rsp - 0x8 ]
adox rax, r13
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r8, r14, r9
mov r13, 0xfffffffefffffc2f 
mov rdx, r9
mulx r15, r9, r13
adcx rbx, r12
adcx rcx, rax
movzx rdx, bpl
mov r12, [ rsp - 0x10 ]
lea rdx, [ rdx + r12 ]
movzx r12, dil
mov rbp, 0x0 
adox r12, rbp
adcx rdx, r12
mov rdi, r14
mov rax, -0x3 
inc rax
adox rdi, r15
mov r15, r14
adox r15, r8
setc r12b
clc
adcx r9, r10
adcx rdi, r11
adox r14, r8
adcx r15, rbx
adox r8, rbp
adcx r14, rcx
adcx r8, rdx
movzx r9, r12b
adc r9, 0x0
mov r10, rdi
sub r10, r13
mov r11, r15
mov rbx, 0xffffffffffffffff 
sbb r11, rbx
mov rcx, r14
sbb rcx, rbx
mov r12, r8
sbb r12, rbx
sbb r9, 0x00000000
cmovc r11, r15
cmovc r10, rdi
cmovc rcx, r14
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r10
mov [ r9 + 0x10 ], rcx
cmovc r12, r8
mov [ r9 + 0x8 ], r11
mov [ r9 + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.7818
; seed 3213472967258084 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1200428 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=126, initial num_batches=31): 81014 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06748759609072764
; number reverted permutation / tried permutation: 69792 / 90007 =77.541%
; number reverted decision / tried decision: 43698 / 89992 =48.558%
; validated in 2.574s
