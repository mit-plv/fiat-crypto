SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rax + 0x8 ]
test al, al
adox rbp, r10
adcx r9, rbx
mov rdx, [ rax + 0x18 ]
mulx r10, rbp, [ rsi + 0x10 ]
adcx r13, r8
adcx rbp, r14
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r14, [ rax + 0x8 ]
clc
adcx r14, r11
adcx rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ rax + 0x18 ]
adcx r11, r15
setc dl
clc
adcx rcx, r12
adox rcx, r14
mov r12, [ rsp - 0x10 ]
mov r15, 0x0 
adcx r12, r15
movzx rbx, dl
lea rbx, [ rbx + r8 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mulx r10, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x0 ], rbp
mov [ rsp + 0x8 ], r13
mulx r13, rbp, [ rsi + 0x18 ]
clc
adcx r15, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r15
mulx r15, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r9
mulx r9, rbp, [ rax + 0x10 ]
adcx r14, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r14
mulx r14, r10, [ rsi + 0x8 ]
adcx r13, r8
mov rdx, 0x0 
adcx r15, rdx
clc
adcx r14, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
adcx r9, [ rsp - 0x30 ]
mov r8, [ rsp - 0x38 ]
adcx r8, rdx
adox r12, rdi
adox r11, [ rsp - 0x40 ]
clc
adcx r10, rcx
adcx r14, r12
adox rbx, [ rsp - 0x48 ]
adcx rbp, r11
mov rdi, 0xffffffff 
mov rdx, r10
mulx rcx, r10, rdi
adcx r9, rbx
mov r12, 0xffffffffffffffff 
mulx rbx, r11, r12
seto r12b
movzx r12, r12b
adcx r12, r8
mov r8, -0x2 
inc r8
adox r10, rbx
mov rbx, 0x0 
adox rcx, rbx
mov r8, -0x3 
inc r8
adox r11, rdx
adox r10, r14
adox rcx, rbp
setc r11b
clc
adcx r10, [ rsp - 0x18 ]
mov r14, 0xffffffff00000001 
mulx rbx, rbp, r14
adox rbp, r9
adcx rcx, [ rsp + 0x20 ]
adox rbx, r12
movzx rdx, r11b
mov r9, 0x0 
adox rdx, r9
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mulx r9, r11, r10
inc r8
adox r11, r10
adcx rbp, [ rsp + 0x8 ]
adcx rbx, [ rsp + 0x0 ]
mov rdx, r10
mulx r11, r10, rdi
adcx r12, [ rsp - 0x8 ]
setc r8b
clc
adcx r10, r9
mov r9, 0x0 
adcx r11, r9
adox r10, rcx
adox r11, rbp
mulx rbp, rcx, r14
clc
adcx r10, [ rsp + 0x18 ]
adox rcx, rbx
mov rdx, r10
mulx rbx, r10, rdi
adox rbp, r12
adcx r11, [ rsp + 0x10 ]
movzx r12, r8b
adox r12, r9
adcx rcx, [ rsp + 0x28 ]
adcx r13, rbp
adcx r15, r12
mov r8, 0xffffffffffffffff 
mulx r12, rbp, r8
mov r14, -0x3 
inc r14
adox rbp, rdx
setc bpl
clc
adcx r10, r12
adox r10, r11
adcx rbx, r9
adox rbx, rcx
mov r11, 0xffffffff00000001 
mulx r12, rcx, r11
adox rcx, r13
adox r12, r15
movzx rdx, bpl
adox rdx, r9
mov r13, r10
sub r13, r8
mov rbp, rbx
sbb rbp, rdi
mov r15, rcx
sbb r15, 0x00000000
mov r9, r12
sbb r9, r11
sbb rdx, 0x00000000
cmovc r9, r12
cmovc r13, r10
cmovc rbp, rbx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r13
mov [ rdx + 0x8 ], rbp
mov [ rdx + 0x18 ], r9
cmovc r15, rcx
mov [ rdx + 0x10 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.6000
; seed 1703388720447270 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 934220 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 62577 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06698315172015157
; number reverted permutation / tried permutation: 67304 / 90124 =74.679%
; number reverted decision / tried decision: 50961 / 89875 =56.702%
; validated in 1.396s
