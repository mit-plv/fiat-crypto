SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov [ rsp - 0x58 ], r15
xor r15, r15
adox rbp, rcx
mov rdx, [ rsi + 0x10 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
mov rdx, rbx
adcx rdx, r11
adox r8, r12
adox rax, r9
mov rdx, 0xffffffffffffffff 
mulx r9, r11, rbx
seto r12b
mov rdx, -0x2 
inc rdx
adox r11, r14
movzx r14, r12b
lea r14, [ r14 + r10 ]
mov r10, 0xffffffff 
mov rdx, r10
mulx r12, r10, rbx
adox r10, r9
mov rbx, 0x0 
adox r12, rbx
adcx r13, rbp
adcx r11, r8
mov rbp, -0x3 
inc rbp
adox rdi, r13
adcx r10, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, r8, [ rsi + 0x8 ]
setc dl
clc
adcx r8, r15
mov r15b, dl
mov rdx, [ rsi + 0x10 ]
mulx r13, r9, rdx
adcx r9, rax
mov rdx, [ rsi + 0x10 ]
mulx rbx, rax, [ rsi + 0x18 ]
adcx rax, r13
mov rdx, [ rsi + 0x8 ]
mulx rbp, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r9
mulx r9, rax, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r8
mulx r8, rbx, [ rsi + 0x8 ]
clc
adcx r13, rcx
adox r13, r11
adcx rax, rbp
adox rax, r10
adcx rbx, r9
mov rdx, 0x0 
adcx r8, rdx
clc
mov rcx, -0x1 
movzx r15, r15b
adcx r15, rcx
adcx r14, r12
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx r11, r12, rdi
adox rbx, r14
setc r11b
movzx r11, r11b
adox r11, r8
mulx r10, r15, r12
mov rbp, 0xffffffff00000000 
mov rdx, r12
mulx r9, r12, rbp
clc
adcx r15, r9
mov r8, 0xffffffff 
mulx r9, r14, r8
adcx r14, r10
seto r10b
inc rcx
adox rdx, rdi
adox r12, r13
adcx r9, rcx
clc
adcx r12, [ rsp - 0x48 ]
mov rdx, 0xffffffffffffffff 
mulx r13, rdi, r12
adox r15, rax
adox r14, rbx
adcx r15, [ rsp - 0x28 ]
adcx r14, [ rsp - 0x38 ]
mulx rax, r13, rdi
adox r9, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ rsi + 0x18 ]
seto dl
mov r8, -0x2 
inc r8
adox rcx, r11
movzx r11, dl
movzx r10, r10b
lea r11, [ r11 + r10 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, [ rsi + 0x18 ]
adox r10, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r10
mulx r10, rbp, rdx
adox rbp, r8
adcx r9, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x30 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x18 ], rbp
mulx rbp, r8, rdi
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], r9
mulx r9, r11, rdi
setc dl
clc
adcx r13, rbp
adcx r11, rax
mov rax, 0x0 
adox r10, rax
adc r9, 0x0
xor rbp, rbp
adox rdi, r12
adox r8, r15
adcx rbx, r8
mov rax, 0xffffffffffffffff 
xchg rdx, rax
mulx r12, rdi, rbx
mov r12, 0xffffffff00000000 
mov rdx, rdi
mulx r15, rdi, r12
adox r13, r14
mov r14, 0xffffffffffffffff 
mulx rbp, r8, r14
adcx rcx, r13
adox r11, [ rsp - 0x8 ]
adcx r11, [ rsp - 0x20 ]
adox r9, [ rsp - 0x10 ]
movzx r13, al
mov r12, 0x0 
adox r13, r12
adcx r9, [ rsp - 0x18 ]
adcx r10, r13
mov rax, -0x3 
inc rax
adox r8, r15
mov r15, rdx
setc r13b
clc
adcx r15, rbx
adcx rdi, rcx
mov r15, 0xffffffff 
mulx rcx, rbx, r15
adox rbx, rbp
adcx r8, r11
adcx rbx, r9
adox rcx, r12
adcx rcx, r10
movzx rdx, r13b
adc rdx, 0x0
mov rbp, rdi
sub rbp, 0x00000001
mov r11, r8
mov r9, 0xffffffff00000000 
sbb r11, r9
mov r13, rbx
sbb r13, r14
mov r10, rcx
sbb r10, r15
sbb rdx, 0x00000000
cmovc rbp, rdi
cmovc r11, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], r11
cmovc r10, rcx
mov [ rdx + 0x18 ], r10
cmovc r13, rbx
mov [ rdx + 0x10 ], r13
mov [ rdx + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4438
; seed 1876898539660246 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1835897 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=224, initial num_batches=31): 143653 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07824676438819825
; number reverted permutation / tried permutation: 67611 / 89986 =75.135%
; number reverted decision / tried decision: 57244 / 90013 =63.595%
; validated in 4.431s
