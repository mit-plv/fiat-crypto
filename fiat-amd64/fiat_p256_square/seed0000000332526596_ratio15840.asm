SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
adcx r15, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r9
mulx r9, r14, [ rsi + 0x8 ]
adcx r14, rdi
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, rdi, [ rsi + 0x0 ]
adox rdi, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r8
mulx r8, r10, [ rsi + 0x0 ]
adox r10, r9
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], rbx
mulx rbx, r9, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r12
mulx r12, r13, r11
mov rdx, 0x0 
adox r8, rdx
adc rbp, 0x0
add r9, r12
mov r12, -0x3 
inc r12
adox r13, r11
adox r9, rax
adcx rbx, rdx
adox rbx, rdi
clc
adcx rcx, r9
adcx r15, rbx
mov r13, 0xffffffff00000001 
mov rdx, r11
mulx rax, r11, r13
adox r11, r10
adox rax, r8
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rsi + 0x10 ]
adcx r14, r11
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
seto dl
inc r12
adox r10, [ rsp - 0x28 ]
adox r8, [ rsp - 0x30 ]
adcx rax, [ rsp - 0x38 ]
movzx rbx, dl
adcx rbx, rbp
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rsi + 0x18 ]
adox rbp, r9
mov rdx, 0xffffffff 
mulx r12, r9, rcx
mov r13, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp - 0x20 ], rbp
mulx rbp, rcx, r13
setc r13b
clc
adcx r9, rbp
mov rbp, 0x0 
adcx r12, rbp
clc
adcx rcx, rdx
adcx r9, r15
adcx r12, r14
adox r11, rbp
mov rcx, -0x3 
inc rcx
adox rdi, r9
adox r10, r12
mov r15, 0xffffffff00000001 
mulx r9, r14, r15
mov rdx, rdi
mulx r12, rdi, r15
adcx r14, rax
adcx r9, rbx
mov rax, 0xffffffffffffffff 
mulx rbp, rbx, rax
adox r8, r14
adox r9, [ rsp - 0x20 ]
mov r14, 0xffffffff 
mulx r15, rcx, r14
movzx rax, r13b
mov r14, 0x0 
adcx rax, r14
clc
adcx rcx, rbp
adcx r15, r14
clc
adcx rbx, rdx
adcx rcx, r10
adcx r15, r8
adcx rdi, r9
adox r11, rax
adcx r12, r11
seto bl
adc bl, 0x0
movzx rbx, bl
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rsi + 0x18 ]
adox rbp, rcx
mov rdx, 0xffffffffffffffff 
mulx rax, r9, rbp
adcx r8, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
adox r8, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, rdx
adcx rcx, r10
adcx r15, r14
mov rdx, 0xffffffff 
mulx r10, r11, rbp
clc
adcx r11, rax
adcx r10, r14
clc
adcx r9, rbp
mov r9, 0xffffffff00000001 
mov rdx, rbp
mulx rax, rbp, r9
adox r13, rdi
adcx r11, r8
adcx r10, r13
adox rcx, r12
movzx rdi, bl
adox rdi, r15
adcx rbp, rcx
adcx rax, rdi
seto r12b
adc r12b, 0x0
movzx r12, r12b
mov rbx, r11
mov rdx, 0xffffffffffffffff 
sub rbx, rdx
mov r8, r10
mov r15, 0xffffffff 
sbb r8, r15
mov r13, rbp
sbb r13, 0x00000000
mov rcx, rax
sbb rcx, r9
movzx rdi, r12b
sbb rdi, 0x00000000
cmovc r13, rbp
cmovc r8, r10
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x10 ], r13
cmovc rbx, r11
cmovc rcx, rax
mov [ rdi + 0x0 ], rbx
mov [ rdi + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5840
; seed 1933178558222061 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1828500 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 122900 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06721356302980586
; number reverted permutation / tried permutation: 68130 / 90740 =75.083%
; number reverted decision / tried decision: 55805 / 89259 =62.520%
; validated in 1.983s
