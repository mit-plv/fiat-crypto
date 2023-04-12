SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, r11
test al, al
adox r8, rcx
mov r10, 0xffffffff 
mov rdx, rdi
mulx rcx, rdi, r10
mov r10, 0xffffffff00000000 
mov [ rsp - 0x40 ], rax
mov [ rsp - 0x38 ], r15
mulx r15, rax, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], rbp
mulx rbp, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r14
mulx r14, rbp, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rbp
mulx rbp, r14, r10
adcx r14, r15
adcx rdi, rbp
mov r15, 0x0 
adcx rcx, r15
clc
adcx r10, r11
adcx rax, r8
adox r12, r9
adox rbx, r13
adcx r14, r12
mov r10, [ rsp - 0x28 ]
adox r10, r15
mov r11, -0x3 
inc r11
adox rax, [ rsp - 0x30 ]
adcx rdi, rbx
mulx r13, r9, rax
adcx rcx, r10
mov rdx, [ rsi + 0x8 ]
mulx r8, r13, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rbx, [ rsi + 0x8 ]
setc dl
clc
adcx r13, [ rsp - 0x38 ]
adox r13, r14
adcx rbp, r8
adox rbp, rdi
adcx rbx, r12
adcx r10, r15
adox rbx, rcx
mov r14, r9
clc
adcx r14, rax
mov r14, 0xffffffff00000000 
xchg rdx, r14
mulx rdi, rax, r9
adcx rax, r13
mov rcx, 0xffffffffffffffff 
mov rdx, r9
mulx r8, r9, rcx
movzx r12, r14b
adox r12, r10
mov r14, 0xffffffff 
mulx r10, r13, r14
seto dl
mov r11, -0x3 
inc r11
adox r9, rdi
adox r13, r8
adcx r9, rbp
adcx r13, rbx
adox r10, r15
mov bpl, dl
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rsi + 0x0 ]
adcx r10, r12
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, rdx
movzx rdx, bpl
adc rdx, 0x0
xor rbp, rbp
adox rdi, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
adox r12, [ rsp - 0x18 ]
adcx rbx, rax
adcx rdi, r9
xchg rdx, rcx
mulx rax, r15, rbx
mulx r9, rax, r15
mov rdx, r15
mulx rbp, r15, r14
adcx r8, r13
adcx r12, r10
mov r13, [ rsp - 0x20 ]
mov r10, 0x0 
adox r13, r10
mov r11, rdx
mov r14, -0x3 
inc r14
adox r11, rbx
mov r11, 0xffffffff00000000 
mulx r10, rbx, r11
adcx r13, rcx
adox rbx, rdi
setc cl
clc
adcx rax, r10
adcx r15, r9
adox rax, r8
mov rdi, 0x0 
adcx rbp, rdi
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mulx r8, r9, [ rsi + 0x8 ]
adox rbp, r13
mov rdx, [ rsi + 0x10 ]
mulx r10, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, r13, [ rsi + 0x18 ]
movzx rdx, cl
mov r14, 0x0 
adox rdx, r14
xor rcx, rcx
adox r13, rbx
adcx r9, rdi
adox r9, rax
adcx r12, r8
adcx r10, [ rsp - 0x8 ]
mov r14, [ rsp - 0x10 ]
adcx r14, rcx
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mulx r8, rax, r13
mov r8, rax
clc
adcx r8, r13
adox r12, r15
mulx r15, r8, rax
mov rdx, rax
mulx rdi, rax, r11
adcx rax, r9
adox r10, rbp
adox r14, rbx
mov rbp, 0xffffffff 
mulx r13, rbx, rbp
seto r9b
mov rdx, -0x3 
inc rdx
adox r8, rdi
adox rbx, r15
adox r13, rcx
adcx r8, r12
adcx rbx, r10
adcx r13, r14
setc r12b
mov r15, rax
sub r15, 0x00000001
mov rdi, r8
sbb rdi, r11
movzx r10, r12b
movzx r9, r9b
lea r10, [ r10 + r9 ]
mov r9, rbx
mov r14, 0xffffffffffffffff 
sbb r9, r14
mov r12, r13
sbb r12, rbp
sbb r10, 0x00000000
cmovc r9, rbx
cmovc r15, rax
cmovc r12, r13
cmovc rdi, r8
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], r12
mov [ r10 + 0x8 ], rdi
mov [ r10 + 0x0 ], r15
mov [ r10 + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3469
; seed 2112049415111129 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1236336 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=138, initial num_batches=31): 80835 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06538271149590402
; number reverted permutation / tried permutation: 69778 / 90117 =77.430%
; number reverted decision / tried decision: 46284 / 89882 =51.494%
; validated in 2.639s
