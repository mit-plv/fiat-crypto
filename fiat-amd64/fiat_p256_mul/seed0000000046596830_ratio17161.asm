SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
mov [ rsp - 0x58 ], r15
mov r15, 0xffffffff 
mov rdx, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, rbp
xor rdx, rdx
adox rcx, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r12, [ rax + 0x10 ]
adcx r15, r14
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], rbx
mulx rbx, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r14
mulx r14, r12, [ rsi + 0x0 ]
clc
adcx r13, rbp
adox r12, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ rax + 0x18 ]
adcx r15, rcx
adox r13, r14
adcx rdi, r12
mov rdx, 0x0 
adox r8, rdx
mov rbp, -0x3 
inc rbp
adox r9, r15
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r14, rcx, r9
mov r12, 0xffffffff00000001 
mov rdx, r12
mulx r15, r12, r9
adcx r11, r13
mov r13, 0xffffffff 
mov rdx, r13
mulx rbp, r13, r9
adcx r10, r8
setc r8b
clc
adcx r13, r14
mov r14, 0x0 
adcx rbp, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rbx
mulx rbx, r14, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r12
mulx r12, r15, [ rax + 0x8 ]
clc
adcx r15, [ rsp - 0x38 ]
adox r15, rdi
adcx r14, r12
mov rdx, [ rax + 0x18 ]
mulx r12, rdi, [ rsi + 0x8 ]
adcx rdi, rbx
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rcx, r9
adox r14, r11
adox rdi, r10
adcx r13, r15
movzx rcx, r8b
adox rcx, r12
adcx rbp, r14
mov rdx, [ rax + 0x8 ]
mulx r11, r9, [ rsi + 0x10 ]
adcx rdi, [ rsp - 0x8 ]
adcx rcx, [ rsp - 0x10 ]
setc dl
clc
adcx r9, [ rsp - 0x18 ]
movzx r8, dl
mov r10, 0x0 
adox r8, r10
mov rdx, [ rsi + 0x10 ]
mulx r15, rbx, [ rax + 0x10 ]
adcx rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, [ rax + 0x18 ]
adcx r12, r15
adc r14, 0x0
xor rdx, rdx
adox r13, [ rsp - 0x20 ]
mov r10, 0xffffffff 
mov rdx, r13
mulx r11, r13, r10
adox r9, rbp
mov rbp, 0xffffffffffffffff 
mulx r10, r15, rbp
adcx r13, r10
adox rbx, rdi
mov rdi, 0x0 
adcx r11, rdi
clc
adcx r15, rdx
adcx r13, r9
adcx r11, rbx
adox r12, rcx
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rax + 0x8 ]
adox r14, r8
seto dl
mov r8, -0x3 
inc r8
adox r13, [ rsp - 0x40 ]
mov r10, 0xffffffff00000001 
xchg rdx, r15
mulx rdi, rbx, r10
adcx rbx, r12
adcx rdi, r14
movzx rdx, r15b
mov r12, 0x0 
adcx rdx, r12
xchg rdx, rbp
mulx r14, r15, r13
mov rdx, [ rax + 0x18 ]
mulx r8, r12, [ rsi + 0x18 ]
clc
adcx rcx, [ rsp - 0x48 ]
adcx r9, [ rsp - 0x28 ]
adox rcx, r11
adox r9, rbx
adcx r12, [ rsp - 0x30 ]
mov rdx, 0x0 
adcx r8, rdx
adox r12, rdi
adox r8, rbp
mov r11, 0xffffffff 
mov rdx, r11
mulx rbx, r11, r13
clc
adcx r11, r14
mov rdx, r10
mulx rdi, r10, r13
seto bpl
mov r14, -0x2 
inc r14
adox r15, r13
mov r15, 0x0 
adcx rbx, r15
adox r11, rcx
adox rbx, r9
adox r10, r12
adox rdi, r8
movzx r13, bpl
adox r13, r15
mov rcx, r11
mov r9, 0xffffffffffffffff 
sub rcx, r9
mov r12, rbx
mov rbp, 0xffffffff 
sbb r12, rbp
mov r8, r10
sbb r8, 0x00000000
mov r15, rdi
sbb r15, rdx
sbb r13, 0x00000000
cmovc r12, rbx
cmovc rcx, r11
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rcx
cmovc r15, rdi
mov [ r13 + 0x18 ], r15
cmovc r8, r10
mov [ r13 + 0x8 ], r12
mov [ r13 + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.7161
; seed 1658496892007498 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1135899 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=123, initial num_batches=31): 76428 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06728415114371965
; number reverted permutation / tried permutation: 66938 / 89711 =74.615%
; number reverted decision / tried decision: 44068 / 90288 =48.808%
; validated in 1.783s
