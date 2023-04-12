SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rbx
mulx rbx, rbp, [ rsi + 0x18 ]
add rbp, r15
adcx rax, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], rbp
mulx rbp, rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rax, rcx
adox r15, rbp
adox r11, rbx
adcx r8, r10
mov r10, 0xffffffff 
mov rdx, r10
mulx rcx, r10, r12
mov rbx, 0x0 
adcx r9, rbx
clc
adcx r10, r14
adcx rcx, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r14, [ rsi + 0x8 ]
adox rdi, rbx
xor rdx, rdx
adox r14, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, rbx, [ rsi + 0x10 ]
mov rdx, r12
adcx rdx, [ rsp - 0x18 ]
adox rbx, rbp
adcx r10, r14
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, [ rsi + 0x0 ]
adox rbp, r13
mov rdx, 0x0 
adox r14, rdx
mov r13, 0xffffffff00000001 
mov rdx, r13
mov [ rsp - 0x10 ], r9
mulx r9, r13, r12
adcx rcx, rbx
adcx r13, rbp
adcx r9, r14
mov r12, -0x2 
inc r12
adox r10, [ rsp - 0x20 ]
adox rax, rcx
mov rbx, 0xffffffff 
mov rdx, r10
mulx rbp, r10, rbx
mov r14, 0xffffffffffffffff 
mulx r12, rcx, r14
setc bl
clc
adcx r10, r12
mov r12, 0x0 
adcx rbp, r12
clc
adcx rcx, rdx
adcx r10, rax
adox r15, r13
adcx rbp, r15
mov rcx, 0xffffffff00000001 
mulx rax, r13, rcx
adox r11, r9
adcx r13, r11
mov rdx, [ rsi + 0x0 ]
mulx r15, r9, [ rsi + 0x10 ]
movzx rdx, bl
adox rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rbx, [ rsi + 0x8 ]
adcx rax, rdi
seto dl
mov rdi, -0x3 
inc rdi
adox r9, r10
movzx r10, dl
adcx r10, r12
mov rdx, r14
mulx r12, r14, r9
clc
adcx rbx, r15
adox rbx, rbp
mov rdx, rcx
mulx rbp, rcx, r9
adcx r11, [ rsp - 0x38 ]
adox r11, r13
mov rdx, [ rsi + 0x10 ]
mulx r15, r13, [ rsi + 0x18 ]
adcx r13, [ rsp - 0x40 ]
adox r13, rax
mov rdx, 0xffffffff 
mulx rdi, rax, r9
mov rdx, 0x0 
adcx r15, rdx
adox r15, r10
clc
adcx rax, r12
adcx rdi, rdx
clc
adcx r14, r9
adcx rax, rbx
seto r14b
mov r9, -0x3 
inc r9
adox rax, [ rsp - 0x48 ]
mov r10, 0xffffffff 
mov rdx, r10
mulx r12, r10, rax
adcx rdi, r11
adcx rcx, r13
adcx rbp, r15
movzx rbx, r14b
mov r11, 0x0 
adcx rbx, r11
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r14, r13, rax
clc
adcx r10, r14
adcx r12, r11
adox rdi, [ rsp - 0x28 ]
mov r15, 0xffffffff00000001 
mov rdx, r15
mulx r14, r15, rax
clc
adcx r13, rax
adcx r10, rdi
adox rcx, [ rsp - 0x30 ]
adcx r12, rcx
adox r8, rbp
adcx r15, r8
adox rbx, [ rsp - 0x10 ]
adcx r14, rbx
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov rax, r10
mov rbp, 0xffffffffffffffff 
sub rax, rbp
mov rdi, r12
mov rcx, 0xffffffff 
sbb rdi, rcx
mov r8, r15
sbb r8, 0x00000000
mov rbx, r14
sbb rbx, rdx
movzx r9, r13b
sbb r9, 0x00000000
cmovc rdi, r12
cmovc rbx, r14
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], rbx
mov [ r9 + 0x8 ], rdi
cmovc r8, r15
mov [ r9 + 0x10 ], r8
cmovc rax, r10
mov [ r9 + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.6444
; seed 4064841588498464 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1069704 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 79018 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07386903292873542
; number reverted permutation / tried permutation: 70014 / 90236 =77.590%
; number reverted decision / tried decision: 42413 / 89763 =47.250%
; validated in 1.54s
