SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
xor rdx, rdx
adox rbx, r8
mov rbx, 0xffffffff00000001 
mov rdx, rbx
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, r8
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rax
mulx rax, r8, [ rsi + 0x8 ]
adcx r11, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], r14
mulx r14, r15, [ rsi + 0x10 ]
setc dl
clc
adcx rbp, r9
adox r11, rbp
adcx r15, rdi
movzx r9, dl
lea r9, [ r9 + r10 ]
adox r9, r15
adcx r12, r14
mov r10, 0x0 
adcx r13, r10
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, [ rsi + 0x10 ]
clc
adcx r8, rcx
adcx rdi, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, rcx, rdx
adcx rcx, r14
mov rdx, [ rsi + 0x0 ]
mulx r15, rbp, [ rsi + 0x8 ]
adcx rax, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], rax
mov [ rsp - 0x10 ], rcx
mulx rcx, rax, [ rsi + 0x8 ]
adox rbx, r12
clc
adcx r15, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x28 ]
adcx rax, r10
adox r13, [ rsp - 0x30 ]
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx rbp, r11
adcx r15, r9
mov r11, 0xffffffff00000001 
mov rdx, r11
mulx r9, r11, rbp
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx r10, r12, rbp
adcx r14, rbx
adcx rax, r13
mov rbx, 0xffffffff 
mov rdx, rbx
mulx r13, rbx, rbp
setc dl
movzx rdx, dl
adox rdx, rcx
clc
adcx rbx, r10
mov rcx, 0x0 
adcx r13, rcx
clc
adcx r12, rbp
adcx rbx, r15
adcx r13, r14
adcx r11, rax
adcx r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, rdx
setc dl
clc
adcx rbp, [ rsp - 0x38 ]
adcx r15, [ rsp - 0x40 ]
seto r14b
mov rax, -0x3 
inc rax
adox r12, rbx
mov rbx, 0xffffffff 
xchg rdx, rbx
mulx rax, rcx, r12
adox rbp, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rdi
mulx rdi, r13, [ rsi + 0x18 ]
adcx r13, r10
adox r15, r11
mov rdx, 0xffffffffffffffff 
mulx r10, r11, r12
mov rdx, 0x0 
adcx rdi, rdx
adox r13, r9
movzx r9, bl
movzx r14, r14b
lea r9, [ r9 + r14 ]
clc
adcx r11, r12
adox rdi, r9
seto r11b
mov r14, -0x3 
inc r14
adox rcx, r10
adox rax, rdx
adcx rcx, rbp
mov rbx, 0xffffffff00000001 
mov rdx, r12
mulx rbp, r12, rbx
adcx rax, r15
adcx r12, r13
inc r14
adox rcx, [ rsp - 0x48 ]
mov rdx, rcx
mulx r15, rcx, rbx
adox r8, rax
adcx rbp, rdi
adox r12, [ rsp - 0x8 ]
adox rbp, [ rsp - 0x10 ]
movzx r10, r11b
mov r13, 0x0 
adcx r10, r13
adox r10, [ rsp - 0x18 ]
mov r9, 0xffffffffffffffff 
mulx rdi, r11, r9
mov rax, 0xffffffff 
mulx r14, r13, rax
clc
adcx r13, rdi
mov rdi, 0x0 
adcx r14, rdi
clc
adcx r11, rdx
adcx r13, r8
adcx r14, r12
adcx rcx, rbp
adcx r15, r10
seto r11b
adc r11b, 0x0
movzx r11, r11b
mov rdx, r13
sub rdx, r9
mov r8, r14
sbb r8, rax
mov r12, rcx
sbb r12, 0x00000000
mov rbp, r15
sbb rbp, rbx
movzx r10, r11b
sbb r10, 0x00000000
cmovc r8, r14
cmovc r12, rcx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], r12
cmovc rdx, r13
mov [ r10 + 0x8 ], r8
cmovc rbp, r15
mov [ r10 + 0x0 ], rdx
mov [ r10 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5529
; seed 3728293613747396 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1101909 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=133, initial num_batches=31): 75247 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06828785317117839
; number reverted permutation / tried permutation: 67960 / 89864 =75.625%
; number reverted decision / tried decision: 42299 / 90135 =46.928%
; validated in 1.469s
