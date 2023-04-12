SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
xor r14, r14
adox rbx, r10
mov rdx, [ rsi + 0x18 ]
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
adox r15, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r10
mulx r10, rbp, rax
adox r8, rdi
adcx r12, r10
mov rdi, 0x0 
adox r9, rdi
adc r13, 0x0
xor r10, r10
adox rbp, rax
mov rdx, [ rsi + 0x18 ]
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mulx r9, r10, rdx
adcx r11, r14
adcx rdi, rcx
adcx r10, rbp
adox r12, rbx
adox r13, r15
mov rdx, 0x0 
adcx r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r14, [ rsi + 0x8 ]
clc
adcx rcx, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, rbp, [ rsi + 0x10 ]
adcx rbp, rbx
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x38 ], r9
mulx r9, rbx, rax
adox rbx, r8
adox r9, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rax, [ rsi + 0x18 ]
adcx rax, r15
mov rdx, 0x0 
adcx r8, rdx
clc
adcx r14, r12
adcx rcx, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, [ rsi + 0x10 ]
adcx rbp, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rsi + 0x10 ]
adcx rax, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r10
mulx r10, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r11
mulx r11, rdi, [ rsi + 0x10 ]
setc dl
clc
adcx r12, rbx
adcx r9, r13
adcx rdi, r10
movzx r13, dl
adox r13, r8
mov r8, 0xffffffffffffffff 
mov rdx, r14
mulx rbx, r14, r8
seto r10b
mov r8, -0x2 
inc r8
adox r14, rdx
mov r14, 0xffffffff 
mov [ rsp - 0x18 ], rdi
mulx rdi, r8, r14
setc r14b
clc
adcx r8, rbx
adox r8, rcx
mov rcx, 0x0 
adcx rdi, rcx
movzx rbx, r14b
lea rbx, [ rbx + r11 ]
clc
adcx r15, r8
adox rdi, rbp
mov rbp, 0xffffffff00000001 
mulx r14, r11, rbp
adcx r12, rdi
adox r11, rax
adox r14, r13
movzx rdx, r10b
adox rdx, rcx
mov rax, 0xffffffffffffffff 
xchg rdx, rax
mulx r13, r10, r15
mov r8, 0xffffffff 
mov rdx, r15
mulx rdi, r15, r8
mov r8, -0x3 
inc r8
adox r15, r13
adox rdi, rcx
adcx r9, r11
adcx r14, [ rsp - 0x18 ]
adcx rbx, rax
mov r11, -0x3 
inc r11
adox r10, rdx
mulx r11, r10, rbp
adox r15, r12
adox rdi, r9
adox r10, r14
adox r11, rbx
setc dl
clc
adcx r15, [ rsp - 0x48 ]
adcx rdi, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
adcx r11, [ rsp - 0x30 ]
movzx r12, dl
adox r12, rcx
mov rax, 0xffffffffffffffff 
mov rdx, r15
mulx r13, r15, rax
adcx r12, [ rsp - 0x38 ]
mov r9, 0xffffffff 
mulx rbx, r14, r9
mov r8, -0x3 
inc r8
adox r14, r13
adox rbx, rcx
mov r13, -0x3 
inc r13
adox r15, rdx
adox r14, rdi
adox rbx, r10
mulx r15, r13, rbp
adox r13, r11
adox r15, r12
setc dl
seto dil
mov r10, r14
sub r10, rax
movzx r11, dil
movzx rdx, dl
lea r11, [ r11 + rdx ]
mov rdx, rbx
sbb rdx, r9
mov r12, r13
sbb r12, 0x00000000
mov rdi, r15
sbb rdi, rbp
sbb r11, 0x00000000
cmovc r12, r13
cmovc rdi, r15
cmovc r10, r14
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r10
cmovc rdx, rbx
mov [ r11 + 0x8 ], rdx
mov [ r11 + 0x18 ], rdi
mov [ r11 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5551
; seed 3626884735557068 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1627702 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=229, initial num_batches=31): 136582 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0839109370142692
; number reverted permutation / tried permutation: 66885 / 90465 =73.935%
; number reverted decision / tried decision: 55520 / 89534 =62.010%
; validated in 2.533s
