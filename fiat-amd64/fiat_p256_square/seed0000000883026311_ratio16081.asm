SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mulx r9, r8, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, rdx
xor rdx, rdx
adox r12, rax
adcx r8, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r13
mulx r13, r15, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r12
mulx r12, r10, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r10
mulx r10, r12, [ rsi + 0x10 ]
adcx r12, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, r13, [ rsi + 0x18 ]
adcx r13, r10
mov rdx, 0x0 
adcx rbp, rdx
mov r10, 0xffffffff00000001 
mov rdx, rax
mov [ rsp - 0x10 ], rbx
mulx rbx, rax, r10
adox r8, r15
adox r9, r12
adox rax, r13
clc
adcx r11, r8
mov rdx, 0xffffffff 
mulx r12, r15, r11
mov r13, 0xffffffffffffffff 
mov rdx, r11
mulx r8, r11, r13
setc r10b
clc
adcx r15, r8
adox rbx, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r8, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rdi, rcx
adcx r14, [ rsp - 0x10 ]
seto cl
dec rdx
movzx r10, r10b
adox r10, rdx
adox r9, rdi
adcx r8, [ rsp - 0x18 ]
adox r14, rax
mov rax, 0x0 
adcx r13, rax
clc
adcx r11, rbp
adcx r15, r9
adcx r12, r14
mov r11, 0xffffffff00000001 
mov rdx, r11
mulx r10, r11, rbp
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rsi + 0x10 ]
adox r8, rbx
adcx r11, r8
mov rdx, [ rsi + 0x10 ]
mulx r9, rbx, [ rsi + 0x18 ]
movzx rdx, cl
adox rdx, r13
adcx r10, rdx
setc cl
clc
adcx rdi, [ rsp - 0x30 ]
mov r14, [ rsp - 0x38 ]
adcx r14, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
adcx r9, rax
clc
adcx rbp, r15
adcx rdi, r12
adcx r14, r11
adcx rbx, r10
mov r13, 0xffffffffffffffff 
mov rdx, rbp
mulx r15, rbp, r13
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, [ rsi + 0x18 ]
movzx rdx, cl
adox rdx, rax
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r10, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r8, [ rsp - 0x40 ]
adox r10, r11
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, rdx
adox r11, rax
adcx r9, rcx
mov rdx, 0xffffffff 
mulx rax, rcx, r12
setc dl
clc
adcx rcx, r15
mov r15, 0x0 
adcx rax, r15
adox r13, r15
mov [ rsp - 0x8 ], r13
xor r13, r13
adox rbp, r12
adox rcx, rdi
adcx rcx, [ rsp - 0x48 ]
mov rbp, 0xffffffff00000001 
xchg rdx, r12
mulx rdi, r15, rbp
mov rdx, rbp
mulx r13, rbp, rcx
adox rax, r14
adox r15, rbx
adcx r8, rax
adcx r10, r15
adox rdi, r9
movzx r14, r12b
mov rbx, 0x0 
adox r14, rbx
mov r12, 0xffffffffffffffff 
mov rdx, rcx
mulx r9, rcx, r12
mov rax, -0x3 
inc rax
adox rcx, rdx
adcx r11, rdi
mov rcx, 0xffffffff 
mulx rdi, r15, rcx
seto dl
mov rax, -0x3 
inc rax
adox r15, r9
seto r9b
dec rbx
movzx rdx, dl
adox rdx, rbx
adox r8, r15
adcx r14, [ rsp - 0x8 ]
movzx rdx, r9b
lea rdx, [ rdx + rdi ]
adox rdx, r10
adox rbp, r11
adox r13, r14
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov r11, r8
sub r11, r12
mov rdi, rdx
sbb rdi, rcx
mov r15, rbp
sbb r15, 0x00000000
mov r9, r13
mov r14, 0xffffffff00000001 
sbb r9, r14
movzx rbx, r10b
sbb rbx, 0x00000000
cmovc r9, r13
cmovc rdi, rdx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], rdi
cmovc r15, rbp
cmovc r11, r8
mov [ rbx + 0x10 ], r15
mov [ rbx + 0x0 ], r11
mov [ rbx + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6081
; seed 3166731883836883 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1128993 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=150, initial num_batches=31): 76450 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06771521169750389
; number reverted permutation / tried permutation: 68588 / 90007 =76.203%
; number reverted decision / tried decision: 59549 / 89992 =66.171%
; validated in 1.689s
