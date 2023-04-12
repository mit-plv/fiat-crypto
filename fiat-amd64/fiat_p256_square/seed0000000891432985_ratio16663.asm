SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0xffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, rax
xor rdx, rdx
adox rdi, r13
adcx r12, rax
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x40 ], r11
mov r11, -0x2 
inc r11
adox r12, r10
movzx r10, dl
lea r10, [ r10 + rcx ]
adcx rdi, r12
adox rbx, r13
mov rdx, [ rsi + 0x8 ]
mulx r13, rcx, [ rsi + 0x18 ]
adox r8, rbp
adcx r10, rbx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rbx, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rbx, rdi
mov rdi, 0xffffffff00000001 
mov rdx, rdi
mov [ rsp - 0x38 ], r13
mulx r13, rdi, rax
adcx rdi, r8
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx r8, rax, rbx
adcx r13, r9
setc r9b
clc
adcx r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r11, [ rsi + 0x10 ]
adcx r11, r15
adox r14, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rsi + 0x8 ]
adcx r15, rcx
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r12
mulx r12, rcx, rbx
mov rdx, 0x0 
adcx r10, rdx
clc
adcx rcx, r8
adcx r12, rdx
clc
adcx rax, rbx
adcx rcx, r14
adox r11, rdi
mov rax, 0xffffffff00000001 
mov rdx, rax
mulx rdi, rax, rbx
adox r15, r13
adcx r12, r11
adcx rax, r15
movzx rbx, r9b
adox rbx, r10
adcx rdi, rbx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r13, [ rsi + 0x10 ]
seto dl
mov r10, -0x2 
inc r10
adox rcx, [ rsp - 0x40 ]
movzx r11, dl
mov r15, 0x0 
adcx r11, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], rbp
mulx rbp, r10, rcx
clc
adcx rbx, [ rsp - 0x48 ]
adcx r8, r15
adox rbx, r12
adcx r13, r9
mov r12, 0x0 
adcx r14, r12
mov r9, 0xffffffffffffffff 
mov rdx, rcx
mulx r15, rcx, r9
adox r8, rax
adox r13, rdi
adox r14, r11
clc
adcx r10, r15
setc al
clc
adcx rcx, rdx
adcx r10, rbx
movzx rcx, al
lea rcx, [ rcx + rbp ]
adcx rcx, r8
mov rdi, 0xffffffff00000001 
mulx rbp, r11, rdi
seto dl
mov rbx, -0x3 
inc rbx
adox r10, [ rsp - 0x20 ]
adcx r11, r13
adcx rbp, r14
movzx r15, dl
adcx r15, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsp - 0x30 ]
clc
adcx rdx, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x38 ]
adox rdx, rcx
mov r14, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rax, rdx
adcx rax, r13
adox r8, r11
adcx rcx, r12
adox rax, rbp
mov rdx, r9
mulx r11, r9, r10
mov rbp, 0xffffffff 
mov rdx, r10
mulx r13, r10, rbp
clc
adcx r10, r11
adcx r13, r12
mulx r12, r11, rdi
clc
adcx r9, rdx
adcx r10, r14
adcx r13, r8
adcx r11, rax
adox rcx, r15
adcx r12, rcx
seto r9b
adc r9b, 0x0
movzx r9, r9b
mov rdx, r10
mov r15, 0xffffffffffffffff 
sub rdx, r15
mov r14, r13
sbb r14, rbp
mov r8, r11
sbb r8, 0x00000000
mov rax, r12
sbb rax, rdi
movzx rcx, r9b
sbb rcx, 0x00000000
cmovc r14, r13
cmovc r8, r11
cmovc rax, r12
cmovc rdx, r10
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], rax
mov [ rcx + 0x10 ], r8
mov [ rcx + 0x8 ], r14
mov [ rcx + 0x0 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6663
; seed 3854606073735993 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1030484 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=150, initial num_batches=31): 72812 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07065805970786543
; number reverted permutation / tried permutation: 71650 / 89810 =79.780%
; number reverted decision / tried decision: 59834 / 90189 =66.343%
; validated in 1.72s
