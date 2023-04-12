SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox r11, r10
adox r8, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, rdx
adcx rbx, rcx
adcx rdi, rbp
adcx r14, r8
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r11
mulx r11, r8, rdx
adox rbp, r9
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], rbp
mulx rbp, r9, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], r14
mulx r14, rax, r8
mov rdx, 0x0 
adcx r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
clc
adcx r15, r11
mov rdx, 0x0 
adox rcx, rdx
mov r11, -0x3 
inc r11
adox r9, r14
seto r14b
mov r11, -0x3 
inc r11
adox rax, r8
adox r9, r15
movzx rax, r14b
lea rax, [ rax + rbp ]
mov rdx, [ rsi + 0x10 ]
mulx r15, rbp, [ rsi + 0x0 ]
adcx rbp, rdi
mov rdx, [ rsi + 0x0 ]
mulx r14, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, r11, rdx
adcx r12, r15
setc dl
clc
adcx r11, r14
movzx r15, dl
lea r15, [ r15 + r13 ]
adox rax, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
adcx r13, rcx
adcx r14, rbp
mov rdx, 0xffffffff00000001 
mulx rbp, rcx, r8
adox rcx, r12
mov r8, 0x0 
adcx rbx, r8
clc
adcx rdi, r9
adox rbp, r15
adcx r11, rax
adcx r13, rcx
mov r9, 0xffffffff 
mov rdx, r9
mulx r12, r9, rdi
adcx r14, rbp
setc r15b
movzx r15, r15b
adox r15, rbx
mov rax, 0xffffffffffffffff 
mov rdx, rdi
mulx rcx, rdi, rax
clc
adcx r9, rcx
adcx r12, r8
clc
adcx rdi, rdx
adcx r9, r11
adcx r12, r13
seto dil
mov rbx, -0x3 
inc rbx
adox r10, r9
adox r12, [ rsp - 0x8 ]
mov rbp, 0xffffffff00000001 
mulx r13, r11, rbp
adcx r11, r14
adcx r13, r15
mov rdx, r10
mulx r14, r10, rax
movzx r15, dil
adcx r15, r8
mov rdi, 0xffffffff 
mulx r9, rcx, rdi
clc
adcx rcx, r14
adox r11, [ rsp - 0x18 ]
adox r13, [ rsp - 0x28 ]
adox r15, [ rsp - 0x20 ]
seto r14b
mov rbx, -0x3 
inc rbx
adox r10, rdx
adcx r9, r8
adox rcx, r12
adox r9, r11
clc
adcx rcx, [ rsp - 0x30 ]
mulx r12, r10, rbp
adox r10, r13
adox r12, r15
mov rdx, rcx
mulx r11, rcx, rax
adcx r9, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
movzx r13, r14b
adox r13, r8
mulx r15, r14, rdi
adcx r12, [ rsp - 0x38 ]
mov rbx, -0x3 
inc rbx
adox r14, r11
adcx r13, [ rsp - 0x10 ]
setc r11b
clc
adcx rcx, rdx
adcx r14, r9
mulx r9, rcx, rbp
adox r15, r8
adcx r15, r10
adcx rcx, r12
adcx r9, r13
movzx rdx, r11b
adc rdx, 0x0
mov r10, r14
sub r10, rax
mov r12, r15
sbb r12, rdi
mov r11, rcx
sbb r11, 0x00000000
mov r13, r9
sbb r13, rbp
sbb rdx, 0x00000000
cmovc r13, r9
cmovc r12, r15
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r13
cmovc r11, rcx
mov [ rdx + 0x8 ], r12
cmovc r10, r14
mov [ rdx + 0x10 ], r11
mov [ rdx + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5933
; seed 4162672366920002 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1649386 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=228, initial num_batches=31): 137923 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08362081404837922
; number reverted permutation / tried permutation: 67160 / 90050 =74.581%
; number reverted decision / tried decision: 56562 / 89949 =62.882%
; validated in 2.468s
