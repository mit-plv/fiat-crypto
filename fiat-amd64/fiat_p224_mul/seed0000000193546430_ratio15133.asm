SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
xor rdx, rdx
adox r13, r12
mov r12, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp - 0x58 ], r15
mulx r15, rbp, r12
adox r10, r14
adox r9, r11
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x50 ], rdi
mulx rdi, r12, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r11
mulx r11, r14, rbp
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, rbp
adcx r14, rdi
adcx r8, r11
mov rdi, 0x0 
adox rbx, rdi
adc rcx, 0x0
test al, al
adox rbp, r15
adox r12, r13
adox r14, r10
adox r8, r9
mov rdx, [ rax + 0x0 ]
mulx r15, rbp, [ rsi + 0x8 ]
adcx r15, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, r13, [ rax + 0x10 ]
adox rcx, rbx
setc dl
clc
adcx rbp, r12
adcx r15, r14
seto r9b
dec rdi
movzx rdx, dl
adox rdx, rdi
adox r13, [ rsp - 0x38 ]
mov rdx, [ rax + 0x18 ]
mulx rbx, r11, [ rsi + 0x8 ]
adox r11, r10
adcx r13, r8
mov rdx, 0xffffffffffffffff 
mulx r14, r12, rbp
adcx r11, rcx
mov r14, 0xffffffff00000000 
mov rdx, r12
mulx r8, r12, r14
mov r10, rdx
setc cl
clc
adcx r10, rbp
mov r10, 0xffffffffffffffff 
mulx rdi, rbp, r10
adcx r12, r15
setc r15b
clc
adcx rbp, r8
mov r8, 0xffffffff 
mulx r10, r14, r8
mov rdx, 0x0 
adox rbx, rdx
dec rdx
movzx r9, r9b
movzx rcx, cl
adox rcx, rdx
adox rbx, r9
adcx r14, rdi
setc r9b
clc
movzx r15, r15b
adcx r15, rdx
adcx r13, rbp
adcx r14, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rdi, [ rsi + 0x10 ]
seto dl
mov rbp, -0x2 
inc rbp
adox rcx, r15
movzx r15, r9b
lea r15, [ r15 + r10 ]
adcx r15, rbx
movzx r10, dl
mov rbx, 0x0 
adcx r10, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rbp, [ rsi + 0x10 ]
adox r9, r11
adox rbp, rbx
mov rdx, 0x0 
adox r8, rdx
add rdi, r12
adcx rcx, r13
mov r12, 0xffffffffffffffff 
mov rdx, rdi
mulx r13, rdi, r12
adcx r9, r14
adcx rbp, r15
xchg rdx, r12
mulx r14, r13, rdi
mov r11, rdi
mov r15, -0x2 
inc r15
adox r11, r12
adcx r8, r10
mov r11, 0xffffffff00000000 
mov rdx, rdi
mulx r10, rdi, r11
adox rdi, rcx
setc bl
clc
adcx r13, r10
mov r12, 0xffffffff 
mulx r10, rcx, r12
adcx rcx, r14
mov rdx, 0x0 
adcx r10, rdx
adox r13, r9
adox rcx, rbp
adox r10, r8
movzx r9, bl
adox r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, [ rax + 0x0 ]
test al, al
adox rbp, rdi
mov rdx, [ rsi + 0x18 ]
mulx r8, rbx, [ rax + 0x10 ]
adcx r14, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, rdi, [ rax + 0x18 ]
adox r14, r13
adox rbx, rcx
adcx rdi, r8
mov rdx, 0xffffffffffffffff 
mulx rcx, r13, rbp
mov rcx, 0x0 
adcx r15, rcx
adox rdi, r10
mulx r8, r10, r13
adox r15, r9
mov rdx, r11
mulx r9, r11, r13
clc
adcx r10, r9
mov rdx, r12
mulx r9, r12, r13
adcx r12, r8
adcx r9, rcx
clc
adcx r13, rbp
adcx r11, r14
adcx r10, rbx
adcx r12, rdi
adcx r9, r15
setc r13b
seto bpl
mov r14, r11
sub r14, 0x00000001
mov rbx, r10
mov rdi, 0xffffffff00000000 
sbb rbx, rdi
mov r8, r12
mov r15, 0xffffffffffffffff 
sbb r8, r15
movzx rcx, r13b
movzx rbp, bpl
lea rcx, [ rcx + rbp ]
mov rbp, r9
sbb rbp, rdx
sbb rcx, 0x00000000
cmovc rbx, r10
cmovc rbp, r9
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], rbp
cmovc r8, r12
cmovc r14, r11
mov [ rcx + 0x0 ], r14
mov [ rcx + 0x8 ], rbx
mov [ rcx + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5133
; seed 2379634026753201 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1384123 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=114, initial num_batches=31): 86353 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06238824150743828
; number reverted permutation / tried permutation: 64343 / 89770 =71.675%
; number reverted decision / tried decision: 55998 / 90229 =62.062%
; validated in 3.683s
