SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rcx
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
mov [ rsp - 0x58 ], r15
xor r15, r15
adox r13, r12
mov rdx, [ rax + 0x10 ]
mulx r15, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rax + 0x0 ]
mov rdx, 0x0 
adox r14, rdx
adcx r10, rbx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
adcx rbx, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r11, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r11, r8
adox r12, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r8, [ rsi + 0x8 ]
adcx r8, r9
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx rbp, rcx
mov rdx, [ rax + 0x18 ]
mulx r9, rbp, [ rsi + 0x0 ]
adox rbp, r15
adcx r13, r11
mov rdx, 0xffffffff00000001 
mulx r11, r15, rcx
adcx r14, r12
seto cl
mov r12, -0x2 
inc r12
adox rdi, r13
adox r10, r14
mov r13, 0xffffffff 
mov rdx, r13
mulx r14, r13, rdi
movzx r12, cl
lea r12, [ r12 + r9 ]
adcx r15, rbp
adox r15, [ rsp - 0x38 ]
mov r9, 0xffffffff00000001 
mov rdx, r9
mulx rcx, r9, rdi
adcx r11, r12
mov rbp, 0xffffffffffffffff 
mov rdx, rdi
mulx r12, rdi, rbp
setc bpl
clc
adcx r13, r12
mov r12, 0x0 
adcx r14, r12
clc
adcx rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, rdi, [ rax + 0x18 ]
adox r8, r11
adcx r13, r10
movzx rdx, bpl
adox rdx, rbx
adcx r14, r15
adcx r9, r8
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rax + 0x0 ]
seto dl
mov r8, -0x2 
inc r8
adox r10, r11
adcx rcx, rbx
adox r15, [ rsp - 0x40 ]
movzx rbx, dl
mov r11, 0x0 
adcx rbx, r11
clc
adcx rbp, r13
adcx r10, r14
mov r13, 0xffffffffffffffff 
mov rdx, rbp
mulx r14, rbp, r13
adox rdi, [ rsp - 0x48 ]
adox r12, r11
adcx r15, r9
adcx rdi, rcx
mov r9, 0xffffffff 
mulx r11, rcx, r9
adcx r12, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r8, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox rcx, r14
setc r14b
clc
adcx rbp, rbx
adcx rcx, r10
mov rbp, 0x0 
adox r11, rbp
mov r10, 0xffffffff00000001 
mov rdx, r10
mulx rbp, r10, rbx
adcx r11, r15
adcx r10, rdi
adcx rbp, r12
movzx rbx, r14b
adc rbx, 0x0
mov rdx, [ rax + 0x8 ]
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r12, r14, [ rsi + 0x18 ]
xor rdx, rdx
adox r14, rcx
adcx r15, r12
adcx r8, rdi
adox r15, r11
adox r8, r10
mov rdx, r14
mulx rcx, r14, r9
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r10, [ rax + 0x18 ]
adcx r10, r13
adox r10, rbp
mov rdx, 0xffffffffffffffff 
mulx rbp, r13, r11
setc r12b
clc
adcx r13, r11
movzx r13, r12b
lea r13, [ r13 + rdi ]
adox r13, rbx
seto bl
mov rdi, -0x2 
inc rdi
adox r14, rbp
adcx r14, r15
mov r15, 0x0 
adox rcx, r15
adcx rcx, r8
mov r8, 0xffffffff00000001 
mov rdx, r11
mulx r12, r11, r8
adcx r11, r10
adcx r12, r13
movzx rdx, bl
adc rdx, 0x0
mov r10, r14
mov rbp, 0xffffffffffffffff 
sub r10, rbp
mov rbx, rcx
sbb rbx, r9
mov r13, r11
sbb r13, 0x00000000
mov r15, r12
sbb r15, r8
sbb rdx, 0x00000000
cmovc r10, r14
cmovc rbx, rcx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], rbx
cmovc r15, r12
mov [ rdx + 0x18 ], r15
mov [ rdx + 0x0 ], r10
cmovc r13, r11
mov [ rdx + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7358
; seed 1708994731392075 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1107296 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=143, initial num_batches=31): 75717 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0683800898766003
; number reverted permutation / tried permutation: 68123 / 90031 =75.666%
; number reverted decision / tried decision: 58693 / 89968 =65.238%
; validated in 1.978s
