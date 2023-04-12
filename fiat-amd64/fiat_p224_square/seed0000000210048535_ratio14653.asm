SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbx
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r15
mulx r15, rbp, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r10
mulx r10, rdi, r12
mov rdx, 0xffffffff 
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], r8
mulx r8, rax, r12
adcx r12, rbx
adcx rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx rbx, r12, [ rsi + 0x10 ]
adox r12, rcx
mov rdx, [ rsi + 0x0 ]
mulx r11, rcx, [ rsi + 0x18 ]
adox rcx, rbx
mov rdx, 0x0 
adox r11, rdx
mov rbx, -0x3 
inc rbx
adox r13, r10
adox rax, r14
adcx r13, r12
adox r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r14, [ rsi + 0x18 ]
adcx rax, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, [ rsi + 0x8 ]
inc rbx
adox r12, r10
adcx r8, r11
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, rdx
setc dl
clc
adcx r11, r9
adox rbp, rcx
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbx, rcx, rdx
adox rcx, r15
mov rdx, 0x0 
adox rbx, rdx
mov r15, -0x3 
inc r15
adox rdi, [ rsp - 0x28 ]
adcx r10, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbx
mulx rbx, r15, [ rsi + 0x8 ]
adcx r15, [ rsp - 0x38 ]
mov rdx, 0x0 
adcx rbx, rdx
adox r11, r13
adox r10, rax
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx rax, r13, rdi
adox r15, r8
movzx rax, r9b
adox rax, rbx
mov r9, 0xffffffff00000000 
mov rdx, r9
mulx r8, r9, r13
mov rbx, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp - 0x18 ], rcx
mulx rcx, r13, rbx
clc
adcx r13, r8
mov r8, 0xffffffff 
mov [ rsp - 0x10 ], rbp
mulx rbp, rbx, r8
adcx rbx, rcx
seto cl
mov r8, -0x2 
inc r8
adox rdx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rbp, rdx
adox r9, r11
adox r13, r10
adox rbx, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, rdx
adox rbp, rax
movzx rdx, cl
mov r15, 0x0 
adox rdx, r15
test al, al
adox rdi, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x48 ]
adcx rdi, r13
adox r11, r8
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rax, [ rsi + 0x18 ]
adox rax, r10
adox r8, r15
mov rdx, 0xffffffffffffffff 
mulx r10, r13, r9
adcx r11, rbx
adcx rax, rbp
mulx rbx, r10, r13
adcx r8, rcx
mov rbp, r13
mov rcx, -0x3 
inc rcx
adox rbp, r9
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx r9, rbp, r13
setc cl
clc
adcx r10, r9
adox rbp, rdi
adox r10, r11
mov rdi, 0xffffffff 
mov rdx, r13
mulx r11, r13, rdi
adcx r13, rbx
adox r13, rax
adcx r11, r15
adox r11, r8
clc
adcx r14, rbp
mov rdx, 0xffffffffffffffff 
mulx rbx, rax, r14
mulx r8, rbx, rax
adcx r12, r10
adcx r13, [ rsp - 0x10 ]
movzx r9, cl
adox r9, r15
adcx r11, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x20 ]
mov rcx, rax
mov rbp, -0x3 
inc rbp
adox rcx, r14
mov rcx, 0xffffffff00000000 
mov rdx, rax
mulx r10, rax, rcx
setc r14b
clc
adcx rbx, r10
adox rax, r12
mulx r10, r12, rdi
adcx r12, r8
adox rbx, r13
adcx r10, r15
adox r12, r11
adox r10, r9
movzx rdx, r14b
adox rdx, r15
mov r8, rax
sub r8, 0x00000001
mov r13, rbx
sbb r13, rcx
mov r11, r12
mov r14, 0xffffffffffffffff 
sbb r11, r14
mov r9, r10
sbb r9, rdi
sbb rdx, 0x00000000
cmovc r11, r12
cmovc r13, rbx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r11
cmovc r9, r10
cmovc r8, rax
mov [ rdx + 0x8 ], r13
mov [ rdx + 0x18 ], r9
mov [ rdx + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4653
; seed 4310326396586641 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2018334 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=106, initial num_batches=31): 129156 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06399139091944148
; number reverted permutation / tried permutation: 66460 / 89709 =74.084%
; number reverted decision / tried decision: 58043 / 90290 =64.285%
; validated in 3.707s
