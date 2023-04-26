SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 144
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r8, rax
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r8
add r9, rdi
mov rdi, 0xffffffff 
mov rdx, r8
mov [ rsp - 0x48 ], rbp
mulx rbp, r8, rdi
adcx r8, rbx
adc rbp, 0x0
add r11, r10
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rbp
mulx rbp, r13, [ rsi + 0x18 ]
adcx rbx, rcx
adcx r13, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rcx, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r10, rax
mov r10, 0x0 
adcx rbp, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, rdx
clc
adcx rcx, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r12, [ rsi + 0x18 ]
adcx r12, rdi
adcx rax, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r10, rdx
clc
adcx rdi, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r10
mulx r10, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rax
mov [ rsp - 0x18 ], r12
mulx r12, rax, [ rsi + 0x10 ]
adcx r14, rcx
adcx rax, r10
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rax
mulx rax, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], rdi
mulx rdi, r14, [ rsi + 0x10 ]
adox r15, r11
clc
adcx r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, [ rsi + 0x18 ]
adox r9, rbx
adcx r14, rax
adcx r11, rdi
mov rdx, 0x0 
adcx r10, rdx
adox r8, r13
adox rbp, [ rsp - 0x38 ]
clc
adcx rcx, r15
adcx r12, r9
adcx r14, r8
adcx r11, rbp
mov rbx, 0xffffffffffffffff 
mov rdx, rcx
mulx r13, rcx, rbx
mov r13, rcx
seto al
mov rdi, -0x2 
inc rdi
adox r13, rdx
movzx r13, al
adcx r13, r10
mov r15, 0xffffffff00000000 
mov rdx, rcx
mulx r9, rcx, r15
adox rcx, r12
mulx r8, r10, rbx
setc al
clc
adcx r10, r9
adox r10, r14
mov rbp, 0xffffffff 
mulx r14, r12, rbp
adcx r12, r8
mov rdx, 0x0 
adcx r14, rdx
clc
adcx rcx, [ rsp - 0x40 ]
adcx r10, [ rsp + 0x8 ]
adox r12, r11
adox r14, r13
adcx r12, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
movzx r11, al
adox r11, rdx
mov rdx, rbx
mulx rax, rbx, rcx
mov rdx, rbx
mulx rbx, rax, r15
adcx r11, [ rsp - 0x10 ]
mov r13, rdx
inc rdi
adox r13, rcx
adox rax, r10
mov r13, 0xffffffffffffffff 
mulx r8, r9, r13
setc cl
clc
adcx rax, [ rsp - 0x48 ]
setc r10b
clc
adcx r9, rbx
adox r9, r12
mulx rbx, r12, rbp
adcx r12, r8
adox r12, r14
adcx rbx, rdi
adox rbx, r11
movzx r14, cl
adox r14, rdi
mov rdx, r13
mulx rcx, r13, rax
mov rdx, r15
mulx r15, rcx, r13
add r10b, 0x7F
adox r9, [ rsp - 0x30 ]
adox r12, [ rsp - 0x18 ]
adox rbx, [ rsp - 0x20 ]
mov r11, 0xffffffffffffffff 
mov rdx, r13
mulx r8, r13, r11
mov r10, rdx
adcx r10, rax
adcx rcx, r9
adox r14, [ rsp - 0x28 ]
seto r10b
mov rax, -0x3 
inc rax
adox r13, r15
adcx r13, r12
mulx r9, r15, rbp
adox r15, r8
adox r9, rdi
adcx r15, rbx
adcx r9, r14
movzx rdx, r10b
adc rdx, 0x0
mov r12, rcx
sub r12, 0x00000001
mov rbx, r13
mov r8, 0xffffffff00000000 
sbb rbx, r8
mov r10, r15
sbb r10, r11
mov r14, r9
sbb r14, rbp
sbb rdx, 0x00000000
cmovc r10, r15
cmovc r14, r9
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r10
mov [ rdx + 0x18 ], r14
cmovc rbx, r13
mov [ rdx + 0x8 ], rbx
cmovc r12, rcx
mov [ rdx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6025
; seed 3365113051678905 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 975748 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=202, initial num_batches=31): 77429 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07935348061179731
; number reverted permutation / tried permutation: 75396 / 89726 =84.029%
; number reverted decision / tried decision: 65266 / 90273 =72.298%
; validated in 1.78s
