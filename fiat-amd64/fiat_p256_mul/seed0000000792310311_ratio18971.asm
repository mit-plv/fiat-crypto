SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 136
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
add r10, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rcx
mov [ rsp - 0x60 ], r14
mov r14, -0x2 
inc r14
adox r9, r13
mov r13, 0x0 
adox rbx, r13
mov [ rsp - 0x58 ], r15
mov r15, -0x3 
inc r15
adox r12, rcx
mov rdx, [ rax + 0x10 ]
mulx r13, r12, [ rsi + 0x0 ]
adox r9, r10
adcx r12, r11
mov rdx, [ rax + 0x18 ]
mulx r10, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, r15, [ rax + 0x0 ]
adcx r11, r13
adox rbx, r12
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, r13, [ rax + 0x10 ]
clc
adcx r8, r14
adcx r13, rbp
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x8 ]
adcx rbp, r12
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x50 ], rdi
mulx rdi, r12, rcx
mov rcx, 0x0 
adcx r14, rcx
clc
adcx r15, r9
adcx r8, rbx
adox r12, r11
adox rdi, r10
mulx r11, r9, r15
adcx r13, r12
mov rdx, [ rsi + 0x18 ]
mulx r10, rbx, [ rax + 0x8 ]
adcx rbp, rdi
mov rdx, [ rsi + 0x18 ]
mulx rdi, r12, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r12
mulx r12, rcx, [ rax + 0x10 ]
seto dl
mov [ rsp - 0x40 ], r11
mov r11, -0x2 
inc r11
adox rbx, rdi
adox rcx, r10
mov r10b, dl
mov rdx, [ rax + 0x18 ]
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
adox rdi, r12
movzx rdx, r10b
adcx rdx, r14
setc r14b
clc
adcx r9, rbx
mov r10, rdx
mov rdx, [ rax + 0x10 ]
mulx rbx, r12, [ rsi + 0x10 ]
adcx r12, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rbp, [ rsi + 0x10 ]
adcx rbp, rbx
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], rbp
mulx rbp, rbx, r15
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x8 ], rdi
mov byte [ rsp + 0x0 ], r14b
mulx r14, rdi, r15
clc
adcx rbx, r14
mov r14, 0x0 
adcx rbp, r14
adox r11, r14
add rdi, r15
adcx rbx, r8
adcx rbp, r13
mov rdi, -0x3 
inc rdi
adox rcx, rbx
mulx r8, r15, rcx
mov r13, [ rsp - 0x28 ]
adcx r13, [ rsp - 0x20 ]
adox r9, rbp
adcx r10, [ rsp - 0x40 ]
adox r12, r13
movzx rbx, byte [ rsp + 0x0 ]
adcx rbx, r14
mov rbp, 0xffffffff 
mov rdx, rcx
mulx r13, rcx, rbp
clc
adcx rcx, r8
adcx r13, r14
adox r10, [ rsp - 0x10 ]
clc
adcx r15, rdx
adcx rcx, r9
adox rbx, [ rsp - 0x8 ]
adcx r13, r12
seto r15b
mov r8, -0x3 
inc r8
adox rcx, [ rsp - 0x48 ]
adox r13, [ rsp - 0x30 ]
mov r8, 0xffffffff00000001 
mulx r12, r9, r8
adcx r9, r10
adox r9, [ rsp - 0x38 ]
adcx r12, rbx
adox r12, [ rsp - 0x18 ]
movzx rdx, r15b
adcx rdx, r14
adox r11, rdx
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r15, r10, rcx
clc
adcx r10, rcx
mov rdx, rcx
mulx rcx, r10, rbp
seto bl
mov rdi, -0x3 
inc rdi
adox r10, r15
adcx r10, r13
adox rcx, r14
adcx rcx, r9
mulx r9, r13, r8
adcx r13, r12
adcx r9, r11
movzx rdx, bl
adc rdx, 0x0
mov r12, r10
mov rbx, 0xffffffffffffffff 
sub r12, rbx
mov r11, rcx
sbb r11, rbp
mov r15, r13
sbb r15, 0x00000000
mov r14, r9
sbb r14, r8
sbb rdx, 0x00000000
cmovc r11, rcx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], r11
cmovc r15, r13
mov [ rdx + 0x10 ], r15
cmovc r12, r10
cmovc r14, r9
mov [ rdx + 0x18 ], r14
mov [ rdx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.8971
; seed 1839242170919226 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 883261 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 72195 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0817368818503251
; number reverted permutation / tried permutation: 76146 / 90133 =84.482%
; number reverted decision / tried decision: 60674 / 89866 =67.516%
; validated in 1.218s
