SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 152
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r10
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx r9, r8, rcx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r15
mulx r15, r14, rcx
add r14, r9
mov r9, rcx
mov rdx, -0x2 
inc rdx
adox r9, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], rbp
mulx rbp, r9, rcx
adcx r9, r15
mov rcx, 0x0 
adcx rbp, rcx
mov rdx, [ rax + 0x8 ]
mulx rcx, r15, [ rsi + 0x10 ]
clc
adcx r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r15
mulx r15, r10, [ rax + 0x10 ]
adcx r10, rcx
adcx r12, r15
mov rdx, 0x0 
adcx r13, rdx
mov rdx, [ rax + 0x10 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r12
mulx r12, r13, [ rsi + 0x0 ]
clc
adcx rdi, r11
adox r8, rdi
adcx rcx, rbx
adox r14, rcx
adcx r13, r15
mov rdx, 0x0 
adcx r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rax + 0x8 ]
adox r9, r13
mov rdx, [ rsi + 0x18 ]
mulx rdi, r15, [ rax + 0x10 ]
clc
adcx r11, [ rsp - 0x28 ]
adox rbp, r12
mov rdx, [ rax + 0x10 ]
mulx r13, rcx, [ rsi + 0x8 ]
adcx r15, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r12, [ rax + 0x18 ]
adcx r12, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r12
mulx r12, rdi, [ rax + 0x8 ]
seto dl
mov [ rsp + 0x0 ], r15
mov r15, -0x2 
inc r15
adox rdi, [ rsp - 0x38 ]
mov r15b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r10
mulx r10, r11, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r8, [ rsp - 0x40 ]
adcx rdi, r14
adox rcx, r12
adox r11, r13
adcx rcx, r9
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r9, r14, r8
mulx r13, r9, r14
mov r12, 0x0 
adox r10, r12
adcx r11, rbp
mov rbp, 0xffffffff00000000 
mov rdx, r14
mulx r12, r14, rbp
movzx rbp, r15b
adcx rbp, r10
mov r15, -0x2 
inc r15
adox r9, r12
mov r10, 0xffffffff 
mulx r15, r12, r10
adox r12, r13
mov r13, 0x0 
adox r15, r13
mov r10, -0x3 
inc r10
adox rdx, r8
adox r14, rdi
setc dl
clc
adcx r14, [ rsp - 0x30 ]
adox r9, rcx
adox r12, r11
adcx r9, [ rsp - 0x20 ]
adcx r12, [ rsp + 0x10 ]
adox r15, rbp
movzx r8, dl
adox r8, r13
mov rdi, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, rdi
adcx r15, [ rsp - 0x10 ]
mov rcx, r14
mov r11, -0x3 
inc r11
adox rcx, rdx
adcx r8, [ rsp - 0x18 ]
mov r11, 0xffffffff00000000 
mov rdx, r14
mulx r14, rcx, r11
adox rcx, r9
mulx r9, rbp, rdi
setc r10b
clc
adcx rbp, r14
adox rbp, r12
mov r12, 0xffffffff 
mulx r13, r14, r12
adcx r14, r9
mov rdx, 0x0 
adcx r13, rdx
adox r14, r15
adox r13, r8
movzx r15, r10b
adox r15, rdx
add rcx, [ rsp - 0x48 ]
adcx rbp, [ rsp + 0x8 ]
mov rdx, rcx
mulx r10, rcx, rdi
mov r10, rcx
mov r8, -0x2 
inc r8
adox r10, rdx
adcx r14, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
adcx rbx, r15
mov rdx, rcx
mulx rcx, r10, r11
adox r10, rbp
mulx r15, r9, r12
mulx r8, rbp, rdi
setc dl
clc
adcx rbp, rcx
adox rbp, r14
adcx r9, r8
adox r9, r13
mov r14, 0x0 
adcx r15, r14
adox r15, rbx
movzx r13, dl
adox r13, r14
mov rdx, r10
sub rdx, 0x00000001
mov rbx, rbp
sbb rbx, r11
mov rcx, r9
sbb rcx, rdi
mov r8, r15
sbb r8, r12
sbb r13, 0x00000000
cmovc rdx, r10
cmovc rbx, rbp
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], rbx
cmovc r8, r15
mov [ r13 + 0x18 ], r8
cmovc rcx, r9
mov [ r13 + 0x0 ], rdx
mov [ r13 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6839
; seed 2451274458649578 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 917889 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=223, initial num_batches=31): 74803 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08149460337796836
; number reverted permutation / tried permutation: 74788 / 89604 =83.465%
; number reverted decision / tried decision: 63235 / 90395 =69.954%
; validated in 1.77s
