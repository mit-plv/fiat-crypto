SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 224
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r9
mov r14, 0xffffffff00000000 
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, r14
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x8 ]
mov rdx, r14
add rdx, r9
mov rdx, -0x2 
inc rdx
adox rbp, rbx
adcx r13, rbp
setc r9b
clc
adcx rdi, r13
mov rdx, [ rsi + 0x10 ]
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp - 0x40 ], r9b
mulx r9, r13, [ rax + 0x10 ]
adox rcx, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], rbp
mulx rbp, rcx, [ rax + 0x8 ]
adox r12, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r12
mulx r12, r8, rdi
setc r12b
clc
adcx rcx, r11
mov r11, 0x0 
adox r9, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r8
mulx r8, r11, [ rsi + 0x8 ]
adcx r11, rbp
mov rdx, 0xffffffff 
mov [ rsp - 0x10 ], r9
mulx r9, rbp, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x8 ], r11
mov [ rsp + 0x0 ], rcx
mulx rcx, r11, r14
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x8 ], r12b
mulx r12, r14, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r11, r15
adcx r14, r8
mov rdx, [ rax + 0x0 ]
mulx r8, r15, [ rsi + 0x18 ]
adox rbp, rcx
mov rdx, 0x0 
adox r9, rdx
adc r12, 0x0
xor rcx, rcx
adox r10, r8
mov rdx, [ rax + 0x8 ]
mulx rcx, r8, [ rsi + 0x10 ]
adox r13, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x10 ], r13
mov [ rsp + 0x18 ], r10
mulx r10, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r12
mulx r12, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x30 ], r15
mov [ rsp + 0x38 ], r14
mulx r14, r15, [ rsi + 0x10 ]
adcx r8, r12
adcx rbx, rcx
adcx r15, [ rsp - 0x28 ]
mov rdx, 0x0 
adcx r14, rdx
movzx rcx, byte [ rsp - 0x40 ]
clc
mov r12, -0x1 
adcx rcx, r12
adcx r11, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
adox r10, rdx
adcx rbp, [ rsp - 0x20 ]
movzx rcx, byte [ rsp + 0x8 ]
inc r12
mov rdx, -0x1 
adox rcx, rdx
adox r11, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x8 ]
adcx r9, [ rsp - 0x10 ]
mov rcx, 0xffffffffffffffff 
mov rdx, [ rsp - 0x18 ]
mov [ rsp + 0x40 ], r10
mulx r10, r12, rcx
adox r9, [ rsp + 0x38 ]
seto cl
movzx rcx, cl
adcx rcx, [ rsp + 0x28 ]
mov [ rsp + 0x48 ], r13
mov r13, 0xffffffff00000000 
mov [ rsp + 0x50 ], r14
mov [ rsp + 0x58 ], r15
mulx r15, r14, r13
mov r13, -0x2 
inc r13
adox r12, r15
mov r15, rdx
setc r13b
clc
adcx r15, rdi
adcx r14, r11
mov r15, 0xffffffff 
mulx r11, rdi, r15
adox rdi, r10
mov rdx, 0x0 
adox r11, rdx
mov r10, -0x3 
inc r10
adox r14, [ rsp + 0x30 ]
adcx r12, rbp
adcx rdi, r9
adcx r11, rcx
adox r8, r12
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r9, rbp, r14
adox rbx, rdi
movzx r9, r13b
mov rcx, 0x0 
adcx r9, rcx
adox r11, [ rsp + 0x58 ]
adox r9, [ rsp + 0x50 ]
mulx r12, r13, rbp
mov rdi, 0xffffffff00000000 
mov rdx, rdi
mulx rcx, rdi, rbp
mov r10, rbp
clc
adcx r10, r14
adcx rdi, r8
seto r10b
mov r14, -0x2 
inc r14
adox r13, rcx
mov rdx, rbp
mulx r8, rbp, r15
adox rbp, r12
mov rdx, 0x0 
adox r8, rdx
adcx r13, rbx
adcx rbp, r11
adcx r8, r9
movzx rbx, r10b
adc rbx, 0x0
xor r11, r11
adox rdi, [ rsp + 0x20 ]
adox r13, [ rsp + 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r10, rdi
mov r9, 0xffffffff00000000 
mov rdx, r10
mulx r12, r10, r9
mov rcx, 0xffffffffffffffff 
mulx r14, r11, rcx
adox rbp, [ rsp + 0x10 ]
mov r9, rdx
adcx r9, rdi
adcx r10, r13
adox r8, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
seto r9b
mov rdi, -0x2 
inc rdi
adox r11, r12
mulx r12, r13, r15
adox r13, r14
adcx r11, rbp
mov rdx, 0x0 
adox r12, rdx
adcx r13, r8
adcx r12, rbx
movzx r14, r9b
adc r14, 0x0
mov rbp, r10
sub rbp, 0x00000001
mov r8, r11
mov r9, 0xffffffff00000000 
sbb r8, r9
mov rbx, r13
sbb rbx, rcx
mov rdx, r12
sbb rdx, r15
sbb r14, 0x00000000
cmovc rbx, r13
cmovc rbp, r10
cmovc rdx, r12
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rbp
cmovc r8, r11
mov [ r14 + 0x8 ], r8
mov [ r14 + 0x10 ], rbx
mov [ r14 + 0x18 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 224
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.6542
; seed 0376311632847508 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 944707 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=219, initial num_batches=31): 75561 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0799835292847412
; number reverted permutation / tried permutation: 73500 / 90328 =81.370%
; number reverted decision / tried decision: 62858 / 89671 =70.098%
; validated in 1.783s
