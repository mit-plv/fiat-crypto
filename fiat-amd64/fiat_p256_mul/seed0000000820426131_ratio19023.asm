SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 160
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
xor rdx, rdx
adox r13, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rcx
mulx rcx, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r12
mulx r12, rcx, [ rsi + 0x0 ]
adox rcx, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, r14, [ rax + 0x10 ]
adcx r9, r8
adcx r14, rbx
adox r10, r12
mov rdx, [ rax + 0x18 ]
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r11, rdx
adcx r8, rcx
mov r12, 0xffffffff 
mov rdx, r12
mulx rcx, r12, rbp
adc rbx, 0x0
add r12, rdi
adc rcx, 0x0
xor rdi, rdi
adox r15, rbp
adox r12, r13
adox rcx, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x48 ]
adcx r9, rcx
mov r15, 0xffffffff00000001 
mov rdx, r15
mulx r13, r15, rbp
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ rax + 0x8 ]
adox r15, r10
adox r13, r11
adcx r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx rdi, r15, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r10
mulx r10, r14, [ rsi + 0x10 ]
seto dl
mov [ rsp - 0x18 ], r9
mov r9, -0x2 
inc r9
adox rbp, r11
adox r14, rcx
mov cl, dl
mov rdx, [ rax + 0x18 ]
mulx r9, r11, [ rsi + 0x10 ]
adox r11, r10
adcx r8, r13
mov rdx, 0xffffffff 
mulx r10, r13, r12
movzx rdx, cl
adcx rdx, rbx
setc bl
clc
adcx r13, rdi
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r11
mulx r11, rdi, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r14
mulx r14, rdi, [ rax + 0x10 ]
clc
adcx r11, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x40 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adcx rdi, r14
adc r11, 0x0
add r15, r12
adcx r13, [ rsp - 0x18 ]
mov rdx, -0x2 
inc rdx
adox r13, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
mov r15, 0xffffffff00000001 
mov rdx, r15
mulx r14, r15, r12
mov r12, 0xffffffff 
mov rdx, r13
mov [ rsp + 0x18 ], r11
mulx r11, r13, r12
adox rbp, r10
adcx r15, r8
adcx r14, rcx
movzx r8, bl
mov rcx, 0x0 
adcx r8, rcx
adox r15, [ rsp + 0x0 ]
mov rbx, 0xffffffffffffffff 
mulx rcx, r10, rbx
adox r14, [ rsp - 0x10 ]
clc
adcx r13, rcx
adox r9, r8
mov r8, 0x0 
adcx r11, r8
clc
adcx r10, rdx
adcx r13, rbp
adcx r11, r15
mov r10, 0xffffffff00000001 
mulx r15, rbp, r10
seto dl
mov rcx, -0x3 
inc rcx
adox r13, [ rsp - 0x8 ]
adox r11, [ rsp + 0x10 ]
adcx rbp, r14
adcx r15, r9
movzx r14, dl
adcx r14, r8
adox rbp, [ rsp + 0x8 ]
adox rdi, r15
adox r14, [ rsp + 0x18 ]
mov rdx, r13
mulx r9, r13, rbx
mulx r8, r15, r12
clc
adcx r15, r9
mov r9, 0x0 
adcx r8, r9
clc
adcx r13, rdx
adcx r15, r11
adcx r8, rbp
mulx r11, r13, r10
adcx r13, rdi
adcx r11, r14
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbp, r15
sub rbp, rbx
mov rdi, r8
sbb rdi, r12
mov r14, r13
sbb r14, 0x00000000
mov r9, r11
sbb r9, r10
movzx rcx, dl
sbb rcx, 0x00000000
cmovc rbp, r15
cmovc rdi, r8
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], rdi
cmovc r9, r11
cmovc r14, r13
mov [ rcx + 0x18 ], r9
mov [ rcx + 0x10 ], r14
mov [ rcx + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.9023
; seed 3985269749417609 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 849902 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=216, initial num_batches=31): 72978 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08586637047565485
; number reverted permutation / tried permutation: 75379 / 89997 =83.757%
; number reverted decision / tried decision: 61342 / 90002 =68.156%
; validated in 1.07s
