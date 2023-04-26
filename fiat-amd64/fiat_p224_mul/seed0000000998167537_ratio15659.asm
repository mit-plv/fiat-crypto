SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], r8
mulx r8, rbx, [ rax + 0x8 ]
test al, al
adox rbx, r11
adox r14, r8
mov rdx, r9
adcx rdx, r10
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
adox r10, r15
mov rdx, 0xffffffff00000000 
mulx r8, r15, r9
mov rdx, 0x0 
adox r11, rdx
adcx r15, rbx
mov rbx, 0xffffffff 
mov rdx, rbx
mov [ rsp - 0x30 ], rcx
mulx rcx, rbx, r9
mov r9, -0x2 
inc r9
adox rdi, r15
setc r15b
clc
adcx r12, r8
adcx rbx, r13
mov r13, 0x0 
adcx rcx, r13
clc
movzx r15, r15b
adcx r15, r9
adcx r14, r12
adcx rbx, r10
mov r10, 0xffffffffffffffff 
mov rdx, rdi
mulx r8, rdi, r10
adcx rcx, r11
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r11, [ rax + 0x8 ]
mov rdx, 0xffffffff 
mulx r13, r12, rdi
setc r9b
clc
adcx r11, rbp
adox r11, r14
mov rdx, [ rax + 0x10 ]
mulx r14, rbp, [ rsi + 0x8 ]
adcx rbp, r15
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rax + 0x18 ]
adcx r15, r14
adox rbp, rbx
mov rdx, 0x0 
adcx r10, rdx
adox r15, rcx
mov rbx, 0xffffffffffffffff 
mov rdx, rdi
mulx rcx, rdi, rbx
movzx r14, r9b
adox r14, r10
mov r9, 0xffffffff00000000 
mulx rbx, r10, r9
clc
adcx rdi, rbx
adcx r12, rcx
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r13, rdx
clc
adcx rcx, r8
adcx r10, r11
seto cl
mov r8, -0x3 
inc r8
adox rbx, r10
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r10, r11, rbx
adcx rdi, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r10, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov byte [ rsp - 0x28 ], cl
mulx rcx, r8, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r8
mulx r8, rcx, [ rax + 0x18 ]
adcx r12, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r12
mulx r12, r15, r11
adcx r13, r14
setc r14b
clc
adcx r10, r9
adox r10, rdi
adcx rbp, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov r9, 0x0 
adcx r8, r9
adox rbp, [ rsp - 0x10 ]
adox rcx, r13
movzx rdi, r14b
movzx r13, byte [ rsp - 0x28 ]
lea rdi, [ rdi + r13 ]
mov r13, 0xffffffff00000000 
mov rdx, r11
mulx r14, r11, r13
adox r8, rdi
clc
adcx rdx, rbx
seto dl
mov rbx, -0x3 
inc rbx
adox r15, r14
adcx r11, r10
mov r10b, dl
mov rdx, [ rax + 0x0 ]
mulx r14, rdi, [ rsi + 0x18 ]
setc dl
clc
adcx rdi, r11
adox r12, [ rsp - 0x18 ]
mov r11, [ rsp - 0x20 ]
adox r11, r9
mov r9b, dl
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, 0x0 
dec rdx
movzx r9, r9b
adox r9, rdx
adox rbp, r15
adox r12, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r15, rcx, rdi
mulx r9, r15, rcx
adox r11, r8
movzx r8, r10b
mov rdx, 0x0 
adox r8, rdx
mov r10, 0xffffffff00000000 
mov rdx, r10
mov [ rsp + 0x8 ], r9
mulx r9, r10, rcx
mov rdx, -0x2 
inc rdx
adox r13, r14
adox rbx, [ rsp - 0x40 ]
adcx r13, rbp
adcx rbx, r12
mov r14, [ rsp - 0x48 ]
adox r14, [ rsp + 0x0 ]
mov rbp, [ rsp - 0x8 ]
mov r12, 0x0 
adox rbp, r12
adcx r14, r11
adcx rbp, r8
mov r11, 0xffffffff 
mov rdx, rcx
mulx r8, rcx, r11
mov r11, -0x3 
inc r11
adox r15, r9
setc r9b
clc
adcx rdx, rdi
adox rcx, [ rsp + 0x8 ]
adcx r10, r13
adcx r15, rbx
adox r8, r12
adcx rcx, r14
adcx r8, rbp
movzx rdx, r9b
adc rdx, 0x0
mov rdi, r10
sub rdi, 0x00000001
mov r13, r15
mov rbx, 0xffffffff00000000 
sbb r13, rbx
mov r14, rcx
mov r9, 0xffffffffffffffff 
sbb r14, r9
mov rbp, r8
mov r12, 0xffffffff 
sbb rbp, r12
sbb rdx, 0x00000000
cmovc r13, r15
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x8 ], r13
cmovc rbp, r8
mov [ rdx + 0x18 ], rbp
cmovc r14, rcx
mov [ rdx + 0x10 ], r14
cmovc rdi, r10
mov [ rdx + 0x0 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5659
; seed 4421621865613962 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1249561 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 80449 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06438181089198526
; number reverted permutation / tried permutation: 67454 / 90172 =74.806%
; number reverted decision / tried decision: 59964 / 89827 =66.755%
; validated in 3.329s
