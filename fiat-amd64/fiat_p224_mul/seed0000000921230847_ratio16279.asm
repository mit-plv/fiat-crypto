SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 192
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r11
mov r11, 0xffffffffffffffff 
mov rdx, r10
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, r11
mov rbp, 0xffffffff 
xchg rdx, r10
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
mov [ rsp - 0x60 ], r14
mov r14, 0xffffffff00000000 
mov [ rsp - 0x58 ], r15
mulx rbp, r15, r14
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, r11
adcx rdx, r10
adcx r15, r9
setc dl
clc
adcx r14, rbp
adcx r12, rdi
mov r10b, dl
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r13, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rdi, [ rax + 0x8 ]
clc
adcx rdi, rbp
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rdi
mulx rdi, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r12
mulx r12, r13, [ rsi + 0x8 ]
adcx rbp, r11
adcx r13, rdi
seto dl
mov r11, -0x2 
inc r11
adox r9, r15
mov r15b, dl
mov rdx, [ rax + 0x0 ]
mulx r11, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], rbp
mulx rbp, r13, [ rsi + 0x10 ]
seto dl
mov [ rsp - 0x20 ], rdi
mov rdi, -0x2 
inc rdi
adox r13, r11
mov r11b, dl
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
adox rdi, rbp
adox rcx, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, rbp, [ rax + 0x10 ]
mov rdx, 0x0 
adcx r12, rdx
adox r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], rcx
mulx rcx, r8, [ rax + 0x18 ]
add r15b, 0xFF
adcx rbx, rbp
adcx r8, r13
adc rcx, 0x0
mov rdx, 0xffffffffffffffff 
mulx rbp, r15, r9
add r10b, 0x7F
adox rbx, r14
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, [ rax + 0x8 ]
adox r8, [ rsp - 0x38 ]
mov rdx, 0xffffffff00000000 
mulx r13, r14, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r12
mulx r12, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r8
mulx r8, rdi, [ rsi + 0x18 ]
adcx rbp, r12
adcx rdi, r10
mov rdx, [ rsi + 0x18 ]
mulx r12, r10, [ rax + 0x18 ]
adox rcx, [ rsp - 0x40 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], rdi
mov [ rsp + 0x28 ], rbp
mulx rbp, rdi, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x30 ], rcx
mov [ rsp + 0x38 ], r14
mulx r14, rcx, r15
adcx r10, r8
seto r8b
mov rdx, -0x2 
inc rdx
adox rcx, r13
adox rdi, r14
mov r13, 0x0 
adcx r12, r13
adox rbp, r13
add r11b, 0x7F
adox rbx, [ rsp - 0x48 ]
adcx r15, r9
adcx rbx, [ rsp + 0x38 ]
setc r15b
clc
adcx rbx, [ rsp - 0x20 ]
mov r9, [ rsp + 0x18 ]
adox r9, [ rsp - 0x28 ]
mov r11, [ rsp + 0x30 ]
adox r11, [ rsp - 0x30 ]
movzx r8, r8b
movzx r14, r8b
adox r14, [ rsp + 0x8 ]
seto r8b
dec r13
movzx r15, r15b
adox r15, r13
adox r9, rcx
adox rdi, r11
adcx r9, [ rsp - 0x18 ]
adox rbp, r14
adcx rdi, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx r15, rcx, rbx
movzx r15, r8b
mov r11, 0x0 
adox r15, r11
mulx r14, r8, rcx
mov r13, rcx
mov rdx, -0x3 
inc rdx
adox r13, rbx
mov r13, 0xffffffff00000000 
mov rdx, rcx
mulx rbx, rcx, r13
adox rcx, r9
adcx r15, [ rsp - 0x10 ]
setc r9b
clc
adcx r8, rbx
adox r8, rdi
mov rdi, 0xffffffff 
mulx r11, rbx, rdi
adcx rbx, r14
mov rdx, 0x0 
adcx r11, rdx
adox rbx, rbp
clc
adcx rcx, [ rsp + 0x10 ]
adcx r8, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x20 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r14, rbp, rcx
adox r11, r15
mov rdx, rbp
mulx r14, rbp, r13
adcx r10, r11
movzx r15, r9b
mov r11, 0x0 
adox r15, r11
adcx r12, r15
mov r9, rdx
mov r15, -0x3 
inc r15
adox r9, rcx
mov r9, 0xffffffffffffffff 
mulx r11, rcx, r9
setc r15b
clc
adcx rcx, r14
adox rbp, r8
mulx r14, r8, rdi
adcx r8, r11
adox rcx, rbx
mov rbx, 0x0 
adcx r14, rbx
adox r8, r10
adox r14, r12
movzx rdx, r15b
adox rdx, rbx
mov r10, rbp
sub r10, 0x00000001
mov r15, rcx
sbb r15, r13
mov r12, r8
sbb r12, r9
mov r11, r14
sbb r11, rdi
sbb rdx, 0x00000000
cmovc r10, rbp
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r10
cmovc r15, rcx
mov [ rdx + 0x8 ], r15
cmovc r11, r14
cmovc r12, r8
mov [ rdx + 0x10 ], r12
mov [ rdx + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6279
; seed 1477231612506862 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1084978 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 78859 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07268257973894401
; number reverted permutation / tried permutation: 74368 / 90287 =82.368%
; number reverted decision / tried decision: 64513 / 89712 =71.911%
; validated in 2.024s
