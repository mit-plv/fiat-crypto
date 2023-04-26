SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 160
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox rax, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r11
adcx r13, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, [ rsi + 0x0 ]
adcx rdi, r14
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x48 ], rax
mulx rax, r14, r15
adcx rbx, rcx
mov rcx, 0x0 
adcx rbp, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
clc
adcx r8, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r8
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
adcx rcx, r9
adox rbp, r10
mov rdx, [ rsi + 0x18 ]
mulx r9, r10, rdx
adox rbx, r8
adcx r10, r12
mov rdx, 0x0 
adox rdi, rdx
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx r12, r15, r8
adc r9, 0x0
add r15, rax
mov rax, 0xffffffff 
mov [ rsp - 0x10 ], r9
mulx r9, r8, rax
adcx r8, r12
mov r12, -0x2 
inc r12
adox rdx, r11
adox r14, r13
adox r15, [ rsp - 0x18 ]
adox r8, [ rsp - 0x20 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r14, [ rsp - 0x28 ]
adox r9, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rsi + 0x10 ]
adcx r15, [ rsp - 0x48 ]
adcx rbp, r8
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx rax, r12, [ rsi + 0x10 ]
setc dl
movzx rdx, dl
adox rdx, rdi
clc
adcx r8, r13
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r10
mulx r10, r13, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], rdi
mulx rdi, rcx, r14
adcx r13, r9
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mulx r9, rcx, rdi
mov rdi, rdx
mov [ rsp + 0x10 ], r13
seto r13b
mov [ rsp + 0x18 ], r8
mov r8, -0x2 
inc r8
adox rdi, r14
adox rcx, r15
mov rdi, 0xffffffffffffffff 
mulx r15, r14, rdi
adcx r12, r10
mov r10, 0x0 
adcx rax, r10
clc
adcx r14, r9
mov r9, 0xffffffff 
mulx r8, r10, r9
adcx r10, r15
mov rdx, 0x0 
adcx r8, rdx
clc
adcx r11, rcx
adox r14, rbp
adox r10, rbx
adcx r14, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x10 ]
adox r8, [ rsp + 0x8 ]
adcx r12, r8
movzx rbp, r13b
adox rbp, rdx
adcx rax, rbp
mov rdx, r11
mulx rbx, r11, rdi
mov rbx, r11
mov r13, -0x2 
inc r13
adox rbx, rdx
mov rbx, 0xffffffff00000000 
mov rdx, r11
mulx rcx, r11, rbx
adox r11, r14
setc r15b
clc
adcx r11, [ rsp - 0x30 ]
mulx r8, r14, rdi
setc bpl
clc
adcx r14, rcx
mulx r13, rcx, r9
adcx rcx, r8
mov rdx, 0x0 
adcx r13, rdx
adox r14, r10
adox rcx, r12
adox r13, rax
clc
mov r10, -0x1 
movzx rbp, bpl
adcx rbp, r10
adcx r14, [ rsp - 0x38 ]
adcx rcx, [ rsp + 0x0 ]
adcx r13, [ rsp - 0x8 ]
movzx r12, r15b
adox r12, rdx
adcx r12, [ rsp - 0x10 ]
mov rdx, rdi
mulx r15, rdi, r11
mov r15, rdi
inc r10
adox r15, r11
mulx rax, r15, rdi
mov rdx, rdi
mulx r11, rdi, rbx
setc bpl
clc
adcx r15, r11
adox rdi, r14
adox r15, rcx
mulx r14, r8, r9
adcx r8, rax
adcx r14, r10
adox r8, r13
adox r14, r12
movzx rcx, bpl
adox rcx, r10
mov r13, rdi
sub r13, 0x00000001
mov rbp, r15
sbb rbp, rbx
mov r12, r8
mov rdx, 0xffffffffffffffff 
sbb r12, rdx
mov rax, r14
sbb rax, r9
sbb rcx, 0x00000000
cmovc r12, r8
cmovc rbp, r15
cmovc r13, rdi
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], r13
cmovc rax, r14
mov [ rcx + 0x10 ], r12
mov [ rcx + 0x8 ], rbp
mov [ rcx + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.5854
; seed 3751943024192707 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 900535 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=243, initial num_batches=31): 75095 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08338931857173791
; number reverted permutation / tried permutation: 75048 / 89969 =83.415%
; number reverted decision / tried decision: 63559 / 90030 =70.598%
; validated in 1.59s
