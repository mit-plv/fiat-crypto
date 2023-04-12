SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 136
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r14
mulx r14, r11, [ rsi + 0x0 ]
adcx r15, r14
adcx r12, rdi
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, rdx
adcx rdi, r13
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r14
mulx r14, r13, [ rsi + 0x18 ]
clc
adcx rbx, r9
adcx rax, rbp
adcx r13, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], rdi
mulx rdi, rbp, r8
mov rdi, 0x0 
adcx r14, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
adox r10, rcx
adox rdi, r9
mov rdx, 0x0 
adox r12, rdx
mov rcx, 0xffffffff00000000 
mov rdx, rbp
mulx r9, rbp, rcx
mov rcx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r11
mulx r11, r15, rcx
mov rcx, rdx
add rcx, r8
adcx rbp, rbx
mov rcx, -0x2 
inc rcx
adox r15, r9
mov r8, 0xffffffff 
mulx r9, rbx, r8
adox rbx, r11
adcx r15, rax
adcx rbx, r13
mov rax, 0x0 
adox r9, rax
mov r13, -0x3 
inc r13
adox rbp, [ rsp - 0x40 ]
mov rdx, 0xffffffffffffffff 
mulx rax, r11, rbp
mov rax, 0xffffffff00000000 
mov rdx, r11
mulx r13, r11, rax
adox r15, [ rsp - 0x48 ]
adox r10, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r10
mulx r10, rax, [ rsi + 0x10 ]
adcx r9, r14
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, rdx
setc dl
clc
adcx rax, r8
adcx r14, r10
adox rdi, r9
movzx r8, dl
adox r8, r12
mov rdx, [ rsi + 0x10 ]
mulx r10, r12, [ rsi + 0x18 ]
adcx r12, rcx
mov rdx, rbx
seto r9b
mov rcx, -0x2 
inc rcx
adox rdx, rbp
adox r11, r15
mov rdx, 0xffffffff 
mulx r15, rbp, rbx
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp + 0x0 ], r10
mulx r10, rcx, rbx
setc bl
clc
adcx rcx, r13
adcx rbp, r10
mov r13, 0x0 
adcx r15, r13
clc
adcx r11, [ rsp - 0x8 ]
adox rcx, [ rsp - 0x10 ]
adox rbp, rdi
mulx r10, rdi, r11
adox r15, r8
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx r8, r10, rdi
adcx rax, rcx
movzx rcx, r9b
adox rcx, r13
adcx r14, rbp
adcx r12, r15
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rbp, r9, rdi
movzx r15, bl
mov r13, [ rsp + 0x0 ]
lea r15, [ r15 + r13 ]
mov r13, rdi
mov rbx, -0x2 
inc rbx
adox r13, r11
adox r10, rax
adcx r15, rcx
setc r13b
clc
adcx r9, r8
mov r11, 0xffffffff 
mov rdx, rdi
mulx r8, rdi, r11
adcx rdi, rbp
adox r9, r14
mov rdx, 0x0 
adcx r8, rdx
adox rdi, r12
adox r8, r15
movzx rax, r13b
adox rax, rdx
add r10, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
mov rcx, 0xffffffffffffffff 
mov rdx, r10
mulx r14, r10, rcx
adcx r8, [ rsp - 0x30 ]
adcx rax, [ rsp - 0x38 ]
mov r14, r10
inc rbx
adox r14, rdx
mov r14, 0xffffffff00000000 
mov rdx, r10
mulx r12, r10, r14
adox r10, r9
mulx r13, rbp, rcx
setc r15b
clc
adcx rbp, r12
mulx r12, r9, r11
adox rbp, rdi
adcx r9, r13
adox r9, r8
adcx r12, rbx
adox r12, rax
movzx rdi, r15b
adox rdi, rbx
mov rdx, r10
sub rdx, 0x00000001
mov r8, rbp
sbb r8, r14
mov r15, r9
sbb r15, rcx
mov rax, r12
sbb rax, r11
sbb rdi, 0x00000000
cmovc r15, r9
cmovc r8, rbp
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], r15
cmovc rdx, r10
cmovc rax, r12
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x18 ], rax
mov [ rdi + 0x0 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.5983
; seed 0827408223596244 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1005744 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=207, initial num_batches=31): 78543 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07809442561924307
; number reverted permutation / tried permutation: 76014 / 90057 =84.407%
; number reverted decision / tried decision: 64636 / 89942 =71.864%
; validated in 1.777s
