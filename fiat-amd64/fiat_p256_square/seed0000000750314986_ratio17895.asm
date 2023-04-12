SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r12, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
adox r15, r13
adox rax, rdi
mov rdx, 0xffffffffffffffff 
mulx rdi, r13, r11
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x10 ]
adcx rcx, rbp
adcx r9, r14
mov rdx, 0xffffffff 
mulx r14, rbp, r11
mov rdx, -0x2 
inc rdx
adox rbp, rdi
mov rdi, 0x0 
adox r14, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r9
mulx r9, rdi, [ rsi + 0x8 ]
adcx rdi, r8
adc r9, 0x0
add r13, r11
adcx rbp, r12
mov rdx, 0xffffffff00000001 
mulx r12, r13, r11
adcx r14, r15
adcx r13, rax
adcx r12, r10
mov rdx, [ rsi + 0x0 ]
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rax, r15
setc r8b
clc
adcx rbx, rbp
adcx rcx, r14
adcx r13, [ rsp - 0x38 ]
adcx rdi, r12
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r14, rbp, rbx
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rax
mov [ rsp - 0x28 ], r11
mulx r11, rax, rdx
adox r12, r10
adox rax, r15
mov rdx, 0xffffffff 
mulx r15, r10, rbx
seto dl
mov [ rsp - 0x20 ], rax
mov rax, -0x2 
inc rax
adox r10, r14
movzx r14, dl
lea r14, [ r14 + r11 ]
mov r11, 0x0 
adox r15, r11
mov rdx, -0x3 
inc rdx
adox rbp, rbx
adox r10, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r12
mulx r12, r14, rbx
movzx rbx, r8b
adcx rbx, r9
adox r15, r13
adox r14, rdi
adox r12, rbx
setc r9b
clc
adcx rbp, rax
seto r8b
mov r13, -0x2 
inc r13
adox r11, r10
adox rbp, r15
mov rdi, 0xffffffff 
mov rdx, r11
mulx r10, r11, rdi
adcx rcx, [ rsp - 0x40 ]
adox rcx, r14
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, rbx, [ rsi + 0x10 ]
adcx rbx, [ rsp - 0x48 ]
mov rdx, 0x0 
adcx r15, rdx
adox rbx, r12
movzx r14, r8b
movzx r9, r9b
lea r14, [ r14 + r9 ]
adox r15, r14
mov r9, 0xffffffffffffffff 
mov rdx, rax
mulx r8, rax, r9
clc
adcx rax, rdx
seto al
inc r13
adox r11, r8
adox r10, r13
adcx r11, rbp
mov r12, 0xffffffff00000001 
mulx r14, rbp, r12
mov rdx, -0x3 
inc rdx
adox r11, [ rsp - 0x28 ]
mov rdx, rdi
mulx r8, rdi, r11
adcx r10, rcx
adcx rbp, rbx
adcx r14, r15
mov rdx, r11
mulx rcx, r11, r12
movzx rbx, al
adcx rbx, r13
mulx r15, rax, r9
clc
adcx rdi, r15
adcx r8, r13
clc
adcx rax, rdx
adox r10, [ rsp - 0x30 ]
adcx rdi, r10
adox rbp, [ rsp - 0x10 ]
adox r14, [ rsp - 0x20 ]
adcx r8, rbp
adox rbx, [ rsp - 0x18 ]
adcx r11, r14
adcx rcx, rbx
seto al
adc al, 0x0
movzx rax, al
mov rdx, rdi
sub rdx, r9
mov r15, r8
mov r10, 0xffffffff 
sbb r15, r10
mov rbp, r11
sbb rbp, 0x00000000
mov r14, rcx
sbb r14, r12
movzx rbx, al
sbb rbx, 0x00000000
cmovc rbp, r11
cmovc r15, r8
cmovc rdx, rdi
cmovc r14, rcx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], rbp
mov [ rbx + 0x8 ], r15
mov [ rbx + 0x18 ], r14
mov [ rbx + 0x0 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.7895
; seed 1219292514933583 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 767592 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=231, initial num_batches=31): 70159 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09140142158855225
; number reverted permutation / tried permutation: 76891 / 89850 =85.577%
; number reverted decision / tried decision: 59788 / 90149 =66.321%
; validated in 0.933s
