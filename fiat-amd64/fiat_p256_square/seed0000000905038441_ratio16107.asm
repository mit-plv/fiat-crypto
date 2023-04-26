SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
test al, al
adox r8, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rax
adox r10, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, r9, [ rsi + 0x0 ]
adox r9, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mulx r14, rbx, rax
adcx rbx, rax
mov rbx, 0x0 
adox r13, rbx
mov [ rsp - 0x58 ], r15
mov r15, -0x3 
inc r15
adox rbp, r14
adox r12, rbx
adcx rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx r14, r8, [ rsi + 0x10 ]
adcx r12, r10
mov rdx, 0xffffffff00000001 
mulx rbx, r10, rax
mov rdx, [ rsi + 0x0 ]
mulx r15, rax, [ rsi + 0x18 ]
adcx r10, r9
adcx rbx, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rsi + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r11, r15
adox r9, rcx
mov rdx, [ rsi + 0x8 ]
mulx r15, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], rax
mulx rax, r11, rdx
setc dl
clc
adcx rcx, r9
adox r11, r13
mov r13b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r11
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, 0x0 
adox rax, rdx
mov [ rsp - 0x28 ], rax
mov rax, -0x3 
inc rax
adox rdi, rbp
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx rax, rbp, rdi
adox rcx, r12
adcx r9, r15
adox r9, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r12, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], r14
mulx r14, r15, rdi
adcx r12, r11
mov r11, 0x0 
adcx r10, r11
clc
adcx r15, rax
adox r12, rbx
movzx rbx, r13b
adox rbx, r10
adcx r14, r11
clc
adcx rbp, rdi
adcx r15, rcx
adcx r14, r9
mov rbp, 0xffffffff00000001 
mov rdx, rdi
mulx r13, rdi, rbp
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, rdx
adcx rdi, r12
adcx r13, rbx
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, [ rsi + 0x0 ]
seto dl
adc dl, 0x0
movzx rdx, dl
adox r8, r10
adox rax, [ rsp - 0x20 ]
adcx r9, r15
mov r12b, dl
mov rdx, [ rsi + 0x18 ]
mulx r15, rbx, [ rsi + 0x10 ]
adox rbx, rcx
adox r15, r11
adcx r8, r14
mov rdx, rbp
mulx r14, rbp, r9
adcx rax, rdi
adcx rbx, r13
movzx rcx, r12b
adcx rcx, r15
mov rdi, 0xffffffffffffffff 
mov rdx, r9
mulx r13, r9, rdi
mov r10, 0xffffffff 
mulx r15, r12, r10
mov r10, -0x3 
inc r10
adox r9, rdx
setc r9b
clc
adcx r12, r13
adcx r15, r11
adox r12, r8
clc
adcx r12, [ rsp - 0x38 ]
adox r15, rax
adox rbp, rbx
mov rdx, r12
mulx r8, r12, rdi
adox r14, rcx
adcx r15, [ rsp - 0x40 ]
adcx rbp, [ rsp - 0x48 ]
movzx rax, r9b
adox rax, r11
mov rbx, -0x3 
inc rbx
adox r12, rdx
adcx r14, [ rsp - 0x30 ]
mov rbx, 0xffffffff 
mulx r9, r12, rbx
adcx rax, [ rsp - 0x28 ]
setc cl
clc
adcx r12, r8
adox r12, r15
adcx r9, r11
adox r9, rbp
mov r13, 0xffffffff00000001 
mulx r15, r8, r13
adox r8, r14
adox r15, rax
movzx rdx, cl
adox rdx, r11
mov rbp, r12
sub rbp, rdi
mov r14, r9
sbb r14, rbx
mov rcx, r8
sbb rcx, 0x00000000
mov rax, r15
sbb rax, r13
sbb rdx, 0x00000000
cmovc rbp, r12
cmovc rcx, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], rbp
mov [ rdx + 0x10 ], rcx
cmovc rax, r15
mov [ rdx + 0x18 ], rax
cmovc r14, r9
mov [ rdx + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6107
; seed 3884745083904471 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1234428 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=117, initial num_batches=31): 78489 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06358329525901875
; number reverted permutation / tried permutation: 67653 / 90067 =75.114%
; number reverted decision / tried decision: 56126 / 89932 =62.409%
; validated in 1.885s
