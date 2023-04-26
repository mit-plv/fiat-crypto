SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, rcx
test al, al
adox r9, r10
adcx r11, rcx
mov r11, 0x0 
adox rbx, r11
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rax + 0x10 ]
mov rdx, -0x3 
inc rdx
adox rbp, r8
adox rcx, r12
adcx r9, rbp
adcx rbx, rcx
mov rdx, [ rax + 0x18 ]
mulx r12, r8, [ rsi + 0x0 ]
adox r8, r10
adox r12, r11
adcx r13, r8
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, -0x3 
inc rdx
adox r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx rcx, rdi, [ rax + 0x10 ]
adox rdi, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, [ rax + 0x18 ]
adox r8, rcx
adox rbp, r11
mov rdx, -0x3 
inc rdx
adox r15, r9
adox r10, rbx
mov r9, 0xffffffff00000001 
mov rdx, r15
mulx rbx, r15, r9
adox rdi, r13
mov r13, 0xffffffffffffffff 
mulx r11, rcx, r13
adcx r14, r12
adox r8, r14
seto r12b
movzx r12, r12b
adcx r12, rbp
mov rbp, 0xffffffff 
mulx r9, r14, rbp
mov rbp, -0x2 
inc rbp
adox rcx, rdx
setc cl
clc
adcx r14, r11
adox r14, r10
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r9, rdx
clc
adcx r10, r14
mov rdx, r13
mulx r14, r13, r10
adox r9, rdi
adox r15, r8
adox rbx, r12
movzx rdi, cl
mov r8, 0x0 
adox rdi, r8
mov rdx, [ rax + 0x8 ]
mulx rcx, r12, [ rsi + 0x10 ]
mov rdx, -0x3 
inc rdx
adox r12, r11
adox rcx, [ rsp - 0x40 ]
adcx r12, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mulx rbp, r8, r10
adox r11, [ rsp - 0x48 ]
adcx rcx, r15
mov r15, 0x0 
adox r9, r15
mov rdx, -0x3 
inc rdx
adox r8, r14
adox rbp, r15
mov r14, -0x3 
inc r14
adox r13, r10
mov rdx, [ rax + 0x8 ]
mulx r14, r13, [ rsi + 0x18 ]
adox r8, r12
mov rdx, [ rax + 0x10 ]
mulx r15, r12, [ rsi + 0x18 ]
adox rbp, rcx
adcx r11, rbx
mov rdx, 0xffffffff00000001 
mulx rcx, rbx, r10
adox rbx, r11
mov rdx, [ rax + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
adcx r9, rdi
adox rcx, r9
setc dl
clc
adcx r13, r11
movzx rdi, dl
mov r11, 0x0 
adox rdi, r11
adcx r12, r14
mov rdx, [ rsi + 0x18 ]
mulx r9, r14, [ rax + 0x18 ]
mov rdx, -0x3 
inc rdx
adox r10, r8
adox r13, rbp
adcx r14, r15
adox r12, rbx
adcx r9, r11
adox r14, rcx
mov r8, 0xffffffff 
mov rdx, r10
mulx r15, r10, r8
mov rbp, 0xffffffffffffffff 
mulx rcx, rbx, rbp
clc
adcx r10, rcx
adcx r15, r11
clc
adcx rbx, rdx
adcx r10, r13
adcx r15, r12
mov rbx, 0xffffffff00000001 
mulx r12, r13, rbx
adox r9, rdi
adcx r13, r14
adcx r12, r9
setc dil
seto dl
mov r14, r10
sub r14, rbp
mov rcx, r15
sbb rcx, r8
mov r9, r13
sbb r9, 0x00000000
mov r11, r12
sbb r11, rbx
movzx r8, dil
movzx rdx, dl
lea r8, [ r8 + rdx ]
sbb r8, 0x00000000
cmovc rcx, r15
cmovc r9, r13
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rcx
cmovc r11, r12
mov [ r8 + 0x18 ], r11
cmovc r14, r10
mov [ r8 + 0x0 ], r14
mov [ r8 + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6518
; seed 2477178112507916 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1213594 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=113, initial num_batches=31): 82273 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0677928532936056
; number reverted permutation / tried permutation: 64832 / 89889 =72.125%
; number reverted decision / tried decision: 55260 / 90110 =61.325%
; validated in 2.223s
