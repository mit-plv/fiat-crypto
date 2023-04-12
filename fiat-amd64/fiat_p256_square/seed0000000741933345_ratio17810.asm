SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r8, rax
mov [ rsp - 0x80 ], rbx
mov rbx, 0xffffffff00000001 
mov rdx, rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rax
add r14, r9
mov r9, -0x2 
inc r9
adox r12, r10
mov r10, 0x0 
adcx r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x18 ]
clc
adcx r10, r9
adox r11, r13
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, [ rsi + 0x18 ]
adox r13, rcx
mov rdx, 0x0 
adox r9, rdx
mov rcx, -0x3 
inc rcx
adox r8, rax
adox r14, r12
adox r15, r11
mov rdx, [ rsi + 0x10 ]
mulx rax, r8, [ rsi + 0x18 ]
adox rbx, r13
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rsi + 0x10 ]
adox rbp, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r10
mulx r10, rcx, rdx
seto dl
mov [ rsp - 0x38 ], rdi
mov rdi, -0x2 
inc rdi
adox r13, r11
adcx r8, [ rsp - 0x48 ]
adox rcx, r9
mov r11b, dl
mov rdx, [ rsi + 0x18 ]
mulx rdi, r9, rdx
adcx r9, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r9
mulx r9, rax, [ rsi + 0x18 ]
adox rax, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r8
mulx r8, r10, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], rax
mulx rax, rdi, rdx
clc
adcx rdi, r8
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r9
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r10, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, [ rsi + 0x8 ]
adcx r8, rax
adcx r14, r9
adox rdi, r15
adox r8, rbx
adox r14, rbp
mov rdx, 0x0 
adcx rcx, rdx
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rbx, r15, r10
mov rbp, 0xffffffff 
mov rdx, rbp
mulx rax, rbp, r10
clc
adcx rbp, rbx
movzx r9, r11b
adox r9, rcx
mov r11, 0x0 
adcx rax, r11
clc
adcx r15, r10
adcx rbp, rdi
seto r15b
mov rdi, -0x3 
inc rdi
adox r12, rbp
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rbx, rcx, r12
adcx rax, r8
mov r8, 0xffffffff00000001 
mov rdx, r10
mulx rbp, r10, r8
adcx r10, r14
adcx rbp, r9
mov rdx, 0xffffffff 
mulx r9, r14, r12
movzx r11, r15b
mov rdi, 0x0 
adcx r11, rdi
clc
adcx r14, rbx
adcx r9, rdi
adox r13, rax
clc
adcx rcx, r12
adox r10, [ rsp - 0x8 ]
adox rbp, [ rsp - 0x18 ]
adcx r14, r13
adox r11, [ rsp - 0x10 ]
adcx r9, r10
seto cl
mov r15, -0x3 
inc r15
adox r14, [ rsp - 0x38 ]
adox r9, [ rsp - 0x40 ]
mov rdx, r12
mulx rbx, r12, r8
adcx r12, rbp
adox r12, [ rsp - 0x28 ]
adcx rbx, r11
adox rbx, [ rsp - 0x30 ]
mov rdx, 0xffffffff 
mulx r13, rax, r14
mov r10, 0xffffffffffffffff 
mov rdx, r14
mulx rbp, r14, r10
movzx r11, cl
adcx r11, rdi
clc
adcx rax, rbp
adcx r13, rdi
clc
adcx r14, rdx
adcx rax, r9
adcx r13, r12
mulx rcx, r14, r8
adcx r14, rbx
adox r11, [ rsp - 0x20 ]
adcx rcx, r11
seto dl
adc dl, 0x0
movzx rdx, dl
mov r9, rax
sub r9, r10
mov r12, r13
mov rbx, 0xffffffff 
sbb r12, rbx
mov rbp, r14
sbb rbp, 0x00000000
mov r11, rcx
sbb r11, r8
movzx r15, dl
sbb r15, 0x00000000
cmovc rbp, r14
cmovc r12, r13
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], rbp
mov [ r15 + 0x8 ], r12
cmovc r11, rcx
mov [ r15 + 0x18 ], r11
cmovc r9, rax
mov [ r15 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.7810
; seed 3195012255316200 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 772727 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=231, initial num_batches=31): 69813 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09034626718103547
; number reverted permutation / tried permutation: 76316 / 89689 =85.090%
; number reverted decision / tried decision: 60665 / 90310 =67.174%
; validated in 0.921s
