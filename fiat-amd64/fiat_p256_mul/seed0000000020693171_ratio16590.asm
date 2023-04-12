SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], r14
mulx r14, r10, [ rsi + 0x10 ]
add rcx, r12
adcx r9, r8
mov rdx, [ rsi + 0x0 ]
mulx r12, r8, [ rax + 0x18 ]
adcx r8, rbx
adc r12, 0x0
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r14
mulx r14, rbx, rbp
add rbx, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r10
mulx r10, rbx, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r11, [ rax + 0x18 ]
adox r15, r10
adox r11, rdi
mov rdx, 0xffffffff 
mulx r10, rdi, rbp
mov rdx, 0x0 
adox rbx, rdx
mov [ rsp - 0x20 ], rbx
mov rbx, -0x3 
inc rbx
adox rdi, r14
adox r10, rdx
adcx rdi, rcx
adcx r10, r9
mov rdx, [ rax + 0x0 ]
mulx r9, rcx, [ rsi + 0x8 ]
inc rbx
adox rcx, rdi
mov rdx, 0xffffffff00000001 
mulx rdi, r14, rcx
mov [ rsp - 0x18 ], r11
mulx r11, rbx, rbp
adcx rbx, r8
adcx r11, r12
mov rdx, [ rsi + 0x8 ]
mulx r8, rbp, [ rax + 0x8 ]
setc dl
clc
adcx rbp, r9
adox rbp, r10
mov r12b, dl
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rax + 0x10 ]
adcx r10, r8
adox r10, rbx
adcx r13, r9
adox r13, r11
mov rdx, 0xffffffff 
mulx r11, rbx, rcx
mov r8, [ rsp - 0x40 ]
mov r9, 0x0 
adcx r8, r9
movzx r9, r12b
adox r9, r8
mov r12, 0xffffffffffffffff 
mov rdx, rcx
mulx r8, rcx, r12
clc
adcx rcx, rdx
seto cl
mov rdx, -0x2 
inc rdx
adox rbx, r8
mov r8, 0x0 
adox r11, r8
adcx rbx, rbp
adcx r11, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, rbp, [ rax + 0x8 ]
adcx r14, r13
adcx rdi, r9
movzx rdx, cl
adc rdx, 0x0
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, [ rax + 0x0 ]
test al, al
adox rbp, r9
adox r10, [ rsp - 0x30 ]
adcx rcx, rbx
adcx rbp, r11
adcx r10, r14
mov rdx, [ rax + 0x18 ]
mulx r11, rbx, [ rsi + 0x10 ]
adox rbx, [ rsp - 0x38 ]
adox r11, r8
adcx rbx, rdi
mov rdx, rcx
mulx r14, rcx, r12
adcx r11, r13
mov rdi, -0x3 
inc rdi
adox rcx, rdx
mov rcx, 0xffffffff 
mulx r9, r13, rcx
setc dil
clc
adcx r13, r14
adox r13, rbp
adcx r9, r8
adox r9, r10
mov rbp, 0xffffffff00000001 
mulx r14, r10, rbp
adox r10, rbx
adox r14, r11
clc
adcx r13, [ rsp - 0x48 ]
mov rdx, r12
mulx rbx, r12, r13
adcx r9, [ rsp - 0x28 ]
adcx r15, r10
mov rdx, rcx
mulx r11, rcx, r13
movzx r10, dil
adox r10, r8
adcx r14, [ rsp - 0x18 ]
adcx r10, [ rsp - 0x20 ]
mov rdi, -0x3 
inc rdi
adox rcx, rbx
adox r11, r8
mov rbx, -0x3 
inc rbx
adox r12, r13
adox rcx, r9
mov rdx, r13
mulx r12, rbx, rbp
adox r11, r15
adox rbx, r14
adox r12, r10
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov rdx, rcx
mov r9, 0xffffffffffffffff 
sub rdx, r9
mov r15, r11
mov r14, 0xffffffff 
sbb r15, r14
mov r10, rbx
sbb r10, 0x00000000
mov r8, r12
sbb r8, rbp
movzx rdi, r13b
sbb rdi, 0x00000000
cmovc rdx, rcx
cmovc r8, r12
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], r8
cmovc r15, r11
mov [ rdi + 0x8 ], r15
cmovc r10, rbx
mov [ rdi + 0x10 ], r10
mov [ rdi + 0x0 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.6590
; seed 3524942756754285 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1225519 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=116, initial num_batches=31): 79348 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06474644619952853
; number reverted permutation / tried permutation: 64795 / 89646 =72.279%
; number reverted decision / tried decision: 55116 / 90353 =61.001%
; validated in 2.215s
