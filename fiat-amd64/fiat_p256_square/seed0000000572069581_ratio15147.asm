SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
add r11, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, rax
adcx rcx, r9
mov r9, 0xffffffff 
mov rdx, r9
mov [ rsp - 0x40 ], r12
mulx r12, r9, rax
mov rdx, -0x2 
inc rdx
adox r9, rbp
mov rbp, 0x0 
adox r12, rbp
adc r15, 0x0
xor rdx, rdx
adox rdi, rax
adox r9, r11
mov rdx, [ rsi + 0x0 ]
mulx rbp, rdi, [ rsi + 0x8 ]
adox r12, r8
adox r10, rcx
adcx rdi, r9
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, rdx
mov rdx, 0xffffffff00000001 
mulx rcx, r8, rdi
setc r9b
clc
adcx rax, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, rbp, [ rsi + 0x10 ]
adcx rbp, r11
adcx r13, rcx
mov rdx, 0x0 
adcx r14, rdx
clc
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx r12, rax
mov r9, 0xffffffffffffffff 
mov rdx, rdi
mulx rax, rdi, r9
adox rbx, r15
seto r15b
inc r11
adox rdi, rdx
mov rdi, 0xffffffff 
mulx r11, rcx, rdi
setc dl
clc
adcx rcx, rax
mov rax, 0x0 
adcx r11, rax
clc
mov rax, -0x1 
movzx rdx, dl
adcx rdx, rax
adcx r10, rbp
adox rcx, r12
adcx r13, rbx
adox r11, r10
adox r8, r13
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, [ rsi + 0x8 ]
setc dl
clc
adcx rbp, [ rsp - 0x40 ]
setc bl
clc
movzx r15, r15b
movzx rdx, dl
adcx rdx, rax
adcx r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, rdx
adox r14, [ rsp - 0x38 ]
setc dl
clc
movzx rbx, bl
adcx rbx, rax
adcx r12, r15
movzx r13, dl
mov rbx, 0x0 
adox r13, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbx, r15, [ rsi + 0x18 ]
adcx r15, r10
inc rax
adox rcx, [ rsp - 0x48 ]
adox rbp, r11
adcx rbx, rax
adox r12, r8
mov rdx, r9
mulx r11, r9, rcx
mov rdx, rcx
mulx r8, rcx, rdi
clc
adcx rcx, r11
adcx r8, rax
clc
adcx r9, rdx
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
adcx rcx, rbp
adox r15, r14
adox rbx, r13
adcx r8, r12
mov rdx, 0xffffffff00000001 
mulx r13, r14, r9
adcx r14, r15
adcx r13, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rsi + 0x18 ]
seto dl
mov r12, -0x3 
inc r12
adox r9, rcx
movzx rcx, dl
adcx rcx, rax
clc
adcx r10, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbx, r15, [ rsi + 0x10 ]
adcx r15, r11
mov rdx, [ rsi + 0x18 ]
mulx rbp, r11, rdx
adcx r11, rbx
mov rdx, r9
mulx rbx, r9, rdi
adox r10, r8
adox r15, r14
adcx rbp, rax
adox r11, r13
adox rbp, rcx
mov r8, 0xffffffffffffffff 
mulx r13, r14, r8
clc
adcx r9, r13
seto cl
mov r13, -0x3 
inc r13
adox r14, rdx
adox r9, r10
adcx rbx, rax
adox rbx, r15
mov r13, 0xffffffff00000001 
mulx r10, r14, r13
seto dl
mov r15, r9
sub r15, r8
mov rax, rbx
sbb rax, rdi
mov r12, 0x0 
dec r12
movzx rdx, dl
adox rdx, r12
adox r11, r14
adox r10, rbp
movzx rbp, cl
mov rdx, 0x0 
adox rbp, rdx
mov rcx, r11
sbb rcx, 0x00000000
mov r14, r10
sbb r14, r13
sbb rbp, 0x00000000
cmovc rax, rbx
cmovc r15, r9
cmovc r14, r10
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r14
mov [ rbp + 0x0 ], r15
cmovc rcx, r11
mov [ rbp + 0x8 ], rax
mov [ rbp + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5147
; seed 2914975434064003 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1528637 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=233, initial num_batches=31): 134482 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0879751046193439
; number reverted permutation / tried permutation: 67255 / 89836 =74.864%
; number reverted decision / tried decision: 55501 / 90163 =61.556%
; validated in 2.553s
