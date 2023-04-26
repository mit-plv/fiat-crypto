SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
mov [ rsp - 0x48 ], r10
mulx r10, rdi, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r8
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox rcx, r11
adox r12, r8
mov r11, 0xffffffff 
mov rdx, r11
mulx r8, r11, r15
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], rcx
mulx rcx, r12, r15
adcx rdi, rcx
adcx r11, r10
mov r10, 0x0 
adcx r8, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, [ rax + 0x18 ]
adox rcx, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
clc
adcx rbp, r14
adcx r9, rcx
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r14, [ rax + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r15, r13
adcx r14, rbx
mov r15, 0x0 
adcx rcx, r15
adox r12, rbp
mov rdx, [ rsi + 0x8 ]
mulx r13, rbx, [ rax + 0x10 ]
clc
adcx r12, [ rsp - 0x28 ]
mov rdx, 0xffffffffffffffff 
mulx r15, rbp, r12
mov [ rsp - 0x8 ], r10
mulx r10, r15, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], r15
mulx r15, r10, [ rax + 0x8 ]
setc dl
clc
adcx r10, [ rsp - 0x30 ]
adox rdi, r9
adcx rbx, r15
setc r9b
clc
mov r15, -0x1 
movzx rdx, dl
adcx rdx, r15
adcx rdi, r10
adox r11, r14
mov rdx, [ rax + 0x18 ]
mulx r10, r14, [ rsi + 0x8 ]
adox r8, rcx
adcx rbx, r11
seto dl
inc r15
mov rcx, -0x1 
movzx r9, r9b
adox r9, rcx
adox r13, r14
adcx r13, r8
adox r10, r15
movzx r9, dl
adcx r9, r10
mov r11, 0xffffffff 
mov rdx, rbp
mulx r14, rbp, r11
mov r8, 0xffffffff00000000 
mulx r15, r10, r8
inc rcx
adox r15, [ rsp + 0x8 ]
adox rbp, [ rsp + 0x0 ]
adox r14, rcx
mov r8, -0x3 
inc r8
adox rdx, r12
adox r10, rdi
adox r15, rbx
adox rbp, r13
mov rdx, [ rax + 0x10 ]
mulx rdi, r12, [ rsi + 0x10 ]
adox r14, r9
seto dl
adc dl, 0x0
movzx rdx, dl
mov bl, dl
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x8 ]
adox r13, [ rsp - 0x38 ]
adox r12, r9
adcx r10, [ rsp - 0x40 ]
adcx r13, r15
adcx r12, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r15, [ rsi + 0x10 ]
adox r15, rdi
adox rbp, rcx
adcx r15, r14
mov rdx, 0xffffffffffffffff 
mulx r14, rdi, r10
mov r14, 0xffffffff00000000 
mov rdx, rdi
mulx r9, rdi, r14
movzx rcx, bl
adcx rcx, rbp
mov rbx, rdx
inc r8
adox rbx, r10
adox rdi, r13
setc bl
clc
adcx rdi, [ rsp - 0x48 ]
mov r10, 0xffffffffffffffff 
mulx rbp, r13, r10
setc r8b
clc
adcx r13, r9
adox r13, r12
mulx r9, r12, r11
adcx r12, rbp
mov rdx, 0x0 
adcx r9, rdx
adox r12, r15
adox r9, rcx
clc
mov r15, -0x1 
movzx r8, r8b
adcx r8, r15
adcx r13, [ rsp - 0x18 ]
adcx r12, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x10 ]
movzx rcx, bl
adox rcx, rdx
adcx rcx, [ rsp - 0x8 ]
mov rdx, r10
mulx rbx, r10, rdi
mov rdx, r10
mulx rbx, r10, r11
mov r8, 0xffffffffffffffff 
mulx r15, rbp, r8
mulx r8, r11, r14
mov r14, -0x2 
inc r14
adox rbp, r8
setc r8b
clc
adcx rdx, rdi
adcx r11, r13
adcx rbp, r12
adox r10, r15
adcx r10, r9
mov rdx, 0x0 
adox rbx, rdx
adcx rbx, rcx
movzx rdi, r8b
adc rdi, 0x0
mov r13, r11
sub r13, 0x00000001
mov r12, rbp
mov r9, 0xffffffff00000000 
sbb r12, r9
mov r8, r10
mov rcx, 0xffffffffffffffff 
sbb r8, rcx
mov r15, rbx
mov rdx, 0xffffffff 
sbb r15, rdx
sbb rdi, 0x00000000
cmovc r8, r10
cmovc r15, rbx
cmovc r13, r11
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], r15
cmovc r12, rbp
mov [ rdi + 0x8 ], r12
mov [ rdi + 0x10 ], r8
mov [ rdi + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4940
; seed 0268348899348282 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1853465 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=213, initial num_batches=31): 143036 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07717221528326675
; number reverted permutation / tried permutation: 65492 / 89982 =72.783%
; number reverted decision / tried decision: 57757 / 90017 =64.162%
; validated in 4.849s
