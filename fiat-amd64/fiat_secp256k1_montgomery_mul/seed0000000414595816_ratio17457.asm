SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rax + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov [ rsp - 0x70 ], r12
xor r12, r12
adox r8, r11
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
adox r11, r9
mov rdx, [ rax + 0x18 ]
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r14
mulx r14, r11, [ rax + 0x0 ]
adcx r15, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mulx r15, r14, [ rax + 0x10 ]
adcx r14, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mulx r14, rdi, [ rax + 0x0 ]
adox rcx, r12
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r11
mulx r11, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], r9
mulx r9, rdi, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r12, r14
adox rdi, r11
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x18 ]
adcx r14, r15
seto dl
mov r15, -0x2 
inc r15
adox rbx, r10
mov bl, dl
mov rdx, [ rax + 0x0 ]
mulx r15, r10, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], r14
mulx r14, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r12
mulx r12, rdi, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r9
mov byte [ rsp + 0x18 ], bl
mulx rbx, r9, [ rax + 0x10 ]
clc
adcx r11, r15
adcx r9, r14
adcx rdi, rbx
mov rdx, 0x0 
adcx r12, rdx
mov r15, r13
clc
adcx r15, rbp
adox r15, r8
mov rbp, r13
adcx rbp, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x40 ]
setc r8b
clc
adcx r10, r15
movzx r14, r8b
mov rbx, [ rsp - 0x40 ]
lea r14, [ r14 + rbx ]
mov rbx, 0xd838091dd2253531 
mov rdx, rbx
mulx r15, rbx, r10
adox rbp, [ rsp - 0x48 ]
adox r13, rcx
adox r14, [ rsp - 0x18 ]
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, rbx
adcx r11, rbp
adcx r9, r13
adcx rdi, r14
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, [ rax + 0x18 ]
mov rdx, 0xfffffffefffffc2f 
mulx r14, r13, rbx
seto bl
mov rdx, -0x2 
inc rdx
adox r13, r10
mov r13, r15
setc r10b
clc
adcx r13, r14
seto r14b
movzx rdx, byte [ rsp + 0x18 ]
mov [ rsp + 0x20 ], rdi
mov rdi, 0x0 
dec rdi
adox rdx, rdi
adox r8, [ rsp + 0x10 ]
mov rdx, 0x0 
adox rbp, rdx
dec rdx
movzx r14, r14b
adox r14, rdx
adox r11, r13
mov rdi, r15
adcx rdi, rcx
adcx r15, rcx
adox rdi, r9
mov r9, 0x0 
adcx rcx, r9
clc
adcx r11, [ rsp - 0x20 ]
adcx rdi, [ rsp + 0x8 ]
setc r14b
clc
movzx rbx, bl
movzx r10, r10b
adcx r10, rdx
adcx r12, rbx
adox r15, [ rsp + 0x20 ]
adox rcx, r12
setc bl
clc
movzx r14, r14b
adcx r14, rdx
adcx r15, [ rsp + 0x0 ]
adcx r8, rcx
movzx r10, bl
adox r10, r9
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx r14, r13, r11
mov r14, 0xfffffffefffffc2f 
mov rdx, r13
mulx r12, r13, r14
mov rbx, -0x3 
inc rbx
adox r13, r11
adcx rbp, r10
mov r13, 0xffffffffffffffff 
mulx rcx, r11, r13
mov r10, r11
setc dl
clc
adcx r10, r12
mov r12, r11
adcx r12, rcx
adox r10, rdi
adcx r11, rcx
adcx rcx, r9
adox r12, r15
clc
adcx r10, [ rsp - 0x28 ]
adcx r12, [ rsp - 0x38 ]
adox r11, r8
adox rcx, rbp
movzx rdi, dl
adox rdi, r9
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx r8, r15, r10
adcx r11, [ rsp - 0x30 ]
mov rdx, r15
mulx r15, r8, r14
mulx r9, rbp, r13
adcx rcx, [ rsp - 0x8 ]
mov rdx, rbp
inc rbx
adox rdx, r15
mov r15, rbp
adox r15, r9
adcx rdi, [ rsp - 0x10 ]
setc bl
clc
adcx r8, r10
adcx rdx, r12
adox rbp, r9
adcx r15, r11
mov r8, 0x0 
adox r9, r8
adcx rbp, rcx
adcx r9, rdi
movzx r10, bl
adc r10, 0x0
mov r12, rdx
sub r12, r14
mov r11, r15
sbb r11, r13
mov rcx, rbp
sbb rcx, r13
mov rbx, r9
sbb rbx, r13
sbb r10, 0x00000000
cmovc rcx, rbp
cmovc r12, rdx
cmovc r11, r15
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], r11
cmovc rbx, r9
mov [ r10 + 0x18 ], rbx
mov [ r10 + 0x10 ], rcx
mov [ r10 + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.7457
; seed 3845064954388164 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1034157 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=164, initial num_batches=31): 77432 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07487451131694704
; number reverted permutation / tried permutation: 76515 / 90121 =84.903%
; number reverted decision / tried decision: 65950 / 89878 =73.377%
; validated in 2.114s
