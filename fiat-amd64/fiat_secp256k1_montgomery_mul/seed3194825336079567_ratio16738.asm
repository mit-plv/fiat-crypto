SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 192
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
xor rdx, rdx
adox rcx, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r8
mulx r8, rcx, [ rax + 0x0 ]
adcx r15, r8
adox r13, r10
adox r12, r14
mov rdx, [ rax + 0x10 ]
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], r12
mulx r12, r8, [ rsi + 0x0 ]
adcx r14, rdi
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x8 ], r13
mulx r13, rdi, r8
adcx r9, r10
mov rdx, [ rax + 0x8 ]
mulx r10, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], r9
mov [ rsp + 0x8 ], r14
mulx r14, r9, rdi
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x10 ], rbx
mov [ rsp + 0x18 ], r15
mulx r15, rbx, rdi
mov rdi, 0x0 
adox rbp, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], rbp
mulx rbp, rdi, [ rax + 0x8 ]
add rdi, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], rcx
mulx rcx, r11, [ rsi + 0x8 ]
adcx r11, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x30 ], r11
mulx r11, rbp, [ rax + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r13, r12
adox r10, [ rsp - 0x18 ]
adcx rbp, rcx
mov r12, [ rsp - 0x28 ]
adox r12, [ rsp - 0x20 ]
mov rcx, [ rsp - 0x30 ]
mov rdx, 0x0 
adox rcx, rdx
adc r11, 0x0
mov [ rsp + 0x38 ], r11
mov r11, r9
add r11, r15
mov r15, -0x3 
inc r15
adox rbx, r8
adox r11, r13
mov rbx, r9
adcx rbx, r14
adcx r9, r14
adcx r14, rdx
clc
adcx r11, [ rsp - 0x40 ]
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r13, r8, r11
adox rbx, r10
adcx rdi, rbx
adox r9, r12
adox r14, rcx
adcx r9, [ rsp + 0x30 ]
adcx rbp, r14
mov r13, 0xfffffffefffffc2f 
mov rdx, r13
mulx r10, r13, r8
seto r12b
movzx r12, r12b
adcx r12, [ rsp + 0x38 ]
inc r15
adox r13, r11
mov r13, 0xffffffffffffffff 
mov rdx, r8
mulx rcx, r8, r13
mov r11, r8
setc dl
clc
adcx r11, r10
adox r11, rdi
mov rbx, r8
adcx rbx, rcx
adox rbx, r9
adcx r8, rcx
mov rdi, 0x0 
adcx rcx, rdi
adox r8, rbp
clc
adcx r11, [ rsp + 0x28 ]
adcx rbx, [ rsp + 0x18 ]
adox rcx, r12
mov r14, 0xd838091dd2253531 
xchg rdx, r14
mulx rbp, r9, r11
mov rbp, 0xfffffffefffffc2f 
mov rdx, r9
mulx r10, r9, rbp
mulx rdi, r12, r13
seto dl
inc r15
adox r9, r11
mov r9, r12
setc r11b
clc
adcx r9, r10
adox r9, rbx
mov rbx, r12
adcx rbx, rdi
adcx r12, rdi
adcx rdi, r15
clc
adcx r9, [ rsp - 0x48 ]
setc r10b
clc
mov r15, -0x1 
movzx r11, r11b
adcx r11, r15
adcx r8, [ rsp + 0x8 ]
adcx rcx, [ rsp + 0x0 ]
movzx r11, dl
movzx r14, r14b
lea r11, [ r11 + r14 ]
adox rbx, r8
adcx r11, [ rsp + 0x10 ]
adox r12, rcx
adox rdi, r11
seto r14b
adc r14b, 0x0
movzx r14, r14b
mov rdx, 0xd838091dd2253531 
mulx rcx, r8, r9
add r10b, 0x7F
adox rbx, [ rsp - 0x38 ]
adox r12, [ rsp - 0x8 ]
mov rdx, r8
mulx r8, rcx, r13
mulx r11, r10, rbp
mov rdx, rcx
adcx rdx, r11
mov r11, rcx
adcx r11, r8
adox rdi, [ rsp - 0x10 ]
adcx rcx, r8
movzx r14, r14b
movzx r15, r14b
adox r15, [ rsp + 0x20 ]
seto r14b
mov rbp, -0x2 
inc rbp
adox r10, r9
adox rdx, rbx
adox r11, r12
adox rcx, rdi
mov r10, 0x0 
adcx r8, r10
adox r8, r15
movzx r9, r14b
adox r9, r10
mov rbx, rdx
mov r12, 0xfffffffefffffc2f 
sub rbx, r12
mov rdi, r11
sbb rdi, r13
mov r14, rcx
sbb r14, r13
mov r15, r8
sbb r15, r13
sbb r9, 0x00000000
cmovc rbx, rdx
cmovc rdi, r11
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], rdi
cmovc r14, rcx
cmovc r15, r8
mov [ r9 + 0x0 ], rbx
mov [ r9 + 0x10 ], r14
mov [ r9 + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.6738
; seed 3194825336079567 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 12202 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 863 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07072611047369284
; number reverted permutation / tried permutation: 371 / 513 =72.320%
; number reverted decision / tried decision: 328 / 486 =67.490%
; validated in 5.144s
