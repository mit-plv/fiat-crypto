SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 152
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r8
mulx r8, rdi, rbp
xor rbp, rbp
adox r14, r10
mov rdx, [ rax + 0x8 ]
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rcx
mulx rcx, rbp, [ rsi + 0x0 ]
adcx r12, r11
adcx rbp, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rax + 0x18 ]
adcx r11, rcx
mov rdx, 0x0 
adcx r13, rdx
mov rcx, rdi
clc
adcx rcx, r15
adox rcx, r12
mov r15, rdi
adcx r15, r8
adcx rdi, r8
adcx r8, rdx
adox r15, rbp
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r15
mulx r15, r12, [ rsi + 0x10 ]
clc
adcx r14, rbp
adcx r12, r10
adox rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x18 ]
adcx r10, r15
mov rdx, [ rax + 0x0 ]
mulx r15, rbp, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r11, rdx
clc
adcx r9, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r9
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r11
mulx r11, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r12
mulx r12, r10, [ rsi + 0x18 ]
adcx r10, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r10
mulx r10, rbx, [ rax + 0x8 ]
adox r8, r13
adcx r15, r12
seto dl
mov r13, -0x2 
inc r13
adox rbp, rcx
mov cl, dl
mov rdx, [ rax + 0x10 ]
mulx r13, r12, [ rsi + 0x8 ]
setc dl
clc
adcx rbx, r11
adcx r12, r10
adox rbx, [ rsp - 0x30 ]
movzx r11, dl
lea r11, [ r11 + r9 ]
adcx r13, [ rsp - 0x40 ]
mov r9, [ rsp - 0x48 ]
mov r10, 0x0 
adcx r9, r10
mov rdx, 0xd838091dd2253531 
mov [ rsp + 0x8 ], r11
mulx r11, r10, rbp
mov r11, 0xffffffffffffffff 
mov rdx, r11
mov [ rsp + 0x10 ], r15
mulx r15, r11, r10
adox r12, rdi
adox r13, r8
mov rdi, 0xfffffffefffffc2f 
mov rdx, rdi
mulx r8, rdi, r10
clc
adcx rdi, rbp
mov rdi, r11
seto bpl
mov r10, -0x2 
inc r10
adox rdi, r8
mov r8, r11
adox r8, r15
adox r11, r15
adcx rdi, rbx
mov rbx, 0x0 
adox r15, rbx
adcx r8, r12
adcx r11, r13
inc r10
mov rbx, -0x1 
movzx rcx, cl
movzx rbp, bpl
adox rbp, rbx
adox r9, rcx
adcx r15, r9
setc cl
clc
adcx rdi, [ rsp - 0x38 ]
adcx r14, r8
adcx r11, [ rsp - 0x8 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rbp, r12, rdi
movzx rbp, cl
adox rbp, r10
mov r13, 0xfffffffefffffc2f 
mov rdx, r12
mulx r8, r12, r13
mov r9, 0xffffffffffffffff 
mulx r10, rcx, r9
adcx r15, [ rsp - 0x10 ]
adcx rbp, [ rsp - 0x18 ]
mov rdx, rcx
inc rbx
adox rdx, r8
setc r8b
clc
adcx r12, rdi
adcx rdx, r14
mov r12, rcx
adox r12, r10
adox rcx, r10
adox r10, rbx
adcx r12, r11
mov rdi, -0x3 
inc rdi
adox rdx, [ rsp - 0x20 ]
adcx rcx, r15
adox r12, [ rsp - 0x28 ]
adox rcx, [ rsp + 0x0 ]
adcx r10, rbp
movzx r14, r8b
adcx r14, rbx
mov r11, 0xd838091dd2253531 
mulx r8, r15, r11
adox r10, [ rsp + 0x10 ]
xchg rdx, r13
mulx rbp, r8, r15
mov rdx, r9
mulx rbx, r9, r15
adox r14, [ rsp + 0x8 ]
mov r15, r9
clc
adcx r15, rbp
seto bpl
inc rdi
adox r8, r13
adox r15, r12
mov r8, r9
adcx r8, rbx
adcx r9, rbx
adox r8, rcx
mov r13, 0x0 
adcx rbx, r13
adox r9, r10
adox rbx, r14
movzx r12, bpl
adox r12, r13
mov rcx, r15
mov r10, 0xfffffffefffffc2f 
sub rcx, r10
mov rbp, r8
sbb rbp, rdx
mov r14, r9
sbb r14, rdx
mov r13, rbx
sbb r13, rdx
sbb r12, 0x00000000
cmovc r13, rbx
cmovc rbp, r8
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rbp
cmovc r14, r9
mov [ r12 + 0x10 ], r14
cmovc rcx, r15
mov [ r12 + 0x18 ], r13
mov [ r12 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.7309
; seed 1545218475417043 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2175709 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=92, initial num_batches=31): 128506 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05906396489604079
; number reverted permutation / tried permutation: 65874 / 90231 =73.006%
; number reverted decision / tried decision: 60420 / 89768 =67.307%
; validated in 3.909s
