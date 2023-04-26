SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rcx
mov rcx, rdi
test al, al
adox rcx, r15
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r8
mulx r8, r15, [ rsi + 0x0 ]
adcx r15, r11
mov rdx, rdi
adox rdx, r9
adcx r12, r8
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbp
mulx rbp, r8, [ rax + 0x18 ]
adox rdi, r9
mov rdx, 0x0 
adox r9, rdx
mov [ rsp - 0x30 ], rbx
mov rbx, -0x3 
inc rbx
adox r14, r10
adox rcx, r15
adcx r8, r13
adcx rbp, rdx
adox r11, r12
adox rdi, r8
mov rdx, [ rsi + 0x8 ]
mulx r10, r14, [ rax + 0x8 ]
adox r9, rbp
mov rdx, [ rax + 0x10 ]
mulx r15, r13, [ rsi + 0x8 ]
clc
adcx rcx, [ rsp - 0x30 ]
seto dl
inc rbx
adox r14, [ rsp - 0x38 ]
mov r12, 0xd838091dd2253531 
xchg rdx, rcx
mulx rbp, r8, r12
adcx r14, r11
adox r13, r10
adcx r13, rdi
mov rbp, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r11, [ rsi + 0x8 ]
adox r11, r15
adcx r11, r9
mov rdx, 0xfffffffefffffc2f 
mulx r9, r10, r8
mov r15, 0x0 
adox rdi, r15
mov rbx, -0x3 
inc rbx
adox r10, rbp
mov r10, 0xffffffffffffffff 
mov rdx, r8
mulx rbp, r8, r10
movzx rdx, cl
adcx rdx, rdi
mov rcx, r8
setc dil
clc
adcx rcx, r9
mov r9, r8
adcx r9, rbp
adcx r8, rbp
adox rcx, r14
adox r9, r13
adcx rbp, r15
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mulx r15, r13, [ rsi + 0x10 ]
adox r8, r11
adox rbp, r14
clc
adcx r13, rcx
movzx rdx, dil
mov r11, 0x0 
adox rdx, r11
xchg rdx, r13
mulx r14, rdi, r12
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, rcx, [ rsi + 0x10 ]
inc rbx
adox rcx, r15
mov rdx, rdi
mulx r15, rdi, r10
adcx rcx, r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r10, rbx, [ rax + 0x10 ]
adox rbx, r11
adcx rbx, r8
adox r10, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x48 ]
mov r8, 0x0 
adox rdx, r8
adcx r10, rbp
adcx rdx, r13
mov rbp, 0xfffffffefffffc2f 
xchg rdx, r9
mulx r11, r13, rbp
mov rdx, -0x3 
inc rdx
adox r13, r14
mov rdx, [ rax + 0x8 ]
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, rdi
setc bpl
clc
adcx rdx, r11
adox rdx, rcx
mov rcx, rdi
adcx rcx, r15
adcx rdi, r15
adcx r15, r8
adox rcx, rbx
adox rdi, r10
adox r15, r9
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, r10, [ rsi + 0x18 ]
clc
adcx r13, r9
movzx rdx, bpl
adox rdx, r8
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, r11, [ rsi + 0x18 ]
adcx r11, r14
mov rdx, -0x3 
inc rdx
adox r10, rbx
adox r13, rcx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, [ rax + 0x18 ]
adcx r14, r9
adcx rbx, r8
mov rdx, r12
mulx rcx, r12, r10
adox r11, rdi
adox r14, r15
adox rbx, rbp
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rdi, rcx, r12
mov r15, 0xfffffffefffffc2f 
mov rdx, r12
mulx rbp, r12, r15
mov r9, rcx
clc
adcx r9, rbp
seto dl
mov rbp, -0x3 
inc rbp
adox r12, r10
adox r9, r13
mov r12, rcx
adcx r12, rdi
adcx rcx, rdi
adox r12, r11
adox rcx, r14
adcx rdi, r8
adox rdi, rbx
movzx r10, dl
adox r10, r8
mov r13, r9
sub r13, r15
mov r11, r12
mov r14, 0xffffffffffffffff 
sbb r11, r14
mov rdx, rcx
sbb rdx, r14
mov rbx, rdi
sbb rbx, r14
sbb r10, 0x00000000
cmovc rbx, rdi
cmovc r13, r9
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rbx
cmovc rdx, rcx
cmovc r11, r12
mov [ r10 + 0x8 ], r11
mov [ r10 + 0x0 ], r13
mov [ r10 + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 2.0385
; seed 4073217700676317 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1160349 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=100, initial num_batches=31): 75249 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06485031658578583
; number reverted permutation / tried permutation: 65945 / 89795 =73.440%
; number reverted decision / tried decision: 45207 / 90204 =50.116%
; validated in 2.939s
