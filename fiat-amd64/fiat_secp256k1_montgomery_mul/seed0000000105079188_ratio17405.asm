SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov r14, 0xffffffffffffffff 
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, r14
mov r14, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r12
mulx r12, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], r9
mulx r9, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r11
mov r11, 0xfffffffefffffc2f 
mov rdx, r11
mov [ rsp - 0x20 ], rbp
mulx rbp, r11, r14
adcx r11, r10
adox rcx, r9
mov rdx, [ rax + 0x18 ]
mulx r10, r11, [ rsi + 0x0 ]
adox r11, r8
mov rdx, 0x0 
adox r10, rdx
mov r8, r13
mov r14, -0x3 
inc r14
adox r8, rbp
mov r9, r13
adox r9, r15
adcx r8, r12
adcx r9, rcx
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x8 ]
adox r13, r15
adcx r13, r11
seto dl
inc r14
adox r12, r8
mov rcx, 0xd838091dd2253531 
xchg rdx, r12
mulx r8, r11, rcx
movzx r8, r12b
lea r8, [ r8 + r15 ]
adcx r8, r10
setc r15b
clc
adcx rdi, rbp
adcx rbx, [ rsp - 0x20 ]
mov r10, 0xfffffffefffffc2f 
xchg rdx, r11
mulx r12, rbp, r10
adox rdi, r9
adox rbx, r13
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rax + 0x18 ]
adcx r13, [ rsp - 0x38 ]
adox r13, r8
mov rdx, 0x0 
adcx r14, rdx
mov r8, 0xffffffffffffffff 
mov rdx, r9
mulx rcx, r9, r8
mov rdx, r9
clc
adcx rdx, r12
mov r12, r9
adcx r12, rcx
movzx r8, r15b
adox r8, r14
mov r15, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, r14, [ rsi + 0x10 ]
adcx r9, rcx
seto dl
mov [ rsp - 0x18 ], r10
mov r10, -0x2 
inc r10
adox rbp, r11
adox r15, rdi
adox r12, rbx
adox r9, r13
mov rbp, 0x0 
adcx rcx, rbp
adox rcx, r8
mov r11b, dl
mov rdx, [ rax + 0x8 ]
mulx rbx, rdi, [ rsi + 0x10 ]
movzx rdx, r11b
adox rdx, rbp
test al, al
adox r14, r15
adcx rdi, [ rsp - 0x18 ]
mov r13, 0xd838091dd2253531 
xchg rdx, r14
mulx r8, r11, r13
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r15, [ rax + 0x18 ]
adcx rbx, [ rsp - 0x40 ]
adox rdi, r12
adox rbx, r9
adcx r15, [ rsp - 0x48 ]
mov rdx, 0x0 
adcx rbp, rdx
adox r15, rcx
adox rbp, r14
mov r12, 0xfffffffefffffc2f 
mov rdx, r12
mulx r9, r12, r11
mov rcx, 0xffffffffffffffff 
mov rdx, r11
mulx r14, r11, rcx
clc
adcx r12, r8
mov r12, r11
seto r8b
inc r10
adox r12, r9
mov rdx, r11
adox rdx, r14
adox r11, r14
adcx r12, rdi
adcx rdx, rbx
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, rbx, [ rsi + 0x18 ]
adox r14, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rax + 0x8 ]
adcx r11, r15
adcx r14, rbp
movzx rdx, r8b
adc rdx, 0x0
test al, al
adox rbx, r12
xchg rdx, r13
mulx r8, r15, rbx
mov r8, 0xfffffffefffffc2f 
mov rdx, r15
mulx rbp, r15, r8
mov r12, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r13
mulx r13, r8, r12
adcx r10, r9
adcx rcx, [ rsp - 0x28 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r9, [ rsi + 0x18 ]
adcx r9, [ rsp - 0x30 ]
adox r10, rdi
mov rdx, 0x0 
adcx r12, rdx
adox rcx, r11
mov rdi, r8
clc
adcx rdi, rbp
mov r11, r8
adcx r11, r13
adcx r8, r13
adcx r13, rdx
clc
adcx r15, rbx
adcx rdi, r10
adox r9, r14
adcx r11, rcx
adcx r8, r9
adox r12, [ rsp - 0x10 ]
adcx r13, r12
seto r15b
adc r15b, 0x0
movzx r15, r15b
mov r14, rdi
mov rbx, 0xfffffffefffffc2f 
sub r14, rbx
mov rbp, r11
mov r10, 0xffffffffffffffff 
sbb rbp, r10
mov rcx, r8
sbb rcx, r10
mov r9, r13
sbb r9, r10
movzx r12, r15b
sbb r12, 0x00000000
cmovc rbp, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rbp
cmovc rcx, r8
mov [ r12 + 0x10 ], rcx
cmovc r9, r13
mov [ r12 + 0x18 ], r9
cmovc r14, rdi
mov [ r12 + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.7405
; seed 2026121181737461 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 942629 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=107, initial num_batches=31): 63441 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06730219418244081
; number reverted permutation / tried permutation: 66187 / 90156 =73.414%
; number reverted decision / tried decision: 49978 / 89843 =55.628%
; validated in 2.306s
