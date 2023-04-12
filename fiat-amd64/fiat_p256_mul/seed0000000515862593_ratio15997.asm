SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mulx r8, rcx, r10
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
mov [ rsp - 0x68 ], r13
xor r13, r13
adox rcx, r12
mov rdx, [ rax + 0x18 ]
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
adcx rdi, r11
mov rdx, 0x0 
adox r8, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x40 ], r15
mulx r15, r11, [ rsi + 0x0 ]
adcx r11, r9
adcx r12, r15
adc r13, 0x0
test al, al
adox rbp, r10
adox rcx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, [ rax + 0x18 ]
mov rdx, 0xffffffff00000001 
mulx r15, rdi, r10
adox r8, r11
mov rdx, [ rax + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
adox rdi, r12
adcx r10, rbx
adox r15, r13
mov rdx, [ rax + 0x10 ]
mulx r12, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r10
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r13
mov [ rsp - 0x28 ], r15
mulx r15, r13, [ rsi + 0x8 ]
adcx rbx, r11
adcx rbp, r12
seto dl
mov r11, -0x2 
inc r11
adox r13, rcx
mov rcx, 0x0 
adcx r9, rcx
mov r12b, dl
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x8 ]
clc
adcx rcx, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], rbp
mulx rbp, r9, [ rsi + 0x8 ]
adcx r14, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r14
mulx r14, r11, [ rax + 0x10 ]
adcx r10, [ rsp - 0x40 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
setc dl
clc
adcx r9, r15
adox r9, r8
adcx r11, rbp
adcx r10, r14
movzx r8, dl
lea r8, [ r8 + rcx ]
adox r11, rdi
mov rdi, 0x0 
adcx rbx, rdi
adox r10, [ rsp - 0x28 ]
movzx r15, r12b
adox r15, rbx
mov r12, 0xffffffffffffffff 
mov rdx, r13
mulx rcx, r13, r12
mov rbp, 0xffffffff 
mulx rbx, r14, rbp
mov rdi, 0xffffffff00000001 
mulx r12, rbp, rdi
clc
adcx r14, rcx
mov rcx, 0x0 
adcx rbx, rcx
clc
adcx r13, rdx
adcx r14, r9
seto r13b
mov rdx, -0x3 
inc rdx
adox r14, [ rsp - 0x48 ]
mov r9, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, r9
adcx rbx, r11
adcx rbp, r10
adox rbx, [ rsp - 0x38 ]
adcx r12, r15
movzx r11, r13b
mov r10, 0x0 
adcx r11, r10
mov r13, 0xffffffff 
mulx r10, r15, r13
adox rbp, [ rsp + 0x8 ]
adox r12, [ rsp - 0x10 ]
clc
adcx r15, rcx
adox r11, [ rsp - 0x18 ]
mov rcx, 0x0 
adcx r10, rcx
clc
adcx r14, rdx
adcx r15, rbx
mulx rbx, r14, rdi
adcx r10, rbp
adcx r14, r12
adcx rbx, r11
seto dl
adc dl, 0x0
movzx rdx, dl
adox r15, [ rsp - 0x30 ]
xchg rdx, r9
mulx r12, rbp, r15
mov rdx, r15
mulx r11, r15, r13
adcx r15, r12
adcx r11, rcx
adox r10, [ rsp - 0x20 ]
clc
adcx rbp, rdx
adox r14, [ rsp - 0x8 ]
adcx r15, r10
adox rbx, [ rsp + 0x0 ]
movzx rbp, r9b
adox rbp, r8
adcx r11, r14
mulx r9, r8, rdi
adcx r8, rbx
adcx r9, rbp
seto dl
adc dl, 0x0
movzx rdx, dl
mov r12, r15
mov r10, 0xffffffffffffffff 
sub r12, r10
mov r14, r11
sbb r14, r13
mov rbx, r8
sbb rbx, 0x00000000
mov rbp, r9
sbb rbp, rdi
movzx r13, dl
sbb r13, 0x00000000
cmovc rbx, r8
cmovc r12, r15
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rbx
mov [ r13 + 0x0 ], r12
cmovc r14, r11
mov [ r13 + 0x8 ], r14
cmovc rbp, r9
mov [ r13 + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5997
; seed 3963771298466728 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1964150 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=104, initial num_batches=31): 126459 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06438357559249548
; number reverted permutation / tried permutation: 63798 / 89991 =70.894%
; number reverted decision / tried decision: 55659 / 90008 =61.838%
; validated in 2.573s
