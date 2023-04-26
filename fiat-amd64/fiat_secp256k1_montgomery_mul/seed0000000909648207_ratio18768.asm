SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], r9
mulx r9, r12, [ rax + 0x8 ]
test al, al
adox r12, r11
adox rbx, r9
mov rdx, 0xffffffffffffffff 
mulx r9, r11, rcx
adcx r8, r15
mov rcx, r11
setc r15b
clc
adcx rcx, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r8
mulx r8, r13, [ rax + 0x18 ]
mov rdx, r11
adcx rdx, r9
adcx r11, r9
mov byte [ rsp - 0x28 ], r15b
mov r15, 0x0 
adcx r9, r15
clc
adcx rdi, r10
adox r13, rbp
adcx rcx, r12
adox r8, r15
adcx rdx, rbx
mov rdi, -0x3 
inc rdi
adox r14, rcx
mov r10, 0xd838091dd2253531 
xchg rdx, r10
mulx r12, rbp, r14
adcx r11, r13
adcx r9, r8
mov r12, 0xfffffffefffffc2f 
mov rdx, rbp
mulx rbx, rbp, r12
mov r13, 0xffffffffffffffff 
mulx r8, rcx, r13
mov rdx, rcx
setc dil
clc
adcx rdx, rbx
mov rbx, rcx
adcx rbx, r8
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r12, r13, [ rsi + 0x8 ]
adcx rcx, r8
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp - 0x20 ], dil
mov [ rsp - 0x18 ], rcx
mulx rcx, rdi, [ rax + 0x18 ]
setc dl
mov [ rsp - 0x10 ], rbx
movzx rbx, byte [ rsp - 0x28 ]
clc
mov [ rsp - 0x8 ], r15
mov r15, -0x1 
adcx rbx, r15
adcx r13, [ rsp - 0x38 ]
adcx rdi, r12
mov rbx, 0x0 
adcx rcx, rbx
adox r10, [ rsp - 0x30 ]
adox r13, r11
movzx r11, dl
lea r11, [ r11 + r8 ]
adox rdi, r9
clc
adcx rbp, r14
adcx r10, [ rsp - 0x8 ]
adcx r13, [ rsp - 0x10 ]
adcx rdi, [ rsp - 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r14, rbp, [ rsi + 0x10 ]
movzx rdx, byte [ rsp - 0x20 ]
adox rdx, rcx
adcx r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx rcx, r12, [ rsi + 0x10 ]
setc dl
clc
adcx r12, r8
seto r8b
mov r15, -0x3 
inc r15
adox r9, r10
mov r10, 0xd838091dd2253531 
xchg rdx, r10
mulx r15, rbx, r9
movzx r15, r10b
movzx r8, r8b
lea r15, [ r15 + r8 ]
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r10, r8, rbx
adcx rcx, [ rsp - 0x40 ]
adox r12, r13
adox rcx, rdi
adcx rbp, [ rsp - 0x48 ]
adox rbp, r11
mov r13, 0x0 
adcx r14, r13
mov rdi, 0xffffffffffffffff 
mov rdx, rbx
mulx r11, rbx, rdi
clc
adcx r8, r9
mov r8, rbx
seto r9b
mov rdx, -0x3 
inc rdx
adox r8, r10
adcx r8, r12
mov r10, rbx
adox r10, r11
adox rbx, r11
adcx r10, rcx
adcx rbx, rbp
mov rdx, [ rax + 0x0 ]
mulx rcx, r12, [ rsi + 0x18 ]
adox r11, r13
dec r13
movzx r9, r9b
adox r9, r13
adox r15, r14
adcx r11, r15
mov rdx, [ rax + 0x8 ]
mulx rbp, r9, [ rsi + 0x18 ]
setc dl
clc
adcx r9, rcx
movzx r14, dl
mov rcx, 0x0 
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x18 ]
inc r13
adox r12, r8
adox r9, r10
mov rdx, 0xd838091dd2253531 
mulx r10, r8, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, [ rax + 0x10 ]
adcx r10, rbp
adcx r15, r13
mov rdx, 0x0 
adcx rcx, rdx
adox r10, rbx
mov rbx, 0xfffffffefffffc2f 
mov rdx, r8
mulx rbp, r8, rbx
adox r15, r11
mulx r13, r11, rdi
mov rdx, r11
clc
adcx rdx, rbp
mov rbp, r11
adcx rbp, r13
adcx r11, r13
mov rdi, 0x0 
adcx r13, rdi
clc
adcx r8, r12
adcx rdx, r9
adcx rbp, r10
adox rcx, r14
adcx r11, r15
adcx r13, rcx
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov r14, rdx
sub r14, rbx
mov r12, rbp
mov r9, 0xffffffffffffffff 
sbb r12, r9
mov r10, r11
sbb r10, r9
mov r15, r13
sbb r15, r9
movzx rcx, r8b
sbb rcx, 0x00000000
cmovc r15, r13
cmovc r14, rdx
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], r15
cmovc r10, r11
cmovc r12, rbp
mov [ rcx + 0x8 ], r12
mov [ rcx + 0x10 ], r10
mov [ rcx + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.8768
; seed 4015315087792886 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1276838 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=102, initial num_batches=31): 78094 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06116202681937724
; number reverted permutation / tried permutation: 64762 / 90000 =71.958%
; number reverted decision / tried decision: 47857 / 89999 =53.175%
; validated in 2.814s
