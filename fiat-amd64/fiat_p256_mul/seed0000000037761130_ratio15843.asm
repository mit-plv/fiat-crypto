SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 160
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov [ rsp - 0x78 ], rbp
mov rbp, 0xffffffffffffffff 
mov rdx, rcx
mov [ rsp - 0x70 ], r12
mulx r12, rcx, rbp
test al, al
adox r9, r12
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x58 ], r15
mulx rbp, r15, r12
adcx r10, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rax + 0x10 ]
adcx r14, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mulx r14, r11, [ rsi + 0x8 ]
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r13
mulx r13, r10, [ rsi + 0x18 ]
adcx r11, rdi
adc r14, 0x0
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r13
mulx r13, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r10
mulx r10, r8, [ rax + 0x10 ]
adox r8, r13
adcx rcx, r12
adcx r9, rdi
mov rdx, [ rsi + 0x0 ]
mulx r12, rcx, [ rax + 0x18 ]
adox rcx, r10
mov rdx, 0x0 
adox r12, rdx
adcx rbx, r8
adcx r15, rcx
adcx rbp, r12
mov r13, -0x3 
inc r13
adox r9, [ rsp - 0x38 ]
mov rdi, 0xffffffffffffffff 
mov rdx, r9
mulx r10, r9, rdi
adox rbx, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
adox r11, rbp
mov r8, 0xffffffff00000001 
mulx r12, rcx, r8
mov rbp, 0xffffffff 
mulx rdi, r13, rbp
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], r12
mulx r12, r8, [ rsi + 0x18 ]
setc dl
movzx rdx, dl
adox rdx, r14
clc
adcx r13, r10
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x10 ], r10
mov [ rsp - 0x8 ], r14
mulx r14, r10, [ rsi + 0x18 ]
seto dl
mov [ rsp + 0x0 ], rcx
mov rcx, -0x2 
inc rcx
adox r10, r12
mov r12, 0x0 
adcx rdi, r12
clc
adcx r9, rbp
adcx r13, rbx
adcx rdi, r15
adox r8, r14
adcx r11, [ rsp + 0x0 ]
mov r9, [ rsp - 0x8 ]
adcx r9, [ rsp - 0x20 ]
movzx rbp, dl
adcx rbp, r12
mov rdx, [ rax + 0x18 ]
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], rbp
mulx rbp, r10, [ rax + 0x0 ]
clc
adcx r14, rbp
adcx rcx, r12
seto dl
mov r12, -0x2 
inc r12
adox r10, r13
adox r14, rdi
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx rbp, rdi, r10
adox rcx, r11
adcx rbx, r8
adox rbx, r9
mov r11, 0xffffffff 
mov rdx, r10
mulx r9, r10, r11
mov r8, 0x0 
adcx r15, r8
clc
adcx r10, rbp
adcx r9, r8
adox r15, [ rsp + 0x18 ]
clc
adcx rdi, rdx
adcx r10, r14
adcx r9, rcx
seto dil
mov r14, -0x3 
inc r14
adox r10, [ rsp - 0x10 ]
xchg rdx, r10
mulx rcx, rbp, r11
mov r8, 0xffffffff00000001 
xchg rdx, r10
mulx r12, r14, r8
adcx r14, rbx
adox r9, [ rsp + 0x10 ]
adcx r12, r15
movzx rdx, dil
mov rbx, 0x0 
adcx rdx, rbx
mov rdi, [ rsp - 0x18 ]
clc
mov r15, -0x1 
movzx r13, r13b
adcx r13, r15
adcx rdi, [ rsp - 0x28 ]
adox r14, [ rsp + 0x8 ]
adox rdi, r12
mov r13, [ rsp - 0x30 ]
adcx r13, rbx
mov r12, 0xffffffffffffffff 
xchg rdx, r12
mulx r15, rbx, r10
clc
adcx rbp, r15
mov r15, 0x0 
adcx rcx, r15
adox r13, r12
clc
adcx rbx, r10
adcx rbp, r9
mov rdx, r10
mulx rbx, r10, r8
adcx rcx, r14
adcx r10, rdi
adcx rbx, r13
seto dl
adc dl, 0x0
movzx rdx, dl
mov r9, rbp
mov r12, 0xffffffffffffffff 
sub r9, r12
mov r14, rcx
sbb r14, r11
mov rdi, r10
sbb rdi, 0x00000000
mov r13, rbx
sbb r13, r8
movzx r11, dl
sbb r11, 0x00000000
cmovc r13, rbx
cmovc r14, rcx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], r14
mov [ r11 + 0x18 ], r13
cmovc rdi, r10
cmovc r9, rbp
mov [ r11 + 0x10 ], rdi
mov [ r11 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5843
; seed 1522505654171140 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1156285 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=125, initial num_batches=31): 75619 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06539823659391931
; number reverted permutation / tried permutation: 65443 / 90228 =72.531%
; number reverted decision / tried decision: 42402 / 89771 =47.234%
; validated in 1.773s
