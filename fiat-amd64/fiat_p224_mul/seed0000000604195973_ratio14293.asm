SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 160
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
test al, al
adox r10, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mulx r14, rbx, [ rax + 0x18 ]
adox rbp, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r15
mulx r15, r11, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], rdi
mulx rdi, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], r10
mulx r10, rbp, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r14
mulx r14, r10, [ rsi + 0x10 ]
adox r10, r12
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x10 ], r10
mulx r10, r12, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r9
mov [ rsp + 0x0 ], r10
mulx r10, r9, [ rax + 0x8 ]
adcx r9, rdi
adcx rcx, r10
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rax + 0x8 ]
mulx r10, rdi, [ rsi + 0x8 ]
adcx r11, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x8 ], r14
mulx r14, r8, [ rsi + 0x8 ]
adc r15, 0x0
test al, al
adox rdi, r14
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x10 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
adox r14, r10
mov rdx, rbp
adcx rdx, r13
adox rbx, rdi
adcx r12, r9
mov rdx, 0xffffffffffffffff 
mulx r9, r13, rbp
seto r10b
mov rdi, -0x2 
inc rdi
adox r13, [ rsp + 0x0 ]
mov rdi, 0xffffffff 
mov rdx, rdi
mov byte [ rsp + 0x18 ], r10b
mulx r10, rdi, rbp
adox rdi, r9
mov rbp, 0x0 
adox r10, rbp
mov r9, -0x3 
inc r9
adox r8, r12
adcx r13, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, r8
mulx r12, r8, rcx
adcx rdi, r11
adcx r10, r15
adox r13, [ rsp + 0x10 ]
adox r14, rdi
adox rbx, r10
xchg rdx, r8
mulx r11, r12, rcx
mov r15, 0xffffffff00000000 
mulx r10, rdi, r15
setc r9b
clc
adcx r12, r10
mov r10, 0xffffffff 
mulx r15, rbp, r10
adcx rbp, r11
seto r11b
mov r10, -0x2 
inc r10
adox rdx, r8
adox rdi, r13
mov rdx, 0x0 
adcx r15, rdx
adox r12, r14
adox rbp, rbx
clc
adcx rdi, [ rsp - 0x8 ]
mov rdx, rdi
mulx r8, rdi, rcx
xchg rdx, rcx
mulx r13, r8, rdi
movzx r14, byte [ rsp + 0x18 ]
mov rbx, [ rsp - 0x18 ]
lea r14, [ r14 + rbx ]
adcx r12, [ rsp - 0x20 ]
setc bl
clc
movzx r9, r9b
movzx r11, r11b
adcx r11, r10
adcx r14, r9
adox r15, r14
setc r9b
clc
movzx rbx, bl
adcx rbx, r10
adcx rbp, [ rsp - 0x28 ]
movzx r11, r9b
mov rbx, 0x0 
adox r11, rbx
mov r14, 0xffffffff00000000 
mov rdx, r14
mulx r9, r14, rdi
adcx r15, [ rsp - 0x10 ]
mov r10, rdi
mov rdx, -0x3 
inc rdx
adox r10, rcx
adcx r11, [ rsp + 0x8 ]
adox r14, r12
setc r10b
clc
adcx r8, r9
mov rcx, 0xffffffff 
mov rdx, rcx
mulx r12, rcx, rdi
adcx rcx, r13
adcx r12, rbx
adox r8, rbp
adox rcx, r15
adox r12, r11
mov rdx, [ rax + 0x10 ]
mulx r13, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r9, rbp, [ rsi + 0x18 ]
movzx rdx, r10b
adox rdx, rbx
mov r15, [ rsp - 0x30 ]
test al, al
adox r15, [ rsp - 0x38 ]
adcx r14, [ rsp - 0x40 ]
adcx r15, r8
adox rdi, [ rsp - 0x48 ]
adox rbp, r13
adox r9, rbx
mov r10, 0xffffffffffffffff 
xchg rdx, r10
mulx r8, r11, r14
mov r8, r11
mov r13, -0x3 
inc r13
adox r8, r14
adcx rdi, rcx
mov r8, 0xffffffff00000000 
mov rdx, r11
mulx rcx, r11, r8
adox r11, r15
adcx rbp, r12
adcx r9, r10
mov r12, 0xffffffffffffffff 
mulx r14, r10, r12
setc r15b
clc
adcx r10, rcx
mov rcx, 0xffffffff 
mulx r13, rbx, rcx
adcx rbx, r14
adox r10, rdi
adox rbx, rbp
mov rdx, 0x0 
adcx r13, rdx
adox r13, r9
movzx rdi, r15b
adox rdi, rdx
mov rbp, r11
sub rbp, 0x00000001
mov r15, r10
sbb r15, r8
mov r9, rbx
sbb r9, r12
mov r14, r13
sbb r14, rcx
sbb rdi, 0x00000000
cmovc r15, r10
cmovc r14, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], r14
cmovc rbp, r11
cmovc r9, rbx
mov [ rdi + 0x10 ], r9
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.4293
; seed 1047340286621555 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2191848 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=86, initial num_batches=31): 122927 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05608372478383537
; number reverted permutation / tried permutation: 72359 / 90102 =80.308%
; number reverted decision / tried decision: 47792 / 89897 =53.163%
; validated in 3.668s
