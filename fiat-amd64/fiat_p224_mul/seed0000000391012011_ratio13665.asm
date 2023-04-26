SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 152
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rsi + 0x18 ]
mov rdx, r15
mov [ rsp - 0x40 ], r10
xor r10, r10
adox rdx, rbp
mov rdx, [ rax + 0x10 ]
mulx r10, rbp, [ rsi + 0x10 ]
adcx r13, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
adcx rbp, r14
adcx r11, r10
mov rdx, 0x0 
adcx rdi, rdx
mov r14, 0xffffffff00000000 
mov rdx, r14
mulx r10, r14, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r11
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], rbp
mov [ rsp - 0x18 ], r13
mulx r13, rbp, [ rsi + 0x0 ]
clc
adcx rcx, r12
adcx rbp, r8
adcx rdi, r13
mov rdx, 0x0 
adcx r11, rdx
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx r12, r15, r8
adox r14, rcx
clc
adcx r15, r10
adox r15, rbp
mov r10, 0xffffffff 
mulx rcx, r13, r10
adcx r13, r12
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rax + 0x0 ]
adox r13, rdi
clc
adcx rbp, r14
mov rdx, r8
mulx rdi, r8, rbp
adox rcx, r11
mulx r11, rdi, r8
mov rdx, [ rax + 0x8 ]
mulx r10, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], rdi
mulx rdi, r11, [ rax + 0x10 ]
seto dl
mov [ rsp + 0x0 ], rbx
mov rbx, -0x2 
inc rbx
adox r14, r12
adox r11, r10
adcx r14, r15
adox r9, rdi
adcx r11, r13
adcx r9, rcx
mov r15, [ rsp + 0x0 ]
mov r12, 0x0 
adox r15, r12
movzx r13, dl
adcx r13, r15
mov rdx, 0xffffffff00000000 
mulx r10, rcx, r8
mov rdi, r8
mov r15, -0x3 
inc r15
adox rdi, rbp
adox rcx, r14
mov rdi, 0xffffffff 
mov rdx, rdi
mulx rbp, rdi, r8
setc r8b
clc
adcx r10, [ rsp - 0x8 ]
adcx rdi, [ rsp - 0x10 ]
adox r10, r11
adox rdi, r9
adcx rbp, r12
adox rbp, r13
clc
adcx rcx, [ rsp - 0x48 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r11, r14, rcx
mov r11, r14
seto r9b
mov r13, -0x3 
inc r13
adox r11, rcx
adcx r10, [ rsp - 0x18 ]
mulx r13, r11, r14
adcx rdi, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov rcx, 0xffffffff00000000 
mov rdx, r14
mulx r12, r14, rcx
movzx r15, r9b
movzx r8, r8b
lea r15, [ r15 + r8 ]
adox r14, r10
seto r8b
inc rbx
adox r14, [ rsp - 0x38 ]
adcx r15, [ rsp - 0x30 ]
mov r9, 0xffffffffffffffff 
xchg rdx, r14
mulx rbx, r10, r9
setc bl
clc
adcx r11, r12
mov r12, 0xffffffff 
xchg rdx, r12
mulx rcx, r9, r14
adcx r9, r13
mov r14, 0x0 
adcx rcx, r14
mulx r14, r13, r10
clc
mov rdx, -0x1 
movzx r8, r8b
adcx r8, rdx
adcx rdi, r11
adcx r9, rbp
mov rdx, [ rax + 0x10 ]
mulx r8, rbp, [ rsi + 0x18 ]
adcx rcx, r15
mov rdx, [ rax + 0x18 ]
mulx r11, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r13
mulx r13, r14, [ rax + 0x8 ]
setc dl
clc
adcx r14, [ rsp - 0x40 ]
adcx rbp, r13
adox r14, rdi
adcx r15, r8
adox rbp, r9
adox r15, rcx
mov rdi, 0x0 
adcx r11, rdi
movzx r9, dl
movzx rbx, bl
lea r9, [ r9 + rbx ]
mov rbx, 0xffffffffffffffff 
mov rdx, rbx
mulx r8, rbx, r10
mov rcx, 0xffffffff00000000 
mov rdx, rcx
mulx r13, rcx, r10
clc
adcx rbx, r13
adcx r8, [ rsp + 0x10 ]
mov r13, [ rsp + 0x8 ]
adcx r13, rdi
clc
adcx r10, r12
adcx rcx, r14
adcx rbx, rbp
adox r11, r9
adcx r8, r15
adcx r13, r11
seto r10b
adc r10b, 0x0
movzx r10, r10b
mov r12, rcx
sub r12, 0x00000001
mov r14, rbx
sbb r14, rdx
mov rbp, r8
mov r15, 0xffffffffffffffff 
sbb rbp, r15
mov r9, r13
mov r11, 0xffffffff 
sbb r9, r11
movzx r11, r10b
sbb r11, 0x00000000
cmovc r9, r13
cmovc r14, rbx
cmovc r12, rcx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r12
mov [ r11 + 0x18 ], r9
cmovc rbp, r8
mov [ r11 + 0x10 ], rbp
mov [ r11 + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.3665
; seed 0685819763020572 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1031746 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=130, initial num_batches=31): 67540 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06546184816805686
; number reverted permutation / tried permutation: 67585 / 89902 =75.176%
; number reverted decision / tried decision: 52978 / 90097 =58.801%
; validated in 2.339s
