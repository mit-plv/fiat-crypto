SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 168
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], rdi
mulx rdi, rcx, r10
mov [ rsp - 0x38 ], r13
mulx r13, rdi, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r14
mulx r14, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r8
mulx r8, rbx, rcx
mov rdx, rcx
mov [ rsp + 0x0 ], r9
xor r9, r9
adox rdx, r10
adcx rdi, r8
mov rdx, 0xffffffff 
mulx r8, r10, rcx
adcx r10, r13
adcx r8, r9
clc
adcx r15, r11
adcx rbp, r14
adox rbx, r15
adcx r12, [ rsp + 0x0 ]
mov r11, [ rsp - 0x18 ]
adcx r11, r9
adox rdi, rbp
mov rdx, [ rax + 0x8 ]
mulx r13, rcx, [ rsi + 0x10 ]
clc
adcx rcx, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, r14, [ rax + 0x10 ]
adox r10, r12
adcx r14, r13
adox r8, r11
mov rdx, [ rax + 0x18 ]
mulx r12, rbp, [ rsi + 0x10 ]
adcx rbp, r15
adcx r12, r9
mov rdx, [ rsp - 0x28 ]
clc
adcx rdx, [ rsp - 0x8 ]
mov r11, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x30 ]
seto r13b
mov r15, -0x3 
inc r15
adox rbx, [ rsp - 0x38 ]
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r12
mulx r12, r15, [ rsi + 0x8 ]
adcx r15, [ rsp - 0x40 ]
mov rdx, 0x0 
adcx r12, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], rbp
mov [ rsp + 0x18 ], r14
mulx r14, rbp, rbx
mov r14, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp + 0x20 ], rcx
mulx rcx, rbp, r14
adox r9, rdi
adox r11, r10
adox r15, r8
movzx rdi, r13b
adox rdi, r12
mov r10, 0xffffffffffffffff 
mulx r8, r13, r10
mov r12, rdx
clc
adcx r12, rbx
adcx rbp, r9
setc r12b
clc
adcx r13, rcx
seto bl
mov rcx, -0x1 
inc rcx
mov r9, -0x1 
movzx r12, r12b
adox r12, r9
adox r11, r13
mov r12, 0xffffffff 
mulx rcx, r13, r12
adcx r13, r8
mov rdx, 0x0 
adcx rcx, rdx
adox r13, r15
adox rcx, rdi
clc
adcx rbp, [ rsp - 0x48 ]
movzx r15, bl
adox r15, rdx
adcx r11, [ rsp + 0x20 ]
mov rdx, rbp
mulx rbx, rbp, r10
xchg rdx, r10
mulx rdi, rbx, rbp
mov r8, rbp
inc r9
adox r8, r10
adcx r13, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x10 ]
mov rdx, r14
mulx r14, r8, rbp
adox r8, r11
adcx r15, [ rsp + 0x8 ]
mov rdx, r12
mulx r10, r12, rbp
setc r11b
clc
adcx rbx, r14
adcx r12, rdi
adox rbx, r13
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r14, r13, [ rsi + 0x18 ]
adox r12, rcx
adcx r10, r9
adox r10, r15
clc
adcx rbp, r14
mov rdx, [ rax + 0x10 ]
mulx r15, rcx, [ rsi + 0x18 ]
adcx rcx, rdi
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, [ rax + 0x18 ]
adcx rdi, r15
movzx rdx, r11b
adox rdx, r9
adc r14, 0x0
test al, al
adox r13, r8
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mulx r15, r11, r13
adox rbp, rbx
mov r15, 0xffffffff00000000 
mov rdx, r15
mulx rbx, r15, r11
adox rcx, r12
mov r12, r11
adcx r12, r13
adox rdi, r10
mov r12, 0xffffffffffffffff 
mov rdx, r12
mulx r10, r12, r11
adox r14, r8
adcx r15, rbp
setc r8b
clc
adcx r12, rbx
mov r13, 0xffffffff 
mov rdx, r13
mulx rbp, r13, r11
adcx r13, r10
seto r11b
dec r9
movzx r8, r8b
adox r8, r9
adox rcx, r12
adox r13, rdi
mov rbx, 0x0 
adcx rbp, rbx
adox rbp, r14
movzx rdi, r11b
adox rdi, rbx
mov r10, r15
sub r10, 0x00000001
mov r11, rcx
mov r14, 0xffffffff00000000 
sbb r11, r14
mov r8, r13
mov r12, 0xffffffffffffffff 
sbb r8, r12
mov rbx, rbp
sbb rbx, rdx
sbb rdi, 0x00000000
cmovc r8, r13
cmovc r11, rcx
cmovc rbx, rbp
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], rbx
cmovc r10, r15
mov [ rdi + 0x0 ], r10
mov [ rdi + 0x10 ], r8
mov [ rdi + 0x8 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.3924
; seed 3268252909521610 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1028793 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=131, initial num_batches=31): 68048 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06614352935916167
; number reverted permutation / tried permutation: 67324 / 89784 =74.984%
; number reverted decision / tried decision: 50618 / 90215 =56.108%
; validated in 2.257s
