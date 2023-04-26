SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r13
mov rdi, 0xffffffff 
mov rdx, r15
mov [ rsp - 0x48 ], r10
mulx r10, r15, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rcx
mulx rcx, r8, [ rax + 0x8 ]
test al, al
adox r8, r11
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x30 ], r8
mulx r8, r11, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
adcx r9, r14
adcx r12, rbx
mov rdx, [ rsi + 0x0 ]
mulx r14, rbx, [ rax + 0x18 ]
adcx rbx, rbp
mov rdx, 0x0 
adcx r14, rdx
mov rbp, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp - 0x18 ], rcx
mulx rcx, rdi, rbp
clc
adcx r11, rcx
adcx r15, r8
mov r8, 0x0 
adcx r10, r8
clc
adcx rdx, r13
adcx rdi, r9
adcx r11, r12
adcx r15, rbx
adcx r10, r14
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x10 ]
adox r13, [ rsp - 0x18 ]
adox r9, [ rsp - 0x20 ]
mov rdx, [ rsp - 0x28 ]
adox rdx, r8
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, [ rax + 0x8 ]
mov rdx, -0x3 
inc rdx
adox rdi, [ rsp - 0x38 ]
setc cl
clc
adcx rbx, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, [ rax + 0x10 ]
adcx r8, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r12
mulx r12, r14, [ rax + 0x18 ]
adcx r14, rbp
adox rbx, r11
adox r8, r15
mov rdx, 0x0 
adcx r12, rdx
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r15, r11, rdi
adox r14, r10
mulx r10, r15, r11
mov rbp, 0xffffffff00000000 
mov rdx, r11
mov [ rsp - 0x8 ], r9
mulx r9, r11, rbp
clc
adcx r15, r9
movzx r9, cl
adox r9, r12
mov rcx, 0xffffffff 
mulx rbp, r12, rcx
adcx r12, r10
mov r10, 0x0 
adcx rbp, r10
clc
adcx rdx, rdi
adcx r11, rbx
adcx r15, r8
seto dl
mov rdi, -0x3 
inc rdi
adox r11, [ rsp - 0x48 ]
mov rbx, 0xffffffffffffffff 
xchg rdx, r11
mulx r10, r8, rbx
xchg rdx, r8
mulx rdi, r10, rbx
adcx r12, r14
adcx rbp, r9
adox r15, [ rsp - 0x30 ]
movzx r14, r11b
mov r9, 0x0 
adcx r14, r9
adox r13, r12
mulx r12, r11, rcx
mov r9, 0xffffffff00000000 
mulx rbx, rcx, r9
clc
adcx r10, rbx
adcx r11, rdi
adox rbp, [ rsp - 0x8 ]
adox r14, [ rsp - 0x10 ]
mov rdi, 0x0 
adcx r12, rdi
clc
adcx rdx, r8
adcx rcx, r15
adcx r10, r13
adcx r11, rbp
mov rdx, [ rax + 0x0 ]
mulx r15, r8, [ rsi + 0x18 ]
adcx r12, r14
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r14, rbp, [ rsi + 0x18 ]
seto dl
mov r9, -0x3 
inc r9
adox rbp, r15
mov r15b, dl
mov rdx, [ rsi + 0x18 ]
mulx r9, rdi, [ rax + 0x10 ]
adox rdi, r14
adox r13, r9
mov rdx, 0x0 
adox rbx, rdx
mov r14, -0x3 
inc r14
adox r8, rcx
mov rcx, 0xffffffffffffffff 
mov rdx, r8
mulx r9, r8, rcx
xchg rdx, rcx
mulx r14, r9, r8
adox rbp, r10
adox rdi, r11
adox r13, r12
movzx r10, r15b
mov r11, 0x0 
adcx r10, r11
mov r15, 0xffffffff00000000 
mov rdx, r15
mulx r12, r15, r8
mov rdx, r8
clc
adcx rdx, rcx
adcx r15, rbp
adox rbx, r10
mov rdx, 0xffffffff 
mulx rbp, rcx, r8
seto r8b
mov r10, -0x3 
inc r10
adox r9, r12
adox rcx, r14
adox rbp, r11
adcx r9, rdi
adcx rcx, r13
adcx rbp, rbx
movzx r14, r8b
adc r14, 0x0
mov rdi, r15
sub rdi, 0x00000001
mov r13, r9
mov r12, 0xffffffff00000000 
sbb r13, r12
mov r8, rcx
mov rbx, 0xffffffffffffffff 
sbb r8, rbx
mov r11, rbp
sbb r11, rdx
sbb r14, 0x00000000
cmovc rdi, r15
cmovc r13, r9
cmovc r11, rbp
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x18 ], r11
mov [ r14 + 0x0 ], rdi
cmovc r8, rcx
mov [ r14 + 0x10 ], r8
mov [ r14 + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5833
; seed 2538669239349430 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1376660 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 81764 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05939302369503
; number reverted permutation / tried permutation: 66670 / 89868 =74.187%
; number reverted decision / tried decision: 47078 / 90131 =52.233%
; validated in 2.79s
