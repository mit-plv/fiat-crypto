SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbx
mov rdx, 0xffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], r13
mulx r13, r8, rdx
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rax
mulx rax, r12, rbx
test al, al
adox r8, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mulx r8, r10, [ rsi + 0x0 ]
adcx r11, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rax
mulx rax, rbp, [ rsi + 0x10 ]
adcx rbp, rcx
adcx r10, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rax
mov [ rsp - 0x8 ], rcx
mulx rcx, rax, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx r8, rdx
adox rax, r13
clc
adcx rdi, r15
adcx r9, rdx
clc
adcx r14, rbx
adcx rdi, r11
adcx r9, rbp
adcx r12, r10
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, [ rsi + 0x8 ]
adox r14, rcx
adcx r8, [ rsp - 0x18 ]
setc dl
clc
adcx rdi, [ rsp - 0x28 ]
mov r15, 0x0 
adox rbx, r15
mov r13, 0xffffffffffffffff 
xchg rdx, r13
mulx rbp, r11, rdi
adcx r9, [ rsp - 0x20 ]
adcx rax, r12
adcx r14, r8
movzx r10, r13b
adcx r10, rbx
mov rdx, [ rsi + 0x10 ]
mulx r12, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mulx r8, r13, rdi
mov rbx, -0x3 
inc rbx
adox r12, [ rsp - 0x30 ]
setc bl
clc
adcx r13, rbp
adcx r8, r15
clc
adcx r11, rdi
adcx r13, r9
adcx r8, rax
mov r11, 0xffffffff00000001 
mov rdx, rdi
mulx rbp, rdi, r11
adcx rdi, r14
adcx rbp, r10
movzx rdx, bl
adcx rdx, r15
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, rax, rdx
adox rax, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, rbx, [ rsi + 0x10 ]
adox rbx, r14
adox r10, r15
test al, al
adox rcx, r13
adox r12, r8
mov rdx, 0xffffffffffffffff 
mulx r8, r13, rcx
adox rax, rdi
adox rbx, rbp
adox r10, r9
adcx r13, rcx
mov r13, 0xffffffff 
mov rdx, rcx
mulx rdi, rcx, r13
seto bpl
mov r9, -0x3 
inc r9
adox rcx, r8
adox rdi, r15
adcx rcx, r12
adcx rdi, rax
mulx r12, r14, r11
adcx r14, rbx
mov rdx, [ rsi + 0x10 ]
mulx rax, r8, [ rsi + 0x18 ]
adcx r12, r10
movzx rdx, bpl
adc rdx, 0x0
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, [ rsi + 0x0 ]
test al, al
adox rbp, rcx
adcx r10, [ rsp - 0x8 ]
adcx r8, [ rsp - 0x10 ]
adox r10, rdi
adcx rax, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x48 ]
adcx rdx, r15
adox r8, r14
mov rcx, 0xffffffffffffffff 
xchg rdx, rbp
mulx r14, rdi, rcx
mulx r9, r15, r13
clc
adcx r15, r14
adox rax, r12
adox rbp, rbx
setc r12b
clc
adcx rdi, rdx
movzx rdi, r12b
lea rdi, [ rdi + r9 ]
mulx r14, rbx, r11
adcx r15, r10
adcx rdi, r8
adcx rbx, rax
adcx r14, rbp
setc dl
seto r10b
mov r8, r15
sub r8, rcx
movzx r9, dl
movzx r10, r10b
lea r9, [ r9 + r10 ]
mov r12, rdi
sbb r12, r13
mov rax, rbx
sbb rax, 0x00000000
mov r10, r14
sbb r10, r11
sbb r9, 0x00000000
cmovc r10, r14
cmovc rax, rbx
cmovc r12, rdi
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], r10
cmovc r8, r15
mov [ r9 + 0x8 ], r12
mov [ r9 + 0x10 ], rax
mov [ r9 + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.6335
; seed 2225525884668579 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1058020 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=131, initial num_batches=31): 73615 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06957807980945539
; number reverted permutation / tried permutation: 68721 / 90213 =76.176%
; number reverted decision / tried decision: 40834 / 89786 =45.479%
; validated in 1.55s
