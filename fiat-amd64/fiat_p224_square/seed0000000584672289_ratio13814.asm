SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffff 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov [ rsp - 0x58 ], r15
mov r15, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbx
test al, al
adox r15, r12
adox r13, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r12, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r14, rdx
adcx r11, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x10 ]
adcx rdi, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rdi
mulx rdi, rcx, [ rsi + 0x8 ]
adcx rcx, r14
mov rdx, -0x2 
inc rdx
adox rbx, rax
mov rdx, [ rsi + 0x0 ]
mulx rax, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r14, r10
adox rbp, r14
adcx r8, rcx
adox r15, r8
adcx rbx, r9
adcx rax, rdx
clc
adcx r12, rbp
adcx r11, r15
adox r13, rbx
adox rax, [ rsp - 0x48 ]
adcx r13, [ rsp - 0x40 ]
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, r12
mov r9, 0xffffffff00000000 
mov rdx, r10
mulx rcx, r10, r9
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rsi + 0x10 ]
adcx rax, [ rsp - 0x38 ]
setc dl
movzx rdx, dl
adox rdx, rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r15
mulx r15, r9, rdx
clc
adcx rbp, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
adcx r9, r8
adcx rbx, r15
mov rdx, r14
setc r8b
clc
adcx rdx, r12
adcx r10, r11
mov rdx, 0xffffffffffffffff 
mulx r11, r12, r14
mov r15, 0xffffffff 
mov rdx, r15
mov [ rsp - 0x20 ], rbx
mulx rbx, r15, r14
seto r14b
mov rdx, -0x2 
inc rdx
adox r12, rcx
adox r15, r11
mov rcx, 0x0 
adox rbx, rcx
adcx r12, r13
adcx r15, rax
adcx rbx, rdi
movzx r13, r14b
adc r13, 0x0
xor rax, rax
adox r10, [ rsp - 0x30 ]
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rdi, rcx, r10
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mulx r14, rcx, rdi
mov r11, 0xffffffffffffffff 
mulx rdi, rax, r11
adcx rax, r14
movzx r14, r8b
lea r14, [ r14 + rbp ]
mov rbp, 0xffffffff 
mulx r11, r8, rbp
adcx r8, rdi
mov rdi, 0x0 
adcx r11, rdi
adox r12, [ rsp - 0x28 ]
adox r9, r15
clc
adcx rdx, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r15, [ rsi + 0x18 ]
adox rbx, [ rsp - 0x20 ]
adcx rcx, r12
adcx rax, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, rdx
adcx r8, rbx
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbx, [ rsi + 0x8 ]
adox r14, r13
adcx r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r13, [ rsi + 0x18 ]
setc dl
clc
adcx rbx, r10
adcx r13, rdi
adcx r12, r14
movzx r10, dl
mov rdi, 0x0 
adox r10, rdi
adc r9, 0x0
xor rdx, rdx
adox r15, rcx
adox rbx, rax
mov rdi, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, rdi
adox r13, r8
adox r12, r11
mov rcx, 0xffffffff00000000 
xchg rdx, r15
mulx r8, rax, rcx
mulx r14, r11, rdi
adox r9, r10
mov r10, rdx
adcx r10, r15
seto r10b
mov r15, -0x2 
inc r15
adox r11, r8
adcx rax, rbx
adcx r11, r13
mulx r13, rbx, rbp
adox rbx, r14
mov rdx, 0x0 
adox r13, rdx
adcx rbx, r12
adcx r13, r9
movzx r12, r10b
adc r12, 0x0
mov r8, rax
sub r8, 0x00000001
mov r14, r11
sbb r14, rcx
mov r10, rbx
sbb r10, rdi
mov r9, r13
sbb r9, rbp
sbb r12, 0x00000000
cmovc r14, r11
cmovc r9, r13
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r14
cmovc r8, rax
mov [ r12 + 0x0 ], r8
cmovc r10, rbx
mov [ r12 + 0x10 ], r10
mov [ r12 + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3814
; seed 2737466602650696 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1200889 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=154, initial num_batches=31): 86491 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0720224766818582
; number reverted permutation / tried permutation: 70548 / 90214 =78.201%
; number reverted decision / tried decision: 45514 / 89785 =50.692%
; validated in 2.683s
