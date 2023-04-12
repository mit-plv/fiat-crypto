SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
test al, al
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], rax
mulx rax, r11, r10
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], rbx
mulx rbx, rbp, r10
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r14
mulx r14, rcx, rdx
adox rcx, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r15, [ rsi + 0x8 ]
adcx rbp, rax
mov rdx, 0x0 
adox r14, rdx
mov rax, -0x3 
inc rax
adox r12, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rcx, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mulx r14, r13, [ rsi + 0x8 ]
adox r13, rax
clc
adcx r8, rdi
mov rdx, [ rsi + 0x0 ]
mulx rax, rdi, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r14, rdx
adcx rdi, r9
mov r9, -0x3 
inc r9
adox r11, r10
adox rbp, r8
adcx rax, [ rsp - 0x30 ]
mov r11, [ rsp - 0x38 ]
adcx r11, rdx
clc
adcx r15, rbp
mov r8, 0xffffffffffffffff 
mov rdx, r15
mulx rbp, r15, r8
adox rbx, rdi
mov rdi, 0xffffffff00000001 
xchg rdx, r10
mulx r8, r9, rdi
adox r9, rax
adox r8, r11
adcx r12, rbx
adcx rcx, r9
adcx r13, r8
mov rdx, r10
mulx rax, r10, rdi
mov r11, 0xffffffff 
mulx r9, rbx, r11
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rdi, [ rsi + 0x10 ]
setc dl
clc
adcx rbx, rbp
movzx rbp, dl
adox rbp, r14
mov r14, 0x0 
adcx r9, r14
clc
adcx r15, r8
adcx rbx, r12
adcx r9, rcx
adcx r10, r13
mov rdx, [ rsi + 0x8 ]
mulx r8, r15, [ rsi + 0x10 ]
adcx rax, rbp
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, rdx
setc dl
clc
adcx r15, r11
adcx r12, r8
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mulx rbp, r11, [ rsi + 0x10 ]
adcx r11, rcx
movzx rdx, r13b
adox rdx, r14
mov r8, -0x3 
inc r8
adox rdi, rbx
mov rbx, 0xffffffffffffffff 
xchg rdx, rbx
mulx rcx, r13, rdi
mov r14, 0xffffffff 
mov rdx, rdi
mulx r8, rdi, r14
adox r15, r9
setc r9b
clc
adcx rdi, rcx
adox r12, r10
mov r10, 0x0 
adcx r8, r10
clc
adcx r13, rdx
adcx rdi, r15
adcx r8, r12
adox r11, rax
movzx r13, r9b
lea r13, [ r13 + rbp ]
adox r13, rbx
mov rax, 0xffffffff00000001 
mulx r9, rbp, rax
adcx rbp, r11
adcx r9, r13
seto bl
mov rdx, -0x3 
inc rdx
adox rdi, [ rsp - 0x40 ]
movzx rcx, bl
adcx rcx, r10
adox r8, [ rsp - 0x48 ]
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r12, r15, rdi
mov rdx, rdi
mulx r11, rdi, rax
adox rbp, [ rsp - 0x28 ]
adox r9, [ rsp - 0x20 ]
adox rcx, [ rsp - 0x18 ]
mulx r13, rbx, r14
clc
adcx r15, rdx
seto r15b
mov rdx, -0x3 
inc rdx
adox rbx, r12
adox r13, r10
adcx rbx, r8
adcx r13, rbp
adcx rdi, r9
adcx r11, rcx
movzx r8, r15b
adc r8, 0x0
mov r12, rbx
mov rbp, 0xffffffffffffffff 
sub r12, rbp
mov r9, r13
sbb r9, r14
mov r15, rdi
sbb r15, 0x00000000
mov rcx, r11
sbb rcx, rax
sbb r8, 0x00000000
cmovc r15, rdi
cmovc rcx, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r15
cmovc r12, rbx
mov [ r8 + 0x0 ], r12
cmovc r9, r13
mov [ r8 + 0x18 ], rcx
mov [ r8 + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.4831
; seed 0692623435081629 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1676180 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=94, initial num_batches=31): 105655 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06303320645754036
; number reverted permutation / tried permutation: 73542 / 90256 =81.482%
; number reverted decision / tried decision: 38371 / 89743 =42.757%
; validated in 1.89s
