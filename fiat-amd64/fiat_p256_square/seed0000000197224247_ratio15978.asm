SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov [ rsp - 0x70 ], r12
mov r12, 0xffffffff 
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
xor r14, r14
adox r12, rbp
mov rdx, [ rsi + 0x8 ]
mulx r14, rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], rbp
mulx rbp, r14, [ rsi + 0x8 ]
adcx r15, r10
adcx r8, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r10, [ rsi + 0x18 ]
adcx r10, r9
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx rbx, rax
adcx r12, r15
adox r13, rdx
adcx r13, r8
mov rbx, 0xffffffff00000001 
mov rdx, rax
mulx r9, rax, rbx
adcx rax, r10
mov rdx, -0x2 
inc rdx
adox r11, r12
mov r15, 0xffffffffffffffff 
mov rdx, r11
mulx r8, r11, r15
mov r10, 0xffffffff 
mulx r15, r12, r10
adcx r9, rdi
setc dil
clc
adcx r12, r8
mov r8, 0x0 
adcx r15, r8
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r10, [ rsi + 0x10 ]
clc
adcx rcx, [ rsp - 0x20 ]
adcx r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
adcx rbp, rbx
adox rcx, r13
mov rdx, 0x0 
adcx r14, rdx
adox r10, rax
adox rbp, r9
movzx r13, dil
adox r13, r14
clc
adcx r11, r8
adcx r12, rcx
mov rdx, [ rsi + 0x0 ]
mulx rax, r11, [ rsi + 0x10 ]
seto dl
mov rdi, -0x2 
inc rdi
adox r11, r12
adcx r15, r10
mov r9, 0xffffffff00000001 
xchg rdx, r9
mulx rcx, rbx, r8
adcx rbx, rbp
adcx rcx, r13
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, rdx
setc dl
clc
adcx rax, [ rsp - 0x10 ]
movzx r10, dl
movzx r9, r9b
lea r10, [ r10 + r9 ]
mov rbp, 0xffffffff 
mov rdx, r11
mulx r9, r11, rbp
adcx r8, [ rsp - 0x18 ]
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r12, [ rsi + 0x10 ]
adcx r12, r14
adox rax, r15
adox r8, rbx
mov rdx, 0xffffffff00000001 
mulx rbx, r15, r13
adox r12, rcx
mov rcx, 0x0 
adcx rdi, rcx
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, r13
clc
adcx r11, rcx
mov rcx, 0x0 
adcx r9, rcx
clc
adcx r14, r13
adcx r11, rax
mov rdx, [ rsi + 0x18 ]
mulx r13, r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, [ rsi + 0x18 ]
adcx r9, r8
adox rdi, r10
adcx r15, r12
setc dl
clc
adcx rcx, [ rsp - 0x30 ]
mov r10, [ rsp - 0x38 ]
adcx r10, [ rsp - 0x40 ]
seto r8b
mov r12, -0x1 
inc r12
mov r12, -0x1 
movzx rdx, dl
adox rdx, r12
adox rdi, rbx
adcx r14, [ rsp - 0x48 ]
movzx rbx, r8b
mov rdx, 0x0 
adox rbx, rdx
adc r13, 0x0
test al, al
adox rax, r11
adox rcx, r9
adox r10, r15
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx r9, r11, rax
mov rdx, rbp
mulx r8, rbp, rax
adcx rbp, r9
adox r14, rdi
adox r13, rbx
seto r15b
inc r12
adox r11, rax
adox rbp, rcx
mov r11, 0xffffffff00000001 
mov rdx, r11
mulx rdi, r11, rax
adcx r8, r12
adox r8, r10
adox r11, r14
adox rdi, r13
movzx rbx, r15b
adox rbx, r12
mov rax, rbp
mov rcx, 0xffffffffffffffff 
sub rax, rcx
mov r10, r8
mov r9, 0xffffffff 
sbb r10, r9
mov r14, r11
sbb r14, 0x00000000
mov r15, rdi
sbb r15, rdx
sbb rbx, 0x00000000
cmovc r15, rdi
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], r15
cmovc rax, rbp
mov [ rbx + 0x0 ], rax
cmovc r14, r11
mov [ rbx + 0x10 ], r14
cmovc r10, r8
mov [ rbx + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5978
; seed 2828680055068049 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1100754 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 80572 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0731970994427456
; number reverted permutation / tried permutation: 68261 / 90056 =75.798%
; number reverted decision / tried decision: 42278 / 89943 =47.005%
; validated in 1.51s
