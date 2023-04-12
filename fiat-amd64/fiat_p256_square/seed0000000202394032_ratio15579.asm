SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 168
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
add r8, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
adcx r11, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], rax
mulx rax, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], r8
mulx r8, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
adcx r9, rcx
mov rdx, -0x2 
inc rdx
adox r11, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
adox r15, r8
mov rdx, 0x0 
adcx rax, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r15
mulx r15, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r8
mulx r8, r11, [ rsi + 0x10 ]
clc
adcx r13, r15
adcx rbx, r14
adcx r11, rbp
adox r10, rdi
mov rdx, 0xffffffff 
mulx r14, rbp, r12
mov rdi, 0x0 
adcx r8, rdi
adox rcx, rdi
xor r15, r15
adox rbp, [ rsp - 0x28 ]
adox r14, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], r11
mulx r11, r8, [ rsi + 0x8 ]
mov rdx, r12
adcx rdx, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rbx
mov [ rsp + 0x20 ], r13
mulx r13, rbx, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rdi, r10
adox rbx, r15
adox r8, r13
adcx rbp, [ rsp - 0x38 ]
mov r15, 0x0 
adox r11, r15
adcx r14, [ rsp - 0x40 ]
mov r10, 0xffffffff00000001 
mov rdx, r12
mulx r13, r12, r10
adcx r12, r9
adcx r13, rax
mov rdx, -0x3 
inc rdx
adox rcx, rbp
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rax, r9, rcx
adox rdi, r14
adox rbx, r12
adox r8, r13
mov rbp, 0xffffffff 
mov rdx, rcx
mulx r14, rcx, rbp
seto r12b
mov r13, -0x3 
inc r13
adox rcx, rax
movzx rax, r12b
adcx rax, r11
setc r11b
clc
adcx r9, rdx
adcx rcx, rdi
adox r14, r15
adcx r14, rbx
mov r9, -0x3 
inc r9
adox rcx, [ rsp - 0x10 ]
adox r14, [ rsp + 0x20 ]
mulx rdi, r9, r10
mov rdx, rcx
mulx rbx, rcx, r10
adcx r9, r8
adcx rdi, rax
adox r9, [ rsp + 0x18 ]
movzx r12, r11b
adcx r12, r15
adox rdi, [ rsp + 0x10 ]
mov r8, 0xffffffffffffffff 
mulx rax, r11, r8
mulx r13, r15, rbp
clc
adcx r15, rax
mov rax, 0x0 
adcx r13, rax
clc
adcx r11, rdx
adcx r15, r14
adox r12, [ rsp + 0x8 ]
seto r11b
mov rdx, -0x3 
inc rdx
adox r15, [ rsp - 0x48 ]
adcx r13, r9
adox r13, [ rsp - 0x18 ]
adcx rcx, rdi
adox rcx, [ rsp - 0x20 ]
adcx rbx, r12
movzx r14, r11b
adcx r14, rax
adox rbx, [ rsp + 0x0 ]
mov rdx, r15
mulx r9, r15, r8
adox r14, [ rsp - 0x8 ]
mulx r11, rdi, rbp
clc
adcx rdi, r9
adcx r11, rax
clc
adcx r15, rdx
mulx r12, r15, r10
adcx rdi, r13
adcx r11, rcx
adcx r15, rbx
adcx r12, r14
seto dl
adc dl, 0x0
movzx rdx, dl
mov r13, rdi
sub r13, r8
mov rcx, r11
sbb rcx, rbp
mov rbx, r15
sbb rbx, 0x00000000
mov r9, r12
sbb r9, r10
movzx r14, dl
sbb r14, 0x00000000
cmovc rbx, r15
cmovc rcx, r11
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], rbx
cmovc r13, rdi
cmovc r9, r12
mov [ r14 + 0x18 ], r9
mov [ r14 + 0x0 ], r13
mov [ r14 + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5579
; seed 1729677189422165 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1217502 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=149, initial num_batches=31): 83019 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06818797833596987
; number reverted permutation / tried permutation: 67612 / 89836 =75.262%
; number reverted decision / tried decision: 44192 / 90163 =49.013%
; validated in 1.49s
