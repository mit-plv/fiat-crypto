SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 224
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, r11
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, rdi
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r8
mulx r8, r9, rdi
mov rdx, 0xffffffff 
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r14
mulx r14, r15, [ rsi + 0x0 ]
add rax, rcx
adcx r15, r10
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rsi + 0x0 ]
adcx r10, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r10
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r15
mov [ rsp + 0x8 ], r12
mulx r12, r15, [ rsi + 0x0 ]
adc rcx, 0x0
test al, al
adox r14, r12
adcx rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, rdx
adox rdi, r10
adcx r9, rax
setc dl
clc
adcx rbp, r8
adcx r13, rbx
mov rbx, [ rsp + 0x8 ]
mov r8, 0x0 
adcx rbx, r8
clc
mov rax, -0x1 
movzx rdx, dl
adcx rdx, rax
adcx rbp, [ rsp + 0x0 ]
adox r11, [ rsp - 0x10 ]
mov r10, [ rsp - 0x18 ]
adox r10, r8
adcx r13, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, [ rsi + 0x8 ]
adcx rbx, rcx
inc rax
adox r12, r9
mov rdx, 0xffffffffffffffff 
mulx r9, rcx, r12
mov rdx, [ rsi + 0x8 ]
mulx rax, r9, [ rsi + 0x18 ]
setc dl
clc
adcx r8, [ rsp - 0x20 ]
adox r8, rbp
mov bpl, dl
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r11
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsp - 0x28 ]
adcx rdx, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov [ rsp + 0x20 ], r10
mov r10, 0x0 
adcx rax, r10
clc
adcx r11, [ rsp - 0x40 ]
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x28 ], r11
mov [ rsp + 0x30 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
adcx r11, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r14
mulx r14, r11, rdx
adox r10, r13
adox r9, rbx
mov rdx, 0xffffffffffffffff 
mulx rbx, r13, rcx
adcx r11, rdi
mov rdi, 0xffffffff00000000 
mov rdx, rcx
mov [ rsp + 0x48 ], r14
mulx r14, rcx, rdi
movzx rdi, bpl
adox rdi, rax
mov rbp, 0xffffffff 
mov [ rsp + 0x50 ], r11
mulx r11, rax, rbp
setc bpl
clc
adcx r13, r14
seto r14b
mov byte [ rsp + 0x58 ], bpl
mov rbp, -0x2 
inc rbp
adox rdx, r12
adox rcx, r8
adox r13, r10
adcx rax, rbx
seto dl
inc rbp
adox r15, rcx
mov r12, 0xffffffffffffffff 
xchg rdx, r15
mulx r10, r8, r12
adcx r11, rbp
clc
mov r10, -0x1 
movzx r15, r15b
adcx r15, r10
adcx r9, rax
adcx r11, rdi
movzx rbx, r14b
adcx rbx, rbp
adox r13, [ rsp + 0x40 ]
adox r9, [ rsp + 0x30 ]
xchg rdx, r12
mulx rdi, r14, r8
adox r11, [ rsp + 0x18 ]
mov rcx, 0xffffffff00000000 
mov rdx, r8
mulx r15, r8, rcx
clc
adcx r14, r15
mov rax, 0xffffffff 
mulx rbp, r15, rax
adcx r15, rdi
mov rdi, 0x0 
adcx rbp, rdi
adox rbx, [ rsp + 0x10 ]
clc
adcx rdx, r12
adcx r8, r13
seto dl
mov r12, -0x3 
inc r12
adox r8, [ rsp + 0x20 ]
mov r13, 0xffffffffffffffff 
xchg rdx, r8
mulx r12, rdi, r13
xchg rdx, r13
mulx r10, r12, rdi
adcx r14, r9
adox r14, [ rsp + 0x28 ]
adcx r15, r11
adcx rbp, rbx
movzx r9, r8b
mov r11, 0x0 
adcx r9, r11
mov rdx, rax
mulx r8, rax, rdi
mov rdx, rcx
mulx rbx, rcx, rdi
clc
adcx r12, rbx
adcx rax, r10
adcx r8, r11
clc
adcx rdi, r13
adcx rcx, r14
adox r15, [ rsp + 0x38 ]
adox rbp, [ rsp + 0x50 ]
movzx rdi, byte [ rsp + 0x58 ]
mov r13, [ rsp + 0x48 ]
lea rdi, [ rdi + r13 ]
adcx r12, r15
adox rdi, r9
adcx rax, rbp
adcx r8, rdi
seto r13b
adc r13b, 0x0
movzx r13, r13b
mov r10, rcx
sub r10, 0x00000001
mov r14, r12
sbb r14, rdx
mov r9, rax
mov rbx, 0xffffffffffffffff 
sbb r9, rbx
mov r15, r8
mov rbp, 0xffffffff 
sbb r15, rbp
movzx rdi, r13b
sbb rdi, 0x00000000
cmovc r14, r12
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r14
cmovc r15, r8
cmovc r10, rcx
mov [ rdi + 0x18 ], r15
cmovc r9, rax
mov [ rdi + 0x0 ], r10
mov [ rdi + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 224
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2882
; seed 4069091139136389 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1281227 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=157, initial num_batches=31): 88373 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06897528697100513
; number reverted permutation / tried permutation: 69487 / 90329 =76.927%
; number reverted decision / tried decision: 46128 / 89670 =51.442%
; validated in 2.663s
