SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 232
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rbx
mulx rbx, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], r13
mulx r13, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], r14
mulx r14, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
test al, al
adox r12, r11
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r8
mulx r8, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x20 ], rcx
mov [ rsp + 0x28 ], r13
mulx r13, rcx, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], r14
mulx r14, rbx, [ rax + 0x18 ]
adox r11, rbp
mov rdx, 0xffffffff 
mov [ rsp + 0x40 ], rdi
mulx rdi, rbp, r10
adcx rbp, r13
mov r13, 0x0 
adcx rdi, r13
clc
adcx rcx, r10
adcx rbp, r12
adcx rdi, r11
adox rbx, r8
adcx r15, rbx
adox r14, r13
mov rcx, -0x3 
inc rcx
adox r9, rbp
adcx r14, [ rsp + 0x40 ]
mulx r12, r10, r9
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r11, r8, r9
mov rbp, 0xffffffff00000001 
mov rdx, r9
mulx rbx, r9, rbp
mov rcx, [ rsp + 0x38 ]
setc bpl
clc
adcx rcx, [ rsp + 0x30 ]
adox rcx, rdi
mov rdi, [ rsp + 0x20 ]
adcx rdi, [ rsp + 0x28 ]
mov r13, [ rsp - 0x10 ]
adcx r13, [ rsp + 0x18 ]
adox rdi, r15
adox r13, r14
mov r15, [ rsp - 0x18 ]
mov r14, 0x0 
adcx r15, r14
movzx r14, bpl
adox r14, r15
clc
adcx r10, r11
setc bpl
clc
adcx r8, rdx
adcx r10, rcx
movzx r8, bpl
lea r8, [ r8 + r12 ]
adcx r8, rdi
mov rdx, [ rax + 0x0 ]
mulx r11, r12, [ rsi + 0x10 ]
seto dl
mov rcx, -0x2 
inc rcx
adox r12, r10
mov rdi, 0xffffffff 
xchg rdx, rdi
mulx rbp, r15, r12
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx rcx, r10, r12
adcx r9, r13
adcx rbx, r14
setc r13b
clc
adcx r15, rcx
mov r14, 0x0 
adcx rbp, r14
movzx rcx, r13b
movzx rdi, dil
lea rcx, [ rcx + rdi ]
mov rdi, [ rsp - 0x20 ]
clc
adcx rdi, [ rsp - 0x28 ]
mov r13, [ rsp - 0x40 ]
adcx r13, [ rsp + 0x0 ]
mov r14, [ rsp - 0x8 ]
adcx r14, [ rsp + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x48 ], r14
mov [ rsp + 0x50 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x58 ], rdi
mov [ rsp + 0x60 ], rbp
mulx rbp, rdi, [ rax + 0x10 ]
setc dl
clc
adcx r14, r11
adcx rdi, r13
movzx r11, dl
mov r13, [ rsp + 0x8 ]
lea r11, [ r11 + r13 ]
adox r14, r8
adcx rbp, [ rsp - 0x30 ]
adox rdi, r9
mov r13, [ rsp - 0x38 ]
mov r8, 0x0 
adcx r13, r8
clc
adcx r10, r12
adox rbp, rbx
adcx r15, r14
adox r13, rcx
adcx rdi, [ rsp + 0x60 ]
mov r10, 0xffffffff00000001 
mov rdx, r10
mulx r9, r10, r12
adcx r10, rbp
adcx r9, r13
seto r12b
mov rbx, -0x3 
inc rbx
adox r15, [ rsp - 0x48 ]
mov rcx, 0xffffffff 
mov rdx, r15
mulx r14, r15, rcx
mov rbp, 0xffffffffffffffff 
mulx r8, r13, rbp
movzx rbx, r12b
mov rcx, 0x0 
adcx rbx, rcx
clc
adcx r15, r8
adox rdi, [ rsp + 0x58 ]
adcx r14, rcx
clc
adcx r13, rdx
adox r10, [ rsp + 0x50 ]
adcx r15, rdi
adcx r14, r10
adox r9, [ rsp + 0x48 ]
adox r11, rbx
mov r13, 0xffffffff00000001 
mulx r8, r12, r13
adcx r12, r9
adcx r8, r11
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbx, r15
sub rbx, rbp
mov rdi, r14
mov r10, 0xffffffff 
sbb rdi, r10
mov r9, r12
sbb r9, 0x00000000
mov r11, r8
sbb r11, r13
movzx r13, dl
sbb r13, 0x00000000
cmovc rdi, r14
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], rdi
cmovc rbx, r15
mov [ r13 + 0x0 ], rbx
cmovc r11, r8
cmovc r9, r12
mov [ r13 + 0x10 ], r9
mov [ r13 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 232
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5654
; seed 1535036302554226 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1174485 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=135, initial num_batches=31): 82302 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07007496902897865
; number reverted permutation / tried permutation: 68033 / 89679 =75.863%
; number reverted decision / tried decision: 43995 / 90320 =48.710%
; validated in 1.834s
