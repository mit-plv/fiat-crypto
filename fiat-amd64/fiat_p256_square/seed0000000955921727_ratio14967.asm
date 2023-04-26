SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 168
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0xffffffff00000001 
mov rdx, rax
mulx rcx, rax, r11
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mulx r11, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rbp
mulx rbp, r12, r8
test al, al
adox r13, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rcx
mulx rcx, rbp, [ rsi + 0x8 ]
adcx rbp, r10
adcx r15, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ rsi + 0x18 ]
adcx r10, r11
mov rdx, 0x0 
adcx rcx, rdx
adox r14, rdx
test al, al
adox r12, r8
adox r13, rbp
adcx rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, rbx, [ rsi + 0x10 ]
adox r14, r15
adox rax, r10
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rsi + 0x0 ]
adox rcx, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], rdi
mulx rdi, rbx, [ rsi + 0x18 ]
seto dl
mov [ rsp - 0x18 ], r12
mov r12, -0x2 
inc r12
adox r8, [ rsp - 0x38 ]
adox r9, [ rsp - 0x40 ]
adox rbx, rbp
mov rbp, 0x0 
adox rdi, rbp
mov r12, -0x3 
inc r12
adox r15, r13
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rbx
mulx rbx, rdi, r15
setc dl
clc
adcx rbp, r10
adox rbp, r14
mov r14b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r9
mulx r9, r10, rdx
mov rdx, 0xffffffff 
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rbp
mulx rbp, r8, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], rdi
mov byte [ rsp + 0x20 ], r13b
mulx r13, rdi, [ rsi + 0x10 ]
adcx rdi, r12
adox rdi, rax
mov rdx, [ rsi + 0x8 ]
mulx r12, rax, [ rsi + 0x18 ]
adcx rax, r13
mov rdx, 0x0 
adcx r12, rdx
adox rax, rcx
clc
mov rcx, -0x1 
movzx r14, r14b
adcx r14, rcx
adcx r11, r10
adcx r9, rdx
clc
adcx r8, rbx
adcx rbp, rdx
movzx r14, byte [ rsp + 0x20 ]
adox r14, r12
mov rbx, r15
clc
adcx rbx, [ rsp + 0x18 ]
adcx r8, [ rsp + 0x10 ]
seto bl
mov r10, -0x3 
inc r10
adox r8, [ rsp - 0x18 ]
mov r13, 0xffffffff 
mov rdx, r8
mulx r12, r8, r13
adcx rbp, rdi
mov rdi, 0xffffffff00000001 
xchg rdx, rdi
mulx rcx, r10, r15
adox rbp, [ rsp + 0x8 ]
adcx r10, rax
adcx rcx, r14
movzx r15, bl
mov rax, 0x0 
adcx r15, rax
mov rbx, 0xffffffffffffffff 
mov rdx, rdi
mulx r14, rdi, rbx
adox r10, [ rsp + 0x0 ]
clc
adcx r8, r14
adox rcx, [ rsp - 0x8 ]
adcx r12, rax
clc
adcx rdi, rdx
adcx r8, rbp
adcx r12, r10
adox r15, [ rsp - 0x10 ]
seto dil
mov rbp, -0x3 
inc rbp
adox r8, [ rsp - 0x48 ]
mov r14, 0xffffffff00000001 
mulx rax, r10, r14
adcx r10, rcx
adcx rax, r15
adox r12, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
movzx rdx, dil
mov rcx, 0x0 
adcx rdx, rcx
adox r11, rax
xchg rdx, r8
mulx r15, rdi, r13
mulx rcx, rax, rbx
clc
adcx rax, rdx
adox r9, r8
seto al
inc rbp
adox rdi, rcx
mov r8, 0x0 
adox r15, r8
adcx rdi, r12
adcx r15, r10
mulx r10, r12, r14
adcx r12, r11
adcx r10, r9
movzx rdx, al
adc rdx, 0x0
mov r11, rdi
sub r11, rbx
mov rcx, r15
sbb rcx, r13
mov rax, r12
sbb rax, 0x00000000
mov r9, r10
sbb r9, r14
sbb rdx, 0x00000000
cmovc rax, r12
cmovc r9, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], rax
cmovc rcx, r15
cmovc r11, rdi
mov [ rdx + 0x0 ], r11
mov [ rdx + 0x8 ], rcx
mov [ rdx + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4967
; seed 0957258945381364 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 916506 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=133, initial num_batches=31): 63112 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0688615240925864
; number reverted permutation / tried permutation: 69321 / 90092 =76.945%
; number reverted decision / tried decision: 49746 / 89907 =55.331%
; validated in 1.195s
