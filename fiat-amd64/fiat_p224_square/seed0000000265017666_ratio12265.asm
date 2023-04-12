SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 192
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rdi
mulx rdi, r13, rdx
test al, al
adox r13, r14
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r13
mulx r13, r14, r12
adox rax, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rax
mulx rax, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r13
mulx r13, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], r14
mulx r14, r15, rdx
adcx r11, rax
adcx r15, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r15
mov [ rsp + 0x10 ], r11
mulx r11, r15, [ rsi + 0x0 ]
adcx rcx, r14
mov rdx, 0x0 
adcx rax, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rax
mulx rax, r14, [ rsi + 0x10 ]
clc
adcx r15, rbp
adcx r14, r11
adcx r8, rax
mov rdx, 0x0 
adcx r9, rdx
mov rbp, r12
clc
adcx rbp, rbx
adox rdi, r10
adox r13, rdx
mov rbp, 0xffffffff 
mov rdx, rbp
mulx r10, rbp, r12
adcx r15, [ rsp - 0x10 ]
mov rbx, [ rsp - 0x18 ]
mov r12, -0x2 
inc r12
adox rbx, [ rsp - 0x40 ]
adcx rbx, r14
adox rbp, [ rsp - 0x20 ]
adcx rbp, r8
mov r11, 0x0 
adox r10, r11
mov rax, -0x3 
inc rax
adox r15, [ rsp - 0x48 ]
adox rbx, [ rsp - 0x38 ]
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx r8, r14, r15
mulx r11, r8, r14
adox rbp, [ rsp - 0x30 ]
adcx r10, r9
adox rdi, r10
mov r9, 0xffffffff 
mov rdx, r14
mulx r10, r14, r9
mov rax, 0xffffffff00000000 
mulx r9, r12, rax
setc al
clc
adcx r8, r9
adcx r14, r11
movzx r11, al
adox r11, r13
mov r13, 0x0 
adcx r10, r13
clc
adcx rdx, r15
adcx r12, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rsi + 0x18 ]
seto dl
mov rax, -0x3 
inc rax
adox r12, [ rsp - 0x28 ]
adcx r8, rbp
adox r8, [ rsp + 0x10 ]
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mulx r13, r9, r12
mov r13, 0xffffffff 
mov rdx, r13
mulx rax, r13, r9
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x20 ], rax
mov [ rsp + 0x28 ], r13
mulx r13, rax, r9
adcx r14, rdi
adcx r10, r11
adox r14, [ rsp + 0x8 ]
adox rcx, r10
movzx rdi, bpl
mov r11, 0x0 
adcx rdi, r11
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rcx
mulx rcx, r11, rdx
clc
adcx rbx, [ rsp + 0x0 ]
adcx rbp, [ rsp - 0x8 ]
adcx r11, r10
adox rdi, [ rsp + 0x18 ]
mov rdx, r9
seto r10b
mov [ rsp + 0x38 ], r11
mov r11, -0x2 
inc r11
adox rdx, r12
adox rax, r8
mov rdx, 0x0 
adcx rcx, rdx
clc
adcx r15, rax
mov r12, 0xffffffffffffffff 
mov rdx, r15
mulx r8, r15, r12
xchg rdx, r12
mulx rax, r8, r9
mov r9, r15
setc r11b
clc
adcx r9, r12
setc r9b
clc
adcx r8, r13
adcx rax, [ rsp + 0x28 ]
adox r8, r14
adox rax, [ rsp + 0x30 ]
mov r13, [ rsp + 0x20 ]
mov r14, 0x0 
adcx r13, r14
clc
mov r12, -0x1 
movzx r11, r11b
adcx r11, r12
adcx r8, rbx
adcx rbp, rax
adox r13, rdi
mov rbx, 0xffffffff00000000 
mov rdx, r15
mulx rdi, r15, rbx
movzx r11, r10b
adox r11, r14
mov r10, 0xffffffffffffffff 
mulx r14, rax, r10
inc r12
adox rax, rdi
adcx r13, [ rsp + 0x38 ]
adcx rcx, r11
setc dil
clc
mov r11, -0x1 
movzx r9, r9b
adcx r9, r11
adcx r8, r15
adcx rax, rbp
mov r9, 0xffffffff 
mulx r15, rbp, r9
adox rbp, r14
adox r15, r12
adcx rbp, r13
adcx r15, rcx
setc dl
mov r14, r8
sub r14, 0x00000001
mov r13, rax
sbb r13, rbx
mov rcx, rbp
sbb rcx, r10
movzx r12, dl
movzx rdi, dil
lea r12, [ r12 + rdi ]
mov rdi, r15
sbb rdi, r9
sbb r12, 0x00000000
cmovc r14, r8
cmovc r13, rax
cmovc rdi, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], rdi
mov [ r12 + 0x0 ], r14
cmovc rcx, rbp
mov [ r12 + 0x10 ], rcx
mov [ r12 + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2265
; seed 0666440906020167 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1029275 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 68054 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06611838429962838
; number reverted permutation / tried permutation: 70691 / 90044 =78.507%
; number reverted decision / tried decision: 52978 / 89955 =58.894%
; validated in 2.175s
