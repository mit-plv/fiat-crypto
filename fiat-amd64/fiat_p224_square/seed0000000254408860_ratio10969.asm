SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 216
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
mulx rax, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r9
mulx r9, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r15
mulx r15, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r8
mulx r8, r15, r11
xor r8, r8
adox r12, rbx
mulx r8, rbx, r15
mov rdx, r15
adcx rdx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], r12
mulx r12, r11, [ rsi + 0x0 ]
setc dl
clc
adcx rdi, r12
mov r12b, dl
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], rdi
mov [ rsp + 0x10 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], r11
mov [ rsp + 0x20 ], rdi
mulx rdi, r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], r8
mulx r8, rdi, [ rsi + 0x10 ]
adcx r11, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x38 ], r11
mulx r11, rax, [ rsi + 0x8 ]
setc dl
clc
adcx rax, rcx
adcx rdi, r11
adcx rbp, r8
mov cl, dl
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r9, rdx
adox r14, r13
clc
adcx r8, r10
mov r10, [ rsp - 0x18 ]
adox r10, [ rsp - 0x8 ]
adcx r11, [ rsp - 0x20 ]
mov r13, [ rsp - 0x10 ]
adox r13, rdx
mov rdx, 0xffffffff00000000 
mov [ rsp + 0x40 ], r11
mov [ rsp + 0x48 ], r8
mulx r8, r11, r15
mov rdx, 0x0 
dec rdx
movzx r12, r12b
adox r12, rdx
adox rax, r11
mov r12, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x28 ]
mov r11, 0xffffffff 
mov rdx, r11
mov [ rsp + 0x50 ], r12
mulx r12, r11, r15
setc r15b
clc
adcx rbx, r8
adcx r11, [ rsp + 0x30 ]
mov r8, 0x0 
adcx r12, r8
movzx r8, r15b
mov rdx, [ rsp - 0x40 ]
lea r8, [ r8 + rdx ]
adox rbx, rdi
clc
adcx rax, [ rsp - 0x30 ]
adcx rbx, [ rsp + 0x0 ]
adox r11, rbp
adox r12, r9
adcx r14, r11
adcx r10, r12
mov rdx, 0xffffffffffffffff 
mulx rbp, rdi, rax
mov rbp, 0xffffffff00000000 
mov rdx, rbp
mulx r9, rbp, rdi
setc r15b
movzx r15, r15b
adox r15, r13
mov r13, 0xffffffffffffffff 
mov rdx, r13
mulx r11, r13, rdi
mov r12, rdi
clc
adcx r12, rax
seto r12b
mov rax, -0x2 
inc rax
adox r13, r9
adcx rbp, rbx
mov rbx, 0xffffffff 
mov rdx, rdi
mulx r9, rdi, rbx
adox rdi, r11
adcx r13, r14
adcx rdi, r10
mov r14, 0x0 
adox r9, r14
adcx r9, r15
mov r10, -0x3 
inc r10
adox rbp, [ rsp + 0x10 ]
adox r13, [ rsp + 0x8 ]
adox rdi, [ rsp + 0x38 ]
mov rdx, 0xffffffffffffffff 
mulx r11, r15, rbp
movzx r11, r12b
adcx r11, r14
mov rdx, rbx
mulx r12, rbx, r15
mov r14, [ rsp + 0x28 ]
clc
movzx rcx, cl
adcx rcx, rax
adcx r14, [ rsp + 0x20 ]
mov rcx, r15
seto r10b
inc rax
adox rcx, rbp
mov rcx, [ rsp + 0x18 ]
adcx rcx, rax
clc
mov rbp, -0x1 
movzx r10, r10b
adcx r10, rbp
adcx r9, r14
mov r10, 0xffffffff00000000 
mov rdx, r10
mulx r14, r10, r15
mov rax, 0xffffffffffffffff 
mov rdx, r15
mulx rbp, r15, rax
adcx rcx, r11
setc dl
clc
adcx r15, r14
adcx rbx, rbp
adox r10, r13
mov r13, 0x0 
adcx r12, r13
clc
adcx r10, [ rsp - 0x48 ]
adox r15, rdi
adox rbx, r9
xchg rdx, rax
mulx r11, rdi, r10
adox r12, rcx
mov r11, rdi
setc r9b
clc
adcx r11, r10
movzx r11, al
adox r11, r13
mov r14, 0xffffffff00000000 
mov rdx, r14
mulx rbp, r14, rdi
dec r13
movzx r9, r9b
adox r9, r13
adox r15, [ rsp + 0x48 ]
adox rbx, [ rsp + 0x40 ]
adcx r14, r15
mov rax, 0xffffffffffffffff 
mov rdx, rdi
mulx rcx, rdi, rax
adox r12, [ rsp + 0x50 ]
seto r10b
inc r13
adox rdi, rbp
mov r9, 0xffffffff 
mulx r15, rbp, r9
adox rbp, rcx
adcx rdi, rbx
adcx rbp, r12
adox r15, r13
dec r13
movzx r10, r10b
adox r10, r13
adox r11, r8
adcx r15, r11
setc r8b
seto dl
mov rbx, r14
sub rbx, 0x00000001
mov rcx, rdi
mov r10, 0xffffffff00000000 
sbb rcx, r10
mov r12, rbp
sbb r12, rax
movzx r11, r8b
movzx rdx, dl
lea r11, [ r11 + rdx ]
mov rdx, r15
sbb rdx, r9
sbb r11, 0x00000000
cmovc r12, rbp
cmovc rcx, rdi
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], rcx
cmovc rdx, r15
cmovc rbx, r14
mov [ r11 + 0x10 ], r12
mov [ r11 + 0x0 ], rbx
mov [ r11 + 0x18 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 216
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0969
; seed 2496356477598303 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1059096 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 69172 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.065312304078195
; number reverted permutation / tried permutation: 71424 / 90015 =79.347%
; number reverted decision / tried decision: 53729 / 89984 =59.710%
; validated in 2.118s
