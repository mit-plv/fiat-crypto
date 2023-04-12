SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 192
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r15
mulx r15, rdi, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r13
mulx r13, r14, rbp
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x8 ], r15
mov [ rsp + 0x0 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], rdi
mulx rdi, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], rdi
mov [ rsp + 0x18 ], r14
mulx r14, rdi, [ rax + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x20 ], r15
mov [ rsp + 0x28 ], r11
mulx r11, r15, rbp
adcx r15, r13
mov r13, 0x0 
adcx r11, r13
clc
adcx rcx, r12
adcx r9, r8
adcx rdi, rbx
adox r15, rcx
adox r11, r9
mov r8, 0xffffffff00000001 
mov rdx, r8
mulx rbx, r8, rbp
adcx r14, r13
adox r8, rdi
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, [ rax + 0x0 ]
clc
adcx r10, r9
mov rdx, [ rsp + 0x0 ]
adcx rdx, [ rsp + 0x28 ]
mov rdi, [ rsp - 0x8 ]
adcx rdi, [ rsp + 0x20 ]
adox rbx, r14
mov r14, [ rsp + 0x8 ]
adcx r14, r13
clc
adcx rbp, r15
seto r15b
mov r9, -0x3 
inc r9
adox r12, [ rsp + 0x18 ]
adcx r12, r11
mov r11, [ rsp + 0x10 ]
adox r11, [ rsp - 0x10 ]
adcx r11, r8
mov r8, rdx
mov rdx, [ rax + 0x18 ]
mulx r9, r13, [ rsi + 0x8 ]
adox r13, [ rsp - 0x18 ]
mov rdx, 0x0 
adox r9, rdx
adcx r13, rbx
mov rbx, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp + 0x30 ], r14
mulx r14, rbp, rbx
mov rbx, -0x2 
inc rbx
adox rbp, rdx
mov rbp, 0xffffffff 
mov [ rsp + 0x38 ], rdi
mulx rdi, rbx, rbp
movzx rbp, r15b
adcx rbp, r9
setc r15b
clc
adcx rbx, r14
adox rbx, r12
mov r12, 0x0 
adcx rdi, r12
adox rdi, r11
clc
adcx rcx, rbx
mov r11, 0xffffffff 
xchg rdx, r11
mulx r14, r9, rcx
mov rbx, 0xffffffff00000001 
mov rdx, r11
mulx r12, r11, rbx
adox r11, r13
adox r12, rbp
movzx rdx, r15b
mov r13, 0x0 
adox rdx, r13
adcx r10, rdi
adcx r8, r11
adcx r12, [ rsp + 0x38 ]
mov r15, 0xffffffffffffffff 
xchg rdx, rcx
mulx rdi, rbp, r15
mov r11, -0x3 
inc r11
adox rbp, rdx
adcx rcx, [ rsp + 0x30 ]
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r13, [ rax + 0x0 ]
setc dl
clc
adcx r9, rdi
mov rdi, 0x0 
adcx r14, rdi
adox r9, r10
adox r14, r8
xchg rdx, rbp
mulx r8, r10, rbx
adox r10, r12
adox r8, rcx
movzx rdx, bpl
adox rdx, rdi
test al, al
adox r11, [ rsp - 0x20 ]
mov r12, [ rsp - 0x40 ]
adox r12, [ rsp - 0x28 ]
mov rbp, [ rsp - 0x48 ]
adox rbp, [ rsp - 0x30 ]
adcx r13, r9
adcx r11, r14
mov rcx, [ rsp - 0x38 ]
adox rcx, rdi
adcx r12, r10
adcx rbp, r8
xchg rdx, r13
mulx r14, r9, rbx
mulx r8, r10, r15
adcx rcx, r13
mov r13, -0x3 
inc r13
adox r10, rdx
mov r10, 0xffffffff 
mulx r13, rdi, r10
setc dl
clc
adcx rdi, r8
mov r8, 0x0 
adcx r13, r8
adox rdi, r11
adox r13, r12
seto r11b
mov r12, rdi
sub r12, r15
dec r8
movzx r11, r11b
adox r11, r8
adox rbp, r9
adox r14, rcx
seto r9b
mov rcx, r13
sbb rcx, r10
mov r11, rbp
sbb r11, 0x00000000
movzx r8, r9b
movzx rdx, dl
lea r8, [ r8 + rdx ]
mov rdx, r14
sbb rdx, rbx
sbb r8, 0x00000000
cmovc r11, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r11
cmovc rcx, r13
cmovc rdx, r14
mov [ r8 + 0x18 ], rdx
mov [ r8 + 0x8 ], rcx
cmovc r12, rdi
mov [ r8 + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5594
; seed 3325380606283201 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 926131 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=119, initial num_batches=31): 62378 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06735332258611362
; number reverted permutation / tried permutation: 65577 / 90154 =72.739%
; number reverted decision / tried decision: 49802 / 89845 =55.431%
; validated in 1.462s
