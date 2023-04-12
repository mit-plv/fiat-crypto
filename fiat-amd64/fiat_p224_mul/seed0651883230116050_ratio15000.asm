SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 232
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r15
mulx r15, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r15
mulx r15, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r9
mov [ rsp - 0x20 ], rdi
mulx rdi, r9, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x18 ]
test al, al
adox rbp, r12
adcx rcx, r9
mov rdx, 0xffffffffffffffff 
mulx r9, r12, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], rbp
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], rcx
mov [ rsp + 0x18 ], r13
mulx r13, rcx, r12
adcx r9, r8
adcx r10, rbp
mov r8, 0x0 
adcx r11, r8
mov rdx, [ rax + 0x10 ]
mulx r8, rbp, [ rsi + 0x8 ]
adox rbp, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], r11
mulx r11, r15, [ rax + 0x18 ]
clc
adcx rbx, [ rsp + 0x0 ]
adcx r14, [ rsp - 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
adox r14, r8
adcx r15, [ rsp + 0x18 ]
mov rdx, 0x0 
adox rbx, rdx
adc r11, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x38 ], r11
mulx r11, r8, [ rax + 0x18 ]
mov rdx, [ rsp - 0x10 ]
test al, al
adox rdx, [ rsp - 0x20 ]
mov [ rsp + 0x40 ], r15
mov r15, [ rsp - 0x18 ]
adox r15, [ rsp - 0x28 ]
mov [ rsp + 0x48 ], r11
mov r11, 0xffffffff00000000 
xchg rdx, r11
mov [ rsp + 0x50 ], r15
mov [ rsp + 0x58 ], r11
mulx r11, r15, r12
adcx rcx, r11
adox r8, [ rsp - 0x30 ]
mov r11, 0xffffffff 
mov rdx, r12
mov [ rsp + 0x60 ], r8
mulx r8, r12, r11
adcx r12, r13
seto r13b
mov r11, -0x2 
inc r11
adox rdx, rdi
mov rdx, 0x0 
adcx r8, rdx
adox r15, [ rsp + 0x10 ]
adox rcx, r9
clc
adcx r15, [ rsp - 0x38 ]
adcx rcx, [ rsp + 0x8 ]
adox r12, r10
adcx rbp, r12
mov rdi, 0xffffffffffffffff 
mov rdx, r15
mulx r9, r15, rdi
adox r8, [ rsp + 0x20 ]
xchg rdx, rdi
mulx r10, r9, r15
adcx r14, r8
mov r12, r15
seto r8b
inc r11
adox r12, rdi
mov r12, 0xffffffff00000000 
mov rdx, r12
mulx rdi, r12, r15
movzx r11, r8b
adcx r11, rbx
setc bl
clc
adcx r9, rdi
mov r8, 0xffffffff 
mov rdx, r8
mulx rdi, r8, r15
adcx r8, r10
adox r12, rcx
adox r9, rbp
adox r8, r14
mov rcx, 0x0 
adcx rdi, rcx
clc
adcx r12, [ rsp - 0x40 ]
adox rdi, r11
mov rbp, 0xffffffffffffffff 
mov rdx, r12
mulx r15, r12, rbp
mov r15, 0xffffffff00000000 
xchg rdx, r12
mulx r14, r10, r15
mov r11, rdx
seto r15b
mov rbp, -0x3 
inc rbp
adox r11, r12
adcx r9, [ rsp + 0x58 ]
adcx r8, [ rsp + 0x50 ]
movzx r11, r13b
mov r12, [ rsp + 0x48 ]
lea r11, [ r11 + r12 ]
adox r10, r9
movzx r12, r15b
movzx rbx, bl
lea r12, [ r12 + rbx ]
adcx rdi, [ rsp + 0x60 ]
adcx r11, r12
mov r13, 0xffffffff 
mulx r15, rbx, r13
mov r9, 0xffffffffffffffff 
mulx rcx, r12, r9
setc dl
clc
adcx r12, r14
adcx rbx, rcx
adox r12, r8
adox rbx, rdi
mov r14, 0x0 
adcx r15, r14
clc
adcx r10, [ rsp - 0x48 ]
adcx r12, [ rsp + 0x30 ]
xchg rdx, r10
mulx rdi, r8, r9
adox r15, r11
xchg rdx, r8
mulx r11, rdi, r9
movzx rcx, r10b
adox rcx, r14
adcx rbx, [ rsp + 0x28 ]
adcx r15, [ rsp + 0x40 ]
adcx rcx, [ rsp + 0x38 ]
mov r10, rdx
mov rbp, -0x3 
inc rbp
adox r10, r8
mov r10, 0xffffffff00000000 
mulx r14, r8, r10
mulx r10, rbp, r13
adox r8, r12
setc r12b
clc
adcx rdi, r14
adcx rbp, r11
mov rdx, 0x0 
adcx r10, rdx
seto r11b
mov r14, r8
sub r14, 0x00000001
dec rdx
movzx r11, r11b
adox r11, rdx
adox rbx, rdi
adox rbp, r15
adox r10, rcx
seto r15b
mov rcx, rbx
mov r11, 0xffffffff00000000 
sbb rcx, r11
mov rdi, rbp
sbb rdi, r9
movzx rdx, r15b
movzx r12, r12b
lea rdx, [ rdx + r12 ]
mov r12, r10
sbb r12, r13
sbb rdx, 0x00000000
cmovc rcx, rbx
cmovc rdi, rbp
cmovc r14, r8
cmovc r12, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r14
mov [ rdx + 0x18 ], r12
mov [ rdx + 0x8 ], rcx
mov [ rdx + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 232
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5000
; seed 0651883230116050 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8797 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=117, initial num_batches=31): 468 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.053199954529953394
; number reverted permutation / tried permutation: 334 / 497 =67.203%
; number reverted decision / tried decision: 237 / 502 =47.211%
; validated in 3.125s
