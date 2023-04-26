SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 216
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, 0xffffffffffffffff 
mov rdx, rax
mulx rcx, rax, r11
xchg rdx, r11
mulx r8, rcx, rax
mov r9, 0xffffffff00000000 
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r12
mulx r12, r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
mov rdx, rax
adcx rdx, r11
adox rbp, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r11, [ rsi + 0x18 ]
adox r11, r14
seto dl
mov r14, -0x2 
inc r14
adox rcx, rbx
mov rbx, 0xffffffff 
xchg rdx, rax
mov [ rsp - 0x20 ], r13
mulx r13, r14, rbx
adox r14, r8
adcx r9, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r13, rdx
adcx rcx, rbp
mov rbp, -0x3 
inc rbp
adox r8, r9
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rbp, r9, r8
mulx rbx, rbp, r9
movzx rdx, al
lea rdx, [ rdx + rdi ]
adcx r14, r11
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, [ rsi + 0x8 ]
adcx r13, rdi
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r13
mulx r13, rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r14
mov [ rsp + 0x8 ], r12
mulx r12, r14, [ rsi + 0x10 ]
setc dl
clc
adcx rax, rcx
adcx rdi, r11
adcx r14, r13
mov r11, 0xffffffff00000000 
xchg rdx, r11
mulx rcx, r13, r9
mov rdx, 0x0 
adcx r12, rdx
mov rdx, 0xffffffff 
mov [ rsp + 0x10 ], r12
mov [ rsp + 0x18 ], r14
mulx r14, r12, r9
clc
adcx rbp, rcx
adcx r12, rbx
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rsi + 0x18 ]
mov rdx, 0x0 
adcx r14, rdx
clc
adcx r10, r15
mov r15, [ rsp + 0x8 ]
adcx r15, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x38 ]
adox r10, [ rsp - 0x8 ]
adcx rcx, rdx
clc
adcx r9, r8
adox r15, [ rsp - 0x10 ]
adcx r13, r10
adox rbx, [ rsp - 0x18 ]
setc r9b
clc
adcx r13, [ rsp + 0x0 ]
setc r8b
clc
mov r10, -0x1 
movzx r9, r9b
adcx r9, r10
adcx r15, rbp
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx r9, rbp, r13
adcx r12, rbx
movzx r9, r11b
adox r9, rcx
seto r11b
inc r10
mov rcx, -0x1 
movzx r8, r8b
adox r8, rcx
adox r15, rax
adcx r14, r9
adox rdi, r12
mov rax, 0xffffffff00000000 
mov rdx, rbp
mulx rbx, rbp, rax
mov r8, 0xffffffffffffffff 
mulx r9, r12, r8
movzx r10, r11b
mov rcx, 0x0 
adcx r10, rcx
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, rcx, [ rsi + 0x8 ]
clc
adcx rcx, [ rsp - 0x28 ]
adcx rax, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x20 ], rax
mulx rax, r8, rdx
adcx r8, [ rsp - 0x48 ]
adox r14, [ rsp + 0x18 ]
mov rdx, r11
mov [ rsp + 0x28 ], r8
setc r8b
clc
adcx rdx, r13
adox r10, [ rsp + 0x10 ]
adcx rbp, r15
movzx rdx, r8b
lea rdx, [ rdx + rax ]
seto r13b
mov r15, -0x2 
inc r15
adox rbp, [ rsp - 0x30 ]
mov rax, 0xffffffffffffffff 
xchg rdx, rbp
mulx r15, r8, rax
xchg rdx, rax
mov [ rsp + 0x30 ], rbp
mulx rbp, r15, r8
mov rdx, 0xffffffff 
mov byte [ rsp + 0x38 ], r13b
mov [ rsp + 0x40 ], rbp
mulx rbp, r13, r8
mov [ rsp + 0x48 ], rbp
mov [ rsp + 0x50 ], r13
mulx r13, rbp, r11
setc r11b
clc
adcx r12, rbx
adcx rbp, r9
mov rbx, 0x0 
adcx r13, rbx
clc
mov r9, -0x1 
movzx r11, r11b
adcx r11, r9
adcx rdi, r12
adcx rbp, r14
mov r14, 0xffffffff00000000 
mov rdx, r14
mulx r11, r14, r8
adcx r13, r10
adox rcx, rdi
seto r10b
mov r12, -0x3 
inc r12
adox r15, r11
mov rdi, [ rsp + 0x40 ]
adox rdi, [ rsp + 0x50 ]
mov r11, [ rsp + 0x48 ]
adox r11, rbx
movzx rbx, byte [ rsp + 0x38 ]
adc rbx, 0x0
add r10b, 0x7F
adox rbp, [ rsp + 0x20 ]
adcx r8, rax
adcx r14, rcx
adcx r15, rbp
adox r13, [ rsp + 0x28 ]
adox rbx, [ rsp + 0x30 ]
adcx rdi, r13
adcx r11, rbx
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rax, r14
sub rax, 0x00000001
mov r10, r15
sbb r10, rdx
mov rcx, rdi
mov rbp, 0xffffffffffffffff 
sbb rcx, rbp
mov r13, r11
mov rbx, 0xffffffff 
sbb r13, rbx
movzx r12, r8b
sbb r12, 0x00000000
cmovc rax, r14
cmovc r13, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], r13
cmovc rcx, rdi
cmovc r10, r15
mov [ r12 + 0x10 ], rcx
mov [ r12 + 0x8 ], r10
mov [ r12 + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 216
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1436
; seed 3782171073903758 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1062666 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=145, initial num_batches=31): 69880 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0657591378664604
; number reverted permutation / tried permutation: 72492 / 89721 =80.797%
; number reverted decision / tried decision: 54491 / 90278 =60.359%
; validated in 2.128s
