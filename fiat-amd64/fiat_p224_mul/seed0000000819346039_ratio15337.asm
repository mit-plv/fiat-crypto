SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
test al, al
adox r10, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r10
mulx r10, r8, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], rdi
mulx rdi, rcx, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r10
mulx r10, rdi, [ rsi + 0x8 ]
adcx rdi, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
adcx r9, r10
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], rdi
mulx rdi, r10, [ rsi + 0x8 ]
adox rbp, r11
adcx r10, rbx
adox r13, r12
mov rdx, 0x0 
adox r14, rdx
mov rdx, [ rax + 0x8 ]
mulx rbx, r11, [ rsi + 0x0 ]
adc rdi, 0x0
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x8 ], r14
mulx r14, r12, rcx
mov rdx, 0xffffffff 
mov [ rsp + 0x0 ], r13
mov [ rsp + 0x8 ], rbp
mulx rbp, r13, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r15
mov [ rsp + 0x18 ], rdi
mulx rdi, r15, rcx
xor rdx, rdx
adox r15, r14
adox r13, rdi
adcx r11, [ rsp - 0x20 ]
adox rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x20 ], r10
mov [ rsp + 0x28 ], rbp
mulx rbp, r10, [ rsi + 0x0 ]
adcx r14, rbx
adcx r10, rdi
adc rbp, 0x0
test al, al
adox rcx, r8
adox r12, r11
adcx r12, [ rsp - 0x28 ]
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r12
mov r8, 0xffffffff00000000 
mov rdx, r8
mulx rbx, r8, rcx
adox r15, r14
mov r11, 0xffffffffffffffff 
mov rdx, rcx
mulx rdi, rcx, r11
adox r13, r10
adcx r15, [ rsp - 0x18 ]
adcx r9, r13
adox rbp, [ rsp + 0x28 ]
adcx rbp, [ rsp + 0x20 ]
mov r14, 0xffffffff 
mulx r13, r10, r14
seto r14b
movzx r14, r14b
adcx r14, [ rsp + 0x18 ]
mov r11, -0x2 
inc r11
adox rcx, rbx
adox r10, rdi
mov rbx, 0x0 
adox r13, rbx
mov rdi, -0x3 
inc rdi
adox rdx, r12
adox r8, r15
adox rcx, r9
mov rdx, [ rax + 0x0 ]
mulx r15, r12, [ rsi + 0x10 ]
setc dl
clc
adcx r15, [ rsp + 0x10 ]
adox r10, rbp
mov r9b, dl
mov rdx, [ rax + 0x10 ]
mulx rbx, rbp, [ rsi + 0x10 ]
adcx rbp, [ rsp - 0x10 ]
adox r13, r14
adcx rbx, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
mov r14, 0x0 
adcx rdx, r14
clc
adcx r12, r8
adcx r15, rcx
adcx rbp, r10
mov r8, 0xffffffffffffffff 
xchg rdx, r8
mulx r10, rcx, r12
adcx rbx, r13
mulx r13, r10, rcx
mov r14, 0xffffffff 
mov rdx, r14
mulx rdi, r14, rcx
movzx r11, r9b
mov rdx, 0x0 
adox r11, rdx
adcx r8, r11
mov r9, 0xffffffff00000000 
mov rdx, r9
mulx r11, r9, rcx
mov rdx, -0x2 
inc rdx
adox rcx, r12
setc cl
clc
adcx r10, r11
adcx r14, r13
adox r9, r15
mov r12, 0x0 
adcx rdi, r12
adox r10, rbp
clc
adcx r9, [ rsp - 0x40 ]
adox r14, rbx
adox rdi, r8
movzx r15, cl
adox r15, r12
mov rbp, 0xffffffffffffffff 
mov rdx, r9
mulx rbx, r9, rbp
mov rbx, 0xffffffff00000000 
xchg rdx, r9
mulx rcx, r13, rbx
mulx r11, r8, rbp
mov rbp, -0x3 
inc rbp
adox r8, rcx
adcx r10, [ rsp - 0x48 ]
adcx r14, [ rsp + 0x8 ]
adcx rdi, [ rsp + 0x0 ]
adcx r15, [ rsp - 0x8 ]
mov rcx, 0xffffffff 
mulx rbp, r12, rcx
setc cl
clc
adcx rdx, r9
adcx r13, r10
adcx r8, r14
adox r12, r11
adcx r12, rdi
mov rdx, 0x0 
adox rbp, rdx
adcx rbp, r15
movzx r9, cl
adc r9, 0x0
mov r11, r13
sub r11, 0x00000001
mov r10, r8
sbb r10, rbx
mov r14, r12
mov rdi, 0xffffffffffffffff 
sbb r14, rdi
mov rcx, rbp
mov r15, 0xffffffff 
sbb rcx, r15
sbb r9, 0x00000000
cmovc r11, r13
cmovc rcx, rbp
cmovc r10, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r11
mov [ r9 + 0x18 ], rcx
cmovc r14, r12
mov [ r9 + 0x10 ], r14
mov [ r9 + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5337
; seed 1662770514796942 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1340389 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=129, initial num_batches=31): 87763 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06547576860150299
; number reverted permutation / tried permutation: 66879 / 89836 =74.446%
; number reverted decision / tried decision: 47617 / 90163 =52.812%
; validated in 2.98s
