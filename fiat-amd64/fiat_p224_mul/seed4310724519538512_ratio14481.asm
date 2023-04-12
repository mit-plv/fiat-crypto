SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 200
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r10
mulx r10, r12, [ rax + 0x8 ]
xor rdx, rdx
adox r12, rbx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r12
mulx r12, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r9
mulx r9, rbp, [ rax + 0x10 ]
adcx r13, r11
adcx rcx, r14
mov rdx, [ rax + 0x18 ]
mulx r14, r11, [ rsi + 0x10 ]
adcx r11, r8
mov rdx, 0x0 
adcx r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r14
mulx r14, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], rcx
mulx rcx, r11, [ rax + 0x0 ]
clc
adcx r8, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r13
mulx r13, rcx, [ rax + 0x18 ]
adox rbx, r10
adox rcx, r12
mov rdx, [ rax + 0x0 ]
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x0 ], r10
mov [ rsp + 0x8 ], rcx
mulx rcx, r10, r11
mov rcx, 0x0 
adox r13, rcx
mov rdx, r10
mov [ rsp + 0x10 ], r13
mov r13, -0x3 
inc r13
adox rdx, r11
adcx rbp, r14
mov rdx, 0xffffffff00000000 
mulx r11, r14, r10
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, [ rax + 0x8 ]
adcx r15, r9
adox r14, r8
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r14, [ rsp - 0x28 ]
setc r9b
clc
adcx rcx, r12
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x18 ]
adcx r8, r13
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x18 ], r8
mulx r8, r13, r14
mov [ rsp + 0x20 ], rcx
mulx rcx, r8, r13
adcx r12, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp + 0x28 ], r12
mov r12, 0x0 
adcx rdx, r12
mov [ rsp + 0x30 ], rdx
mov rdx, r13
clc
adcx rdx, r14
mov rdx, 0xffffffff 
mulx r12, r14, r10
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x38 ], rbx
mov byte [ rsp + 0x40 ], r9b
mulx r9, rbx, r10
setc r10b
clc
adcx rbx, r11
adcx r14, r9
adox rbx, rbp
adox r14, r15
mov rbp, 0xffffffff00000000 
mov rdx, r13
mulx r11, r13, rbp
setc r15b
clc
adcx r8, r11
movzx r9, r15b
lea r9, [ r9 + r12 ]
adox r9, rdi
mov rdi, 0xffffffff 
mulx r15, r12, rdi
adcx r12, rcx
seto dl
movzx rcx, byte [ rsp + 0x40 ]
mov r11, 0x0 
dec r11
adox rcx, r11
adox rbx, [ rsp - 0x38 ]
setc cl
clc
movzx r10, r10b
adcx r10, r11
adcx rbx, r13
adox r14, [ rsp + 0x38 ]
adcx r8, r14
adox r9, [ rsp + 0x8 ]
movzx rdx, dl
movzx r10, dl
adox r10, [ rsp + 0x10 ]
seto r13b
inc r11
adox rbx, [ rsp - 0x40 ]
mov rdx, 0xffffffffffffffff 
mulx r11, r14, rbx
movzx r11, cl
lea r11, [ r11 + r15 ]
adox r8, [ rsp - 0x8 ]
adcx r12, r9
adcx r11, r10
movzx r15, r13b
mov rcx, 0x0 
adcx r15, rcx
adox r12, [ rsp - 0x10 ]
adox r11, [ rsp - 0x18 ]
adox r15, [ rsp - 0x20 ]
mov r9, r14
clc
adcx r9, rbx
mulx r13, r9, r14
mov rdx, r14
mulx r10, r14, rbp
adcx r14, r8
seto bl
mov r8, -0x3 
inc r8
adox r9, r10
mulx rcx, r10, rdi
adcx r9, r12
adox r10, r13
mov rdx, 0x0 
adox rcx, rdx
mov r12, -0x3 
inc r12
adox r14, [ rsp + 0x0 ]
adox r9, [ rsp + 0x20 ]
adcx r10, r11
adox r10, [ rsp + 0x18 ]
adcx rcx, r15
adox rcx, [ rsp + 0x28 ]
movzx r12, bl
adcx r12, rdx
adox r12, [ rsp + 0x30 ]
mov r11, 0xffffffffffffffff 
mov rdx, r11
mulx rbx, r11, r14
mov rbx, r11
clc
adcx rbx, r14
mov rdx, r11
mulx rbx, r11, rbp
mov r15, 0xffffffffffffffff 
mulx r14, r13, r15
adcx r11, r9
seto r9b
inc r8
adox r13, rbx
adcx r13, r10
mulx rbx, r10, rdi
adox r10, r14
adcx r10, rcx
mov rcx, 0x0 
adox rbx, rcx
adcx rbx, r12
movzx r12, r9b
adc r12, 0x0
mov r9, r11
sub r9, 0x00000001
mov rdx, r13
sbb rdx, rbp
mov r14, r10
sbb r14, r15
mov rcx, rbx
sbb rcx, rdi
sbb r12, 0x00000000
cmovc rcx, rbx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], rcx
cmovc rdx, r13
mov [ r12 + 0x8 ], rdx
cmovc r9, r11
cmovc r14, r10
mov [ r12 + 0x10 ], r14
mov [ r12 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4481
; seed 4310724519538512 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 14016 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=103, initial num_batches=31): 803 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.057291666666666664
; number reverted permutation / tried permutation: 341 / 492 =69.309%
; number reverted decision / tried decision: 342 / 507 =67.456%
; validated in 4.239s
