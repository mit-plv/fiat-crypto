SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 224
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r15
mulx r15, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rdi
mulx rdi, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], r8
mulx r8, rcx, [ rsi + 0x10 ]
test al, al
adox r13, r8
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x8 ], r13
mulx r13, r8, r10
adcx rdi, r15
adcx r9, r12
mov rdx, [ rax + 0x10 ]
mulx r12, r15, [ rsi + 0x10 ]
adox r15, r14
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x10 ], r9
mulx r9, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r15
mulx r15, rdi, [ rax + 0x10 ]
adcx rbp, rbx
setc dl
clc
adcx r14, r11
adox r12, [ rsp - 0x10 ]
adcx rdi, r9
mov r11, [ rsp - 0x18 ]
mov rbx, 0x0 
adox r11, rbx
mov r9b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
adcx rbx, r15
mov rdx, [ rsi + 0x8 ]
mov byte [ rsp + 0x30 ], r9b
mulx r9, r15, [ rax + 0x8 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x38 ], r11
mov [ rsp + 0x40 ], r12
mulx r12, r11, r10
adc rbp, 0x0
mov rdx, 0xffffffff00000001 
mov [ rsp + 0x48 ], rcx
mov [ rsp + 0x50 ], rbp
mulx rbp, rcx, r10
xor rdx, rdx
adox r11, r13
adcx r15, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x20 ]
mov r13, [ rsp - 0x28 ]
adcx r13, [ rsp + 0x0 ]
adox r12, rdx
mov [ rsp + 0x58 ], r13
mov r13, -0x3 
inc r13
adox r8, r10
mov r8, [ rsp - 0x8 ]
adcx r8, rdx
adox r11, r14
clc
adcx r11, [ rsp - 0x40 ]
mov r10, 0xffffffff 
mov rdx, r11
mulx r14, r11, r10
adox r12, rdi
adox rcx, rbx
adcx r15, r12
adox rbp, [ rsp + 0x50 ]
adcx r9, rcx
adcx rbp, [ rsp + 0x58 ]
mov rdi, 0xffffffffffffffff 
mulx r12, rbx, rdi
mov rcx, 0xffffffff00000001 
mulx r10, r13, rcx
seto cl
mov rdi, -0x2 
inc rdi
adox r11, r12
mov r12, 0x0 
adox r14, r12
mov rdi, -0x3 
inc rdi
adox rbx, rdx
adox r11, r15
adox r14, r9
movzx rbx, cl
adcx rbx, r8
setc r8b
clc
adcx r11, [ rsp + 0x48 ]
adox r13, rbp
mov rdx, 0xffffffffffffffff 
mulx rcx, r15, r11
adox r10, rbx
mov r9, 0xffffffff 
mov rdx, r11
mulx rbp, r11, r9
adcx r14, [ rsp + 0x8 ]
adcx r13, [ rsp + 0x20 ]
adcx r10, [ rsp + 0x40 ]
movzx rbx, r8b
adox rbx, r12
adcx rbx, [ rsp + 0x38 ]
mov r8, -0x3 
inc r8
adox r15, rdx
setc r8b
clc
adcx r11, rcx
adox r11, r14
adcx rbp, r12
adox rbp, r13
mov r15, 0xffffffff00000001 
mulx r14, rcx, r15
clc
adcx r11, [ rsp - 0x38 ]
adox rcx, r10
adox r14, rbx
adcx rbp, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x10 ]
mov rdx, 0xffffffffffffffff 
mulx r10, r13, r11
mov rdx, r9
mulx rbx, r9, r11
adcx r14, [ rsp + 0x28 ]
movzx r12, r8b
mov rdi, 0x0 
adox r12, rdi
mov rdx, r11
mulx r8, r11, r15
mov r15, -0x3 
inc r15
adox r9, r10
adox rbx, rdi
mov r10, -0x3 
inc r10
adox r13, rdx
adox r9, rbp
adox rbx, rcx
adox r11, r14
setc r10b
seto r13b
mov rdx, r9
mov rbp, 0xffffffffffffffff 
sub rdx, rbp
movzx rcx, byte [ rsp + 0x30 ]
mov r14, [ rsp - 0x48 ]
lea rcx, [ rcx + r14 ]
mov r14, rbx
mov rdi, 0xffffffff 
sbb r14, rdi
mov r15, 0x0 
dec r15
movzx r10, r10b
adox r10, r15
adox r12, rcx
seto r10b
mov rcx, r11
sbb rcx, 0x00000000
inc r15
mov r15, -0x1 
movzx r13, r13b
adox r13, r15
adox r12, r8
movzx r8, r10b
mov r13, 0x0 
adox r8, r13
mov r10, r12
mov r13, 0xffffffff00000001 
sbb r10, r13
sbb r8, 0x00000000
cmovc rdx, r9
cmovc r14, rbx
cmovc rcx, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], rcx
cmovc r10, r12
mov [ r8 + 0x0 ], rdx
mov [ r8 + 0x18 ], r10
mov [ r8 + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 224
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5878
; seed 4048432255942674 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7478 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=140, initial num_batches=31): 482 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06445573682802888
; number reverted permutation / tried permutation: 367 / 497 =73.843%
; number reverted decision / tried decision: 348 / 502 =69.323%
; validated in 2.059s
