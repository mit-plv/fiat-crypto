SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r10
mov r9, 0xffffffff 
mov rdx, r10
mov [ rsp - 0x48 ], r14
mulx r14, r10, r9
adcx r10, rbx
mov rbx, 0x0 
adcx r14, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mulx r13, r9, [ rax + 0x18 ]
clc
adcx rbp, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r13
mulx r13, r11, [ rsi + 0x0 ]
adcx rcx, r12
adcx r11, r8
adox r10, rbp
adox r14, rcx
mov rdx, 0xffffffff00000001 
mulx r12, r8, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x30 ], r9
mulx r9, rcx, [ rsi + 0x8 ]
adox r8, r11
mov rdx, 0x0 
adcx r13, rdx
clc
adcx rcx, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r11, [ rax + 0x10 ]
adcx r11, r9
adox r12, r13
adcx r15, rbp
seto dl
mov r9, -0x2 
inc r9
adox rbx, r10
mov r10, 0xffffffffffffffff 
xchg rdx, rbx
mulx rbp, r13, r10
mov r9, 0xffffffff 
mov byte [ rsp - 0x28 ], bl
mulx rbx, r10, r9
adox rcx, r14
adox r11, r8
adox r15, r12
mov r14, 0x0 
adcx rdi, r14
clc
adcx r10, rbp
adcx rbx, r14
clc
adcx r13, rdx
adcx r10, rcx
adcx rbx, r11
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, [ rax + 0x0 ]
movzx rdx, byte [ rsp - 0x28 ]
adox rdx, rdi
seto bpl
mov rcx, -0x3 
inc rcx
adox r8, r10
mov r11, 0xffffffff00000001 
xchg rdx, r11
mulx r10, rdi, r13
adcx rdi, r15
mulx r15, r13, r8
mov rdx, [ rax + 0x8 ]
mulx rcx, r14, [ rsi + 0x10 ]
adcx r10, r11
movzx rdx, bpl
mov r11, 0x0 
adcx rdx, r11
clc
adcx r14, r12
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx r11, rbp, [ rsi + 0x10 ]
adcx rbp, rcx
adox r14, rbx
adox rbp, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbx, [ rax + 0x18 ]
adcx rbx, r11
adox rbx, r10
mov rdx, 0x0 
adcx rdi, rdx
adox rdi, r12
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx r10, rcx, r8
mov rdx, r8
mulx r12, r8, r9
clc
adcx rcx, rdx
setc cl
clc
adcx r8, r10
seto dl
mov r11, -0x1 
inc r11
mov r10, -0x1 
movzx rcx, cl
adox rcx, r10
adox r14, r8
adcx r12, r11
mov cl, dl
mov rdx, [ rax + 0x0 ]
mulx r11, r8, [ rsi + 0x18 ]
clc
adcx r8, r14
adox r12, rbp
adox r13, rbx
adox r15, rdi
mov rdx, 0xffffffffffffffff 
mulx rbx, rbp, r8
movzx rdi, cl
mov r14, 0x0 
adox rdi, r14
mov rcx, -0x3 
inc rcx
adox r11, [ rsp - 0x40 ]
adcx r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r14, r12, [ rax + 0x10 ]
adox r12, [ rsp - 0x48 ]
adcx r12, r13
adox r14, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
mov r13, 0x0 
adox rdx, r13
xchg rdx, r9
mulx rcx, r13, r8
adcx r14, r15
inc r10
adox r13, rbx
adox rcx, r10
mov r15, -0x3 
inc r15
adox rbp, r8
adox r13, r11
mov rbp, 0xffffffff00000001 
mov rdx, rbp
mulx rbx, rbp, r8
adox rcx, r12
adcx r9, rdi
adox rbp, r14
adox rbx, r9
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rdi, r13
mov r11, 0xffffffffffffffff 
sub rdi, r11
mov r12, rcx
mov r14, 0xffffffff 
sbb r12, r14
mov r9, rbp
sbb r9, 0x00000000
mov r10, rbx
sbb r10, rdx
movzx r15, r8b
sbb r15, 0x00000000
cmovc r10, rbx
cmovc r12, rcx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], r12
cmovc rdi, r13
mov [ r15 + 0x0 ], rdi
cmovc r9, rbp
mov [ r15 + 0x10 ], r9
mov [ r15 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.5714
; seed 1130402005019340 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1647639 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=87, initial num_batches=31): 105940 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0642980652922151
; number reverted permutation / tried permutation: 65883 / 90130 =73.098%
; number reverted decision / tried decision: 37609 / 89869 =41.849%
; validated in 2.223s
