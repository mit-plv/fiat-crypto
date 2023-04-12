SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 192
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r9
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r10
mulx r10, r12, r9
xor rdx, rdx
adox r15, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r15
mulx r15, r11, [ rax + 0x10 ]
adcx rcx, rbx
adcx r11, r8
mov rdx, [ rax + 0x18 ]
mulx rbx, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r14
mulx r14, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], r11
mulx r11, r13, [ rax + 0x10 ]
adcx r8, r15
adox rbp, rdi
mov rdx, 0xffffffff 
mulx r15, rdi, r9
mov rdx, 0x0 
adcx rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], r13
mulx r13, r11, [ rax + 0x18 ]
clc
adcx rdi, r10
adox r11, r14
mov rdx, 0x0 
adox r13, rdx
mov r10, -0x3 
inc r10
adox r12, r9
adcx r15, rdx
adox rdi, rcx
adox r15, [ rsp - 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r9, r12, [ rsi + 0x10 ]
adox r8, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, [ rax + 0x8 ]
adox rbx, [ rsp - 0x28 ]
clc
adcx rcx, r9
adcx r14, [ rsp - 0x30 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, [ rax + 0x18 ]
adcx r9, [ rsp - 0x48 ]
setc dl
clc
adcx rdi, [ rsp - 0x40 ]
mov [ rsp + 0x0 ], r10
mov r10, 0xffffffffffffffff 
xchg rdx, rdi
mov byte [ rsp + 0x8 ], dil
mov [ rsp + 0x10 ], r9
mulx r9, rdi, r10
adcx r15, [ rsp - 0x38 ]
adcx rbp, r8
mov r8, 0xffffffff 
mov [ rsp + 0x18 ], r14
mulx r14, r10, r8
adcx r11, rbx
seto bl
mov r8, -0x2 
inc r8
adox r10, r9
mov r9, 0x0 
adox r14, r9
movzx r9, bl
adcx r9, r13
inc r8
adox rdi, rdx
adox r10, r15
adox r14, rbp
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mulx rbx, r13, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000001 
mulx rbp, r15, rdi
adox r15, r11
setc dil
clc
adcx r12, r10
adox rbp, r9
mov r11, 0xffffffff 
mov rdx, r12
mulx r9, r12, r11
adcx rcx, r14
movzx r10, dil
adox r10, r8
adcx r15, [ rsp + 0x18 ]
adcx rbp, [ rsp + 0x10 ]
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, r14, [ rsi + 0x18 ]
mov rdx, -0x2 
inc rdx
adox r14, rbx
movzx rbx, byte [ rsp + 0x8 ]
mov rdx, [ rsp + 0x0 ]
lea rbx, [ rbx + rdx ]
adox r8, [ rsp - 0x8 ]
adcx rbx, r10
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x18 ]
adox r10, [ rsp - 0x10 ]
mov rdx, 0x0 
adox r11, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x20 ], r11
mov [ rsp + 0x28 ], r10
mulx r10, r11, rdi
mov rdx, -0x2 
inc rdx
adox r11, rdi
setc r11b
clc
adcx r12, r10
adox r12, rcx
mov rcx, 0x0 
adcx r9, rcx
clc
adcx r13, r12
mov r10, 0xffffffff00000001 
mov rdx, r10
mulx r12, r10, rdi
adox r9, r15
adox r10, rbp
adox r12, rbx
mulx r15, rdi, r13
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx rbx, rbp, r13
mov rcx, 0xffffffff 
mov rdx, rcx
mov [ rsp + 0x30 ], r15
mulx r15, rcx, r13
setc dl
clc
adcx rcx, rbx
movzx rbx, r11b
mov [ rsp + 0x38 ], rdi
mov rdi, 0x0 
adox rbx, rdi
adc r15, 0x0
add dl, 0x7F
adox r9, r14
adox r8, r10
adcx rbp, r13
adcx rcx, r9
adcx r15, r8
adox r12, [ rsp + 0x28 ]
adox rbx, [ rsp + 0x20 ]
adcx r12, [ rsp + 0x38 ]
adcx rbx, [ rsp + 0x30 ]
seto bpl
adc bpl, 0x0
movzx rbp, bpl
mov r14, rcx
mov r11, 0xffffffffffffffff 
sub r14, r11
mov r13, r15
mov rdx, 0xffffffff 
sbb r13, rdx
mov r10, r12
sbb r10, 0x00000000
mov r9, rbx
mov r8, 0xffffffff00000001 
sbb r9, r8
movzx r8, bpl
sbb r8, 0x00000000
cmovc r10, r12
cmovc r14, rcx
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r10
mov [ r8 + 0x0 ], r14
cmovc r13, r15
cmovc r9, rbx
mov [ r8 + 0x8 ], r13
mov [ r8 + 0x18 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.5887
; seed 2125471332701549 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 938904 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=120, initial num_batches=31): 62862 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06695253188824417
; number reverted permutation / tried permutation: 65453 / 89813 =72.877%
; number reverted decision / tried decision: 50302 / 90186 =55.776%
; validated in 1.408s
