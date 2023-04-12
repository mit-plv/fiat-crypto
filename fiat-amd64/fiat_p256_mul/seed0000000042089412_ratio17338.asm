SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 208
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r10
mulx r10, r13, r15
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rbx
mulx rbx, r8, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], r8
mulx r8, rbx, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], rcx
mulx rcx, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], rcx
mov [ rsp + 0x0 ], rbx
mulx rbx, rcx, [ rsi + 0x10 ]
add rcx, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], rcx
mulx rcx, r11, [ rax + 0x10 ]
adcx r11, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x10 ], r11
mulx r11, rbx, [ rax + 0x18 ]
adcx rbx, rcx
adc r11, 0x0
test al, al
adox rbp, rdi
mov rdx, [ rax + 0x10 ]
mulx rcx, rdi, [ rsi + 0x0 ]
adcx r13, r8
mov rdx, 0x0 
adcx r10, rdx
adox rdi, r12
adox r9, rcx
mov rdx, [ rsi + 0x18 ]
mulx r8, r12, [ rax + 0x8 ]
clc
adcx r12, r14
adcx r8, [ rsp - 0x10 ]
mov rdx, [ rsp - 0x30 ]
mov r14, 0x0 
adox rdx, r14
mov rcx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r8
mulx r8, r14, [ rsi + 0x18 ]
adcx r14, [ rsp - 0x38 ]
adc r8, 0x0
test al, al
adox r15, [ rsp - 0x18 ]
adox r13, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r14
mulx r14, r8, [ rsi + 0x8 ]
adcx r15, r14
adox r10, rdi
adox r9, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x10 ]
adcx rdi, rbp
adcx r14, [ rsp + 0x0 ]
setc dl
clc
adcx r8, r13
mov r13, 0xffffffff 
xchg rdx, r8
mov [ rsp + 0x30 ], r12
mulx r12, rbp, r13
adcx r15, r10
adox rcx, [ rsp - 0x28 ]
mov r10, 0xffffffff00000001 
mov [ rsp + 0x38 ], r11
mulx r11, r13, r10
mov r10, 0xffffffffffffffff 
mov [ rsp + 0x40 ], rbx
mov [ rsp + 0x48 ], r11
mulx r11, rbx, r10
adcx rdi, r9
adcx r14, rcx
movzx r9, r8b
mov rcx, [ rsp - 0x8 ]
lea r9, [ r9 + rcx ]
setc cl
clc
adcx rbp, r11
movzx r8, cl
adox r8, r9
mov r11, 0x0 
adcx r12, r11
clc
adcx rbx, rdx
adcx rbp, r15
seto bl
mov rdx, -0x3 
inc rdx
adox rbp, [ rsp - 0x40 ]
adcx r12, rdi
mov rdx, rbp
mulx r15, rbp, r10
adox r12, [ rsp + 0x8 ]
adcx r13, r14
adcx r8, [ rsp + 0x48 ]
adox r13, [ rsp + 0x10 ]
adox r8, [ rsp + 0x40 ]
movzx rdi, bl
adcx rdi, r11
adox rdi, [ rsp + 0x38 ]
mov rcx, 0xffffffff 
mulx r9, r14, rcx
clc
adcx rbp, rdx
seto bpl
mov rbx, -0x3 
inc rbx
adox r14, r15
adcx r14, r12
adox r9, r11
adcx r9, r13
mov r15, -0x3 
inc r15
adox r14, [ rsp - 0x48 ]
mov r15, 0xffffffff00000001 
mulx r13, r12, r15
adcx r12, r8
adox r9, [ rsp + 0x30 ]
adcx r13, rdi
mov rdx, r10
mulx r8, r10, r14
movzx rdi, bpl
adcx rdi, r11
adox r12, [ rsp + 0x18 ]
mov rdx, r14
mulx rbp, r14, rcx
clc
adcx r14, r8
adcx rbp, r11
clc
adcx r10, rdx
adcx r14, r9
adcx rbp, r12
adox r13, [ rsp + 0x28 ]
mulx r9, r10, r15
adcx r10, r13
adox rdi, [ rsp + 0x20 ]
adcx r9, rdi
seto dl
adc dl, 0x0
movzx rdx, dl
mov r8, r14
mov r12, 0xffffffffffffffff 
sub r8, r12
mov r13, rbp
sbb r13, rcx
mov rdi, r10
sbb rdi, 0x00000000
mov r11, r9
sbb r11, r15
movzx rbx, dl
sbb rbx, 0x00000000
cmovc r13, rbp
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r13
cmovc r11, r9
cmovc rdi, r10
mov [ rbx + 0x10 ], rdi
cmovc r8, r14
mov [ rbx + 0x0 ], r8
mov [ rbx + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 208
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.7338
; seed 1038622392636226 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1240978 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=118, initial num_batches=31): 76217 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.061416882491067526
; number reverted permutation / tried permutation: 64033 / 89387 =71.636%
; number reverted decision / tried decision: 44257 / 90612 =48.842%
; validated in 1.69s
