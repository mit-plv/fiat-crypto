SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 168
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
test al, al
adox r11, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbp, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], rbx
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r13
mulx r13, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rbx
mulx rbx, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r9
mov [ rsp - 0x10 ], r8
mulx r8, r9, [ rsi + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r12
mulx r12, rbx, rbp
adcx r11, r14
adcx r9, r13
adcx rax, r8
mov r14, 0x0 
adcx r10, r14
clc
adcx rbx, rdi
adcx r12, r14
mov rdx, [ rsi + 0x10 ]
mulx r13, rdi, rdx
clc
adcx r15, rbp
adcx rbx, r11
adcx r12, r9
adox rdi, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r15, [ rsi + 0x18 ]
adox r15, r13
mov rdx, 0xffffffff00000001 
mulx r11, r8, rbp
adox rcx, r14
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, -0x3 
inc rdx
adox r9, [ rsp + 0x0 ]
mov r13, [ rsp - 0x8 ]
adox r13, [ rsp - 0x10 ]
adcx r8, rax
mov rdx, [ rsi + 0x8 ]
mulx r14, rax, [ rsi + 0x18 ]
adcx r11, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
adox rax, [ rsp - 0x18 ]
setc dl
clc
adcx rbp, rbx
adcx r9, r12
adcx r13, r8
mov rbx, 0x0 
adox r14, rbx
adcx rax, r11
mov r12, [ rsp - 0x20 ]
mov r8, -0x3 
inc r8
adox r12, [ rsp - 0x28 ]
adox r10, [ rsp - 0x30 ]
movzx r11, dl
adcx r11, r14
mov rdx, [ rsi + 0x18 ]
mulx rbx, r14, rdx
adox r14, rcx
mov rdx, 0xffffffff 
mulx r8, rcx, rbp
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r14
mov [ rsp + 0x18 ], r10
mulx r10, r14, rbp
setc dl
clc
adcx rcx, r10
seto r10b
mov [ rsp + 0x20 ], r12
mov r12, -0x2 
inc r12
adox r14, rbp
adox rcx, r9
movzx r14, r10b
lea r14, [ r14 + rbx ]
mov r9, 0xffffffff00000001 
xchg rdx, rbp
mulx r10, rbx, r9
mov rdx, 0x0 
adcx r8, rdx
adox r8, r13
adox rbx, rax
clc
adcx rcx, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
adox r10, r11
movzx r13, bpl
adox r13, rdx
adcx rdi, rbx
mov rax, 0xffffffffffffffff 
mov rdx, rcx
mulx rbp, rcx, rax
adcx r15, r10
inc r12
adox rcx, rdx
adcx r13, [ rsp + 0x8 ]
mov rcx, 0xffffffff 
mulx rbx, r11, rcx
setc r10b
clc
adcx r11, rbp
adox r11, r8
adcx rbx, r12
mulx rbp, r8, r9
adox rbx, rdi
adox r8, r15
adox rbp, r13
movzx rdx, r10b
adox rdx, r12
test al, al
adox r11, [ rsp - 0x38 ]
adox rbx, [ rsp + 0x20 ]
xchg rdx, rax
mulx r15, rdi, r11
adcx rdi, r11
adox r8, [ rsp + 0x18 ]
adox rbp, [ rsp + 0x10 ]
adox r14, rax
mov rdx, rcx
mulx rcx, rdi, r11
seto r10b
mov r13, -0x3 
inc r13
adox rdi, r15
adcx rdi, rbx
adox rcx, r12
adcx rcx, r8
mov rdx, r11
mulx rax, r11, r9
adcx r11, rbp
adcx rax, r14
movzx rdx, r10b
adc rdx, 0x0
mov rbx, rdi
mov r15, 0xffffffffffffffff 
sub rbx, r15
mov r8, rcx
mov rbp, 0xffffffff 
sbb r8, rbp
mov r10, r11
sbb r10, 0x00000000
mov r14, rax
sbb r14, r9
sbb rdx, 0x00000000
cmovc r10, r11
cmovc r14, rax
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r14
mov [ rdx + 0x10 ], r10
cmovc rbx, rdi
cmovc r8, rcx
mov [ rdx + 0x0 ], rbx
mov [ rdx + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.5749
; seed 3194286271363475 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1145594 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=136, initial num_batches=31): 74769 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06526657786266339
; number reverted permutation / tried permutation: 66614 / 89707 =74.257%
; number reverted decision / tried decision: 42532 / 90292 =47.105%
; validated in 1.462s
