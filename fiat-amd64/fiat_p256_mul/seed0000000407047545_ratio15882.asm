SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r8, rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
add rcx, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mulx r15, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rcx, r11
adox rdi, r15
adox r13, r9
mov r11, 0xffffffff 
mov rdx, r10
mulx r15, r10, r11
mov r9, 0x0 
adox r14, r9
mov r11, -0x3 
inc r11
adox r10, r8
adox r15, r9
adcx r10, rcx
adcx r15, rdi
mov r8, 0xffffffff00000001 
mulx rdi, rcx, r8
adcx rcx, r13
mov rdx, [ rax + 0x10 ]
mulx r9, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, [ rax + 0x18 ]
mov rdx, -0x2 
inc rdx
adox rbp, rbx
adox r13, r12
adox r11, r9
seto bl
inc rdx
adox r10, [ rsp - 0x48 ]
adcx rdi, r14
adox rbp, r15
mov r12, 0xffffffff 
mov rdx, r10
mulx r14, r10, r12
mov r15, rdx
mov rdx, [ rax + 0x8 ]
mulx r12, r9, [ rsi + 0x18 ]
adox r13, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mulx r13, rcx, [ rax + 0x0 ]
setc dl
clc
adcx r9, r13
mov r13b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], rcx
mulx rcx, r9, [ rax + 0x10 ]
adcx r9, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r9
mulx r9, r12, [ rax + 0x18 ]
adcx r12, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x20 ], r12
mulx r12, rcx, r15
setc dl
clc
adcx r10, r12
mov r12, 0x0 
adcx r14, r12
movzx r12, dl
lea r12, [ r12 + r9 ]
clc
adcx rcx, r15
adcx r10, rbp
movzx rcx, bl
lea rcx, [ rcx + r8 ]
adox r11, rdi
movzx r8, r13b
adox r8, rcx
mov rbx, 0xffffffff00000001 
mov rdx, r15
mulx r13, r15, rbx
adcx r14, [ rsp - 0x40 ]
adcx r15, r11
mov rdx, [ rax + 0x8 ]
mulx rbp, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx rcx, r9, [ rsi + 0x10 ]
seto dl
mov r11, -0x2 
inc r11
adox r9, r10
adcx r13, r8
movzx r10, dl
mov r8, 0x0 
adcx r10, r8
mov rdx, 0xffffffff 
mulx r11, r8, r9
clc
adcx rdi, rcx
mov rdx, [ rax + 0x10 ]
mulx rbx, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r11
mulx r11, r12, [ rsi + 0x10 ]
adcx rcx, rbp
adox rdi, r14
adcx r12, rbx
adox rcx, r15
adox r12, r13
mov rdx, 0xffffffffffffffff 
mulx r15, r14, r9
seto bpl
mov r13, -0x2 
inc r13
adox r14, r9
mov r14, 0x0 
adcx r11, r14
clc
movzx rbp, bpl
adcx rbp, r13
adcx r10, r11
setc bl
clc
adcx r8, r15
adox r8, rdi
mov rdi, [ rsp - 0x10 ]
adcx rdi, r14
adox rdi, rcx
clc
adcx r8, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
mov rcx, 0xffffffff00000001 
mov rdx, r9
mulx rbp, r9, rcx
adox r9, r12
adox rbp, r10
mov rdx, r8
mulx r12, r8, rcx
movzx r15, bl
adox r15, r14
mov r11, 0xffffffff 
mulx rbx, r10, r11
adcx r9, [ rsp - 0x28 ]
adcx rbp, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x18 ]
mov r14, 0xffffffffffffffff 
mulx r11, r13, r14
mov r14, -0x2 
inc r14
adox r10, r11
setc r11b
clc
adcx r13, rdx
mov r13, 0x0 
adox rbx, r13
adcx r10, rdi
adcx rbx, r9
adcx r8, rbp
adcx r12, r15
movzx rdx, r11b
adc rdx, 0x0
mov rdi, r10
mov r9, 0xffffffffffffffff 
sub rdi, r9
mov rbp, rbx
mov r11, 0xffffffff 
sbb rbp, r11
mov r15, r8
sbb r15, 0x00000000
mov r13, r12
sbb r13, rcx
sbb rdx, 0x00000000
cmovc r15, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x10 ], r15
cmovc rbp, rbx
cmovc rdi, r10
mov [ rdx + 0x0 ], rdi
cmovc r13, r12
mov [ rdx + 0x18 ], r13
mov [ rdx + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5882
; seed 3479804633874500 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1198655 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=139, initial num_batches=31): 82719 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06900984853857031
; number reverted permutation / tried permutation: 67202 / 90344 =74.385%
; number reverted decision / tried decision: 43917 / 89655 =48.984%
; validated in 1.707s
