SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
test al, al
adox r8, rcx
adox rbx, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, rdx
adox rdi, rbp
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], rdi
mulx rdi, rbp, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r11
mulx r11, r8, [ rsi + 0x10 ]
adcx rbp, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r10
mulx r10, r15, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rdi, rdx
clc
adcx r15, r13
adcx r8, r10
adcx rcx, r11
adcx r9, rdx
clc
adcx r14, r12
adcx rbp, r15
adcx rdi, r8
adox rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r14, rbp
mov r11, 0xffffffff00000001 
mov rdx, r11
mulx r10, r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r15, r12, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mulx rbp, r8, r14
adcx r11, rcx
mov rcx, 0xffffffff00000001 
mov rdx, rcx
mov [ rsp - 0x20 ], rbx
mulx rbx, rcx, r14
adcx r10, r9
setc r9b
clc
adcx rax, r13
adox rax, rdi
mov rdx, [ rsi + 0x10 ]
mulx r13, rdi, [ rsi + 0x8 ]
adcx rdi, [ rsp - 0x28 ]
adcx r12, r13
adox rdi, r11
adox r12, r10
mov rdx, 0x0 
adcx r15, rdx
mov r11, 0xffffffff 
mov rdx, r14
mulx r10, r14, r11
clc
adcx r14, rbp
mov rbp, 0x0 
adcx r10, rbp
clc
adcx r8, rdx
adcx r14, rax
adcx r10, rdi
mov rdx, [ rsi + 0x8 ]
mulx rax, r8, [ rsi + 0x10 ]
movzx rdx, r9b
adox rdx, r15
adcx rcx, r12
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r13, [ rsi + 0x0 ]
seto dl
mov r12, -0x3 
inc r12
adox r8, rdi
adcx rbx, r9
movzx r15, dl
adcx r15, rbp
mov rdx, [ rsi + 0x10 ]
mulx rdi, r9, rdx
clc
adcx r13, r14
adcx r8, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r14, [ rsi + 0x10 ]
adox r9, rax
mov rdx, r13
mulx rax, r13, r11
mov rbp, 0xffffffffffffffff 
mulx r11, r12, rbp
adcx r9, rcx
setc cl
clc
adcx r13, r11
mov r11, 0x0 
adcx rax, r11
clc
adcx r12, rdx
adcx r13, r8
adox r14, rdi
adox r10, r11
dec r11
movzx rcx, cl
adox rcx, r11
adox rbx, r14
adox r10, r15
adcx rax, r9
mov r12, 0xffffffff00000001 
mulx rdi, r15, r12
adcx r15, rbx
seto dl
inc r11
adox r13, [ rsp - 0x30 ]
adcx rdi, r10
adox rax, [ rsp - 0x38 ]
xchg rdx, r13
mulx rcx, r8, rbp
adox r15, [ rsp - 0x48 ]
movzx r9, r13b
adcx r9, r11
mov r14, 0xffffffff 
mulx r13, rbx, r14
adox rdi, [ rsp - 0x40 ]
clc
adcx rbx, rcx
adox r9, [ rsp - 0x20 ]
seto r10b
mov rcx, -0x3 
inc rcx
adox r8, rdx
adox rbx, rax
adcx r13, r11
adox r13, r15
mulx rax, r8, r12
adox r8, rdi
adox rax, r9
movzx rdx, r10b
adox rdx, r11
mov r15, rbx
sub r15, rbp
mov rdi, r13
sbb rdi, r14
mov r10, r8
sbb r10, 0x00000000
mov r9, rax
sbb r9, r12
sbb rdx, 0x00000000
cmovc r9, rax
cmovc r10, r8
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r9
cmovc rdi, r13
mov [ rdx + 0x8 ], rdi
cmovc r15, rbx
mov [ rdx + 0x0 ], r15
mov [ rdx + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.4943
; seed 1388460636738768 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1767645 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=96, initial num_batches=31): 109082 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.061710354737518
; number reverted permutation / tried permutation: 74578 / 90205 =82.676%
; number reverted decision / tried decision: 39779 / 89794 =44.300%
; validated in 1.908s
