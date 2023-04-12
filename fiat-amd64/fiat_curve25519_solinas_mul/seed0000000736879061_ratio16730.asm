SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
add r15, r8
adcx r10, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
adc r14, 0x0
test al, al
adox r9, r15
adox rdi, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r15, [ rax + 0x0 ]
mov rdx, 0x0 
mov [ rsp - 0x38 ], rcx
mov rcx, rdx
adox rcx, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r13
mulx r13, r14, [ rax + 0x8 ]
adcx r15, r13
adcx r10, r9
mov rdx, [ rsi + 0x10 ]
mulx r13, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r12
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r12, rdx
adcx r9, rdi
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x18 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
adcx rdi, rcx
mov rdx, -0x2 
inc rdx
adox r8, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, rcx, [ rax + 0x10 ]
adox rcx, r10
adox rbp, r9
adox r11, rdi
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rax + 0x0 ]
mov rdx, 0x0 
mov rdi, rdx
adcx rdi, r12
setc r12b
clc
adcx r10, rbx
mov rbx, rdx
adox rbx, rdi
adcx r9, r8
seto r8b
mov rdi, -0x3 
inc rdi
adox r14, r10
adcx rcx, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x18 ]
adox r9, [ rsp - 0x38 ]
adox rcx, [ rsp - 0x40 ]
adox r15, rbp
adox r11, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rax + 0x18 ]
movzx rdx, r12b
lea rdx, [ rdx + rbp ]
adcx r10, rbx
adox r13, r10
mov r12, 0x0 
movzx r8, r8b
lea rdx, [ rdx + r12 ]
lea rdx, [ rdx + r8 ]
adcx rdx, r12
adox rdx, r12
mov r8, 0x26 
xchg rdx, r8
mulx rbp, rbx, r15
mulx r10, r15, r11
mulx r12, r11, r8
xor r8, r8
adox r15, r14
adcx rbx, [ rsp - 0x48 ]
adcx rbp, r15
mulx r15, r14, r13
adox r14, r9
adox r11, rcx
adcx r10, r14
adcx r15, r11
adox r12, r8
adc r12, 0x0
mulx rcx, r9, r12
xor rcx, rcx
adox r9, rbx
mov r8, rcx
adox r8, rbp
mov r13, rcx
adox r13, r10
mov rbx, rcx
adox rbx, r15
mov rbp, rcx
cmovo rbp, rdx
adcx r9, rbp
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x10 ], r13
mov [ r14 + 0x8 ], r8
mov [ r14 + 0x0 ], r9
mov [ r14 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.6730
; seed 0863994697597156 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 773661 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 67125 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08676280696584163
; number reverted permutation / tried permutation: 67801 / 89662 =75.618%
; number reverted decision / tried decision: 39516 / 90337 =43.743%
; validated in 0.419s
