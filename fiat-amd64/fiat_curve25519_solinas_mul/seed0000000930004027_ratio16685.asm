SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
xor rdx, rdx
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r14
mulx r14, r12, [ rax + 0x8 ]
adox r12, r11
mov rdx, 0x0 
adox rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rax + 0x0 ]
adcx rcx, r15
adcx rdi, r12
mov rdx, [ rax + 0x8 ]
mulx r12, r15, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r11, r12
adox r10, rcx
mov rdx, [ rax + 0x10 ]
mulx r12, rcx, [ rsi + 0x10 ]
adox rcx, rdi
mov rdx, 0x0 
mov rdi, rdx
adcx rdi, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r12
mulx r12, rbx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rbp
mulx rbp, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r9
mulx r9, r12, [ rax + 0x8 ]
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx r12, r11
adcx r13, r10
adcx r8, rcx
adox rbx, rdi
mov r11, rdx
adox r11, rbp
mov rdx, [ rax + 0x0 ]
mulx rcx, r10, [ rsi + 0x0 ]
adcx r14, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbp, rdi, [ rax + 0x0 ]
mov rdx, 0x0 
mov rbx, rdx
adcx rbx, r11
setc r11b
clc
adcx rdi, rcx
seto cl
mov [ rsp - 0x10 ], r10
mov r10, -0x3 
inc r10
adox r15, rdi
mov rdx, [ rax + 0x18 ]
mulx r10, rdi, [ rsi + 0x18 ]
movzx rdx, cl
lea rdx, [ rdx + r10 ]
adcx rbp, r12
adcx r9, r13
adcx r8, [ rsp - 0x18 ]
adcx r14, [ rsp - 0x20 ]
mov r12, 0x0 
movzx r11, r11b
lea rdx, [ rdx + r12 ]
lea rdx, [ rdx + r11 ]
adox rbp, [ rsp - 0x28 ]
adox r9, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
adox r14, [ rsp - 0x38 ]
mov r13, 0x26 
xchg rdx, r13
mulx r11, rcx, r14
mulx r14, r10, r8
adcx rdi, rbx
adcx r13, r12
adox rdi, [ rsp - 0x30 ]
mulx r8, rbx, rdi
clc
adcx rcx, r15
adox r13, r12
mulx rdi, r15, r13
adcx rbx, rbp
mov rbp, -0x3 
inc rbp
adox r10, [ rsp - 0x10 ]
adcx r15, r9
adcx rdi, r12
adox r14, rcx
adox r11, rbx
adox r8, r15
adox rdi, r12
mulx rcx, r9, rdi
xor rcx, rcx
adox r9, r10
mov r12, rcx
adox r12, r14
mov r13, rcx
adox r13, r11
mov rbx, rcx
adox rbx, r8
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rbx
mov [ r10 + 0x10 ], r13
mov r15, rcx
cmovo r15, rdx
adcx r9, r15
mov [ r10 + 0x8 ], r12
mov [ r10 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.6685
; seed 4335329616729147 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 755436 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=197, initial num_batches=31): 73460 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09724185768218618
; number reverted permutation / tried permutation: 68591 / 89702 =76.465%
; number reverted decision / tried decision: 38861 / 90297 =43.037%
; validated in 0.428s
