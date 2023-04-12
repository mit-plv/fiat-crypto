SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
add r9, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r8, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x8 ]
adcx r10, rbp
mov rdx, -0x2 
inc rdx
adox r14, r9
mov rdx, [ rax + 0x18 ]
mulx rbp, r9, [ rsi + 0x8 ]
adox rbx, r10
mov rdx, 0x0 
adcx rbp, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r8
mulx r8, r13, [ rax + 0x0 ]
clc
adcx r13, rdi
adcx r8, r14
mov rdx, [ rsi + 0x10 ]
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], rcx
mulx rcx, rdi, [ rsi + 0x10 ]
adcx r14, rbx
mov rdx, 0x0 
mov rbx, rdx
adox rbx, rbp
adox rcx, rdx
adcx r12, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rbp, [ rax + 0x8 ]
mov rdx, 0x0 
mov [ rsp - 0x28 ], r10
mov r10, rdx
adcx r10, rcx
mov rcx, -0x3 
inc rcx
adox rbp, r13
mov rdx, [ rax + 0x10 ]
mulx rcx, r13, [ rsi + 0x8 ]
adox r13, r8
adox r15, r14
adox r11, r12
mov rdx, [ rsi + 0x8 ]
mulx r14, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r12, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x18 ], r12
mov r12, -0x2 
inc r12
adox r8, rcx
adox r14, rbp
adox rbx, r13
adox r9, r15
mov rbp, 0x0 
setc r13b
clc
movzx rdx, dl
adcx rdx, r12
adcx r10, rbp
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x18 ]
movzx rdx, r13b
lea rdx, [ rdx + rcx ]
adcx rdx, rbp
adox rdi, r11
adox r15, r10
clc
adcx r8, [ rsp - 0x28 ]
adcx r14, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x40 ]
adcx r9, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x38 ]
mov r13, 0x26 
xchg rdx, rdi
mulx r10, r11, r13
adox rdi, rbp
adcx r15, [ rsp - 0x48 ]
adcx rdi, rbp
test al, al
adox r11, r8
mov rdx, r9
mulx rcx, r9, r13
adcx r9, [ rsp - 0x18 ]
mov rdx, r13
mulx r8, r13, r15
adcx rcx, r11
adox r13, r14
mulx r15, r14, rdi
adcx r10, r13
adox r14, rbx
adcx r8, r14
adox r15, rbp
adc r15, 0x0
mulx rdi, rbx, r15
xor rdi, rdi
adox rbx, r9
mov rbp, rdi
adox rbp, rcx
mov r11, rdi
adox r11, r10
mov r9, rdi
adox r9, r8
mov rcx, rdi
cmovo rcx, rdx
adcx rbx, rcx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rbx
mov [ r13 + 0x8 ], rbp
mov [ r13 + 0x18 ], r9
mov [ r13 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.6949
; seed 2865314735309921 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 784623 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=197, initial num_batches=31): 73441 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09360036603566299
; number reverted permutation / tried permutation: 66392 / 89975 =73.789%
; number reverted decision / tried decision: 37847 / 90024 =42.041%
; validated in 0.426s
