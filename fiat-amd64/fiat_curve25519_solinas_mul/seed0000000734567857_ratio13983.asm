SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], r8
mulx r8, r12, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r12
mulx r12, r15, [ rsi + 0x10 ]
test al, al
adox r15, r8
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], r9
mulx r9, r8, [ rsi + 0x0 ]
adcx r10, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r8
mulx r8, r9, [ rax + 0x18 ]
adcx r13, r8
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r9
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r8, r10
adox r12, r8
adcx r11, r13
mov r10, rdx
adcx r10, rbx
adcx rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, [ rax + 0x8 ]
clc
adcx r13, r15
adox rbp, r11
mov rdx, [ rax + 0x10 ]
mulx r8, r15, [ rsi + 0x18 ]
adox r15, r10
adcx rcx, r12
adcx r9, rbp
mov rdx, [ rax + 0x0 ]
mulx r11, r12, [ rsi + 0x0 ]
adcx r14, r15
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rax + 0x18 ]
mov rdx, 0x0 
mov r15, rdx
adox r15, rdi
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], r12
mulx r12, rdi, [ rsi + 0x8 ]
mov rdx, 0x0 
adox rbp, rdx
mov [ rsp - 0x8 ], r8
mov r8, -0x3 
inc r8
adox rdi, r11
adox r12, r13
adox rbx, rcx
mov r13, rdx
adcx r13, r15
adox r9, [ rsp - 0x28 ]
adcx rbp, rdx
clc
adcx rdi, [ rsp - 0x30 ]
adox r14, [ rsp - 0x38 ]
adox r10, r13
adcx r12, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x18 ]
adcx r9, [ rsp - 0x40 ]
mov rcx, 0x26 
mov rdx, rcx
mulx r11, rcx, r9
mov r15, 0x0 
adox rbp, r15
adcx r14, [ rsp - 0x48 ]
adcx r10, [ rsp - 0x8 ]
mulx r9, r13, r14
mov r14, -0x3 
inc r14
adox rcx, [ rsp - 0x10 ]
adcx rbp, r15
mulx r15, r14, rbp
mulx r8, rbp, r10
clc
adcx r13, rdi
adcx rbp, r12
adox r11, r13
adcx r14, rbx
adox r9, rbp
adox r8, r14
mov rdi, 0x0 
adcx r15, rdi
adox r15, rdi
mulx rbx, r12, r15
xor rbx, rbx
adox r12, rcx
mov rdi, rbx
adox rdi, r11
mov r10, rbx
adox r10, r9
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r10
mov r13, rbx
adox r13, r8
mov rbp, rbx
cmovo rbp, rdx
mov [ rcx + 0x18 ], r13
mov [ rcx + 0x8 ], rdi
adcx r12, rbp
mov [ rcx + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3983
; seed 1884484556613610 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 867291 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=192, initial num_batches=31): 73702 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08497955126941245
; number reverted permutation / tried permutation: 57227 / 89925 =63.639%
; number reverted decision / tried decision: 46973 / 90074 =52.149%
; validated in 0.546s
