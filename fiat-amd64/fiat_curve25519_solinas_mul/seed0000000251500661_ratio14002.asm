SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
test al, al
adox r9, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rbp
mulx rbp, r13, [ rsi + 0x0 ]
adcx r12, r9
adox rdi, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rax + 0x8 ]
adcx rbx, rdi
mov rdx, 0x0 
adox r14, rdx
mov rdi, -0x3 
inc rdi
adox rcx, rbp
mov rbp, rdx
adcx rbp, r14
mov rdx, [ rax + 0x10 ]
mulx rdi, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r13
mulx r13, rdi, [ rax + 0x10 ]
adox r8, r12
adox r14, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r12, [ rsi + 0x10 ]
mov rdx, 0x0 
adcx rbx, rdx
adox rdi, rbp
mov rbp, rdx
adox rbp, rbx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], r13
mulx r13, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], rbx
mov [ rsp - 0x10 ], r9
mulx r9, rbx, [ rsi + 0x8 ]
clc
adcx r10, r13
seto dl
mov r13, -0x2 
inc r13
adox rbx, rcx
adcx r11, rbx
mov cl, dl
mov rdx, [ rsi + 0x8 ]
mulx r13, rbx, [ rax + 0x10 ]
adox rbx, r8
adcx r9, rbx
adox r15, r14
adox rdi, [ rsp - 0x38 ]
adcx r15, [ rsp - 0x40 ]
adcx r12, rdi
mov rdx, [ rsi + 0x18 ]
mulx r14, r8, [ rax + 0x18 ]
movzx rdx, cl
lea rdx, [ rdx + r14 ]
mov rcx, 0x0 
mov rbx, rcx
adox rbx, rbp
adox rdx, rcx
adcx r8, rbx
adcx rdx, rcx
add r10, [ rsp - 0x10 ]
adcx r11, [ rsp - 0x48 ]
adcx r9, [ rsp - 0x28 ]
adcx r13, r15
adcx r12, [ rsp - 0x30 ]
mov rbp, 0x26 
xchg rdx, rbp
mulx r15, rdi, r12
adcx r8, [ rsp - 0x20 ]
adcx rbp, rcx
test al, al
adox rdi, r10
mulx rbx, r14, r8
mulx r12, r10, r13
adox r14, r11
adcx r10, [ rsp - 0x18 ]
mulx r13, r11, rbp
adcx r12, rdi
adcx r15, r14
adox r11, r9
adox r13, rcx
adcx rbx, r11
adc r13, 0x0
mulx r8, r9, r13
test al, al
adox r9, r10
mov r8, rcx
adox r8, r12
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r8
mov rdi, rcx
adox rdi, r15
mov [ rbp + 0x10 ], rdi
mov r14, rcx
adox r14, rbx
mov r10, rcx
cmovo r10, rdx
mov [ rbp + 0x18 ], r14
adcx r9, r10
mov [ rbp + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4002
; seed 0785429675065311 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1191456 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=355, initial num_batches=31): 130993 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10994363199312437
; number reverted permutation / tried permutation: 57016 / 89659 =63.592%
; number reverted decision / tried decision: 46009 / 90340 =50.929%
; validated in 0.713s
