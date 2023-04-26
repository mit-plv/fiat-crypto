SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r15
mov [ rsp - 0x40 ], r10
mulx r10, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], rcx
mulx rcx, r10, [ rax + 0x10 ]
add r9, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r10
mulx r10, r12, [ rsi + 0x8 ]
adcx rcx, r11
adc r10, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r12
mulx r12, r11, [ rax + 0x8 ]
add r11, r9
adcx rbx, rcx
mov rdx, [ rax + 0x0 ]
mulx rcx, r9, [ rsi + 0x0 ]
mov rdx, -0x2 
inc rdx
adox rbp, rcx
mov rcx, 0x0 
mov rdx, rcx
adcx rdx, r10
seto r10b
mov [ rsp - 0x8 ], r9
mov r9, -0x3 
inc r9
adox r13, r8
adcx rdi, rcx
mov r8, rdx
mov rdx, [ rax + 0x8 ]
mulx r9, rcx, [ rsi + 0x8 ]
clc
adcx rcx, r13
adox r14, r11
adcx r15, r14
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rax + 0x10 ]
adox r11, rbx
adcx r12, r11
mov rdx, [ rax + 0x10 ]
mulx r14, rbx, [ rsi + 0x18 ]
adox rbx, r8
adcx rbx, [ rsp - 0x18 ]
mov rdx, 0x0 
mov r8, rdx
adox r8, rdi
mov rdx, [ rax + 0x18 ]
mulx r11, rdi, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r11, rdx
dec rdx
movzx r10, r10b
adox r10, rdx
adox rcx, [ rsp - 0x20 ]
adox r9, r15
adox r12, [ rsp - 0x10 ]
mov r10, 0x0 
mov r15, r10
adcx r15, r8
adcx r11, r10
clc
adcx rbp, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x28 ]
adcx r9, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x38 ]
mov r8, 0x26 
mov rdx, r12
mulx r10, r12, r8
adox rbx, [ rsp - 0x48 ]
adox rdi, r15
adcx r13, rbx
adcx r14, rdi
mov rdx, r8
mulx r15, r8, r13
mov rbx, 0x0 
adox r11, rbx
adcx r11, rbx
test al, al
adox r12, [ rsp - 0x8 ]
mulx r13, rdi, r11
adcx r8, rbp
adox r10, r8
mulx r11, rbp, r14
adcx rbp, rcx
adox r15, rbp
adcx rdi, r9
adox r11, rdi
adcx r13, rbx
adox r13, rbx
mulx r9, rcx, r13
test al, al
adox rcx, r12
mov r9, rbx
adox r9, r10
mov r14, rbx
adox r14, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], r14
mov r8, rbx
adox r8, r11
mov [ r12 + 0x18 ], r8
mov r10, rbx
cmovo r10, rdx
adcx rcx, r10
mov [ r12 + 0x8 ], r9
mov [ r12 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3742
; seed 0395137969134797 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5486 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=192, initial num_batches=31): 460 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08384979948960991
; number reverted permutation / tried permutation: 327 / 496 =65.927%
; number reverted decision / tried decision: 301 / 503 =59.841%
; validated in 0.546s
