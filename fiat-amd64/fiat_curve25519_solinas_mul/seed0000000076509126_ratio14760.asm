SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r14
mulx r14, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r9
mulx r9, r14, [ rax + 0x8 ]
test al, al
adox r10, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r9
mulx r9, r12, [ rax + 0x8 ]
adcx r12, r10
adox r15, r8
mov rdx, [ rax + 0x18 ]
mulx r10, r8, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r10, rdx
adcx r11, r15
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r8
mulx r8, r15, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r15, rbx
adox r8, r12
mov rbx, 0x0 
mov r12, rbx
adcx r12, r10
mov rdx, [ rax + 0x10 ]
mulx rbx, r10, [ rsi + 0x10 ]
adox r10, r11
adox r13, r12
mov rdx, 0x0 
adcx rcx, rdx
mov r11, rdx
adox r11, rcx
clc
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mulx r12, r15, [ rax + 0x10 ]
adcx r15, r8
adcx r9, r10
adcx rdi, r13
mov rdx, [ rax + 0x18 ]
mulx r10, r8, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r10, rdx
mov r13, rdx
adcx r13, r11
mov rdx, [ rax + 0x0 ]
mulx r11, rcx, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r10, rdx
mov [ rsp - 0x8 ], rcx
xor rcx, rcx
adox rbp, r11
adcx rbp, [ rsp - 0x20 ]
adox r14, [ rsp - 0x28 ]
adox r15, [ rsp - 0x18 ]
adox r9, [ rsp - 0x10 ]
adox rdi, [ rsp - 0x30 ]
adox r8, r13
adcx r14, [ rsp - 0x38 ]
adcx r15, [ rsp - 0x40 ]
adox r10, rcx
adcx r12, r9
adcx rbx, rdi
adcx r8, [ rsp - 0x48 ]
adcx r10, rcx
mov rdx, 0x26 
mulx r11, r13, rbx
xor r9, r9
adox r13, rbp
mulx rbp, rcx, r8
mulx rbx, rdi, r12
adox rcx, r14
adcx rdi, [ rsp - 0x8 ]
adcx rbx, r13
mulx r12, r14, r10
adox r14, r15
adcx r11, rcx
adox r12, r9
adcx rbp, r14
adc r12, 0x0
mulx r8, r15, r12
xor r8, r8
adox r15, rdi
mov r9, r8
adox r9, rbx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], r9
mov r13, r8
adox r13, r11
mov rcx, r8
adox rcx, rbp
mov rdi, r8
cmovo rdi, rdx
mov [ r10 + 0x10 ], r13
adcx r15, rdi
mov [ r10 + 0x0 ], r15
mov [ r10 + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.4760
; seed 1703259393460510 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1334419 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=176, initial num_batches=31): 112066 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08398111837436367
; number reverted permutation / tried permutation: 57569 / 90215 =63.813%
; number reverted decision / tried decision: 46663 / 89784 =51.973%
; validated in 0.585s
