SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
xor rdx, rdx
adox r13, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
adox r9, rbp
mov rdx, 0x0 
adox rcx, rdx
adcx r12, r8
mov r8, -0x3 
inc r8
adox r10, r13
adcx r15, r10
adox r14, r9
mov rdx, [ rsi + 0x10 ]
mulx rbp, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r9, [ rsi + 0x10 ]
adcx r13, r14
mov rdx, 0x0 
mov r14, rdx
adox r14, rcx
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x18 ]
adcx rcx, r14
mov rdx, 0x0 
adox r10, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r8
mulx r8, r14, [ rsi + 0x8 ]
mov rdx, 0x0 
mov [ rsp - 0x28 ], rbp
mov rbp, rdx
adcx rbp, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r9
mulx r9, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], rbp
mulx rbp, r10, [ rax + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r14, r9
setc r9b
clc
adcx r10, r12
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r14
mulx r14, r12, [ rax + 0x10 ]
adcx r12, r15
adcx r11, r13
adcx rbx, rcx
adox r8, r10
adox rbp, r12
mov rdx, [ rax + 0x18 ]
mulx r13, r15, [ rsi + 0x18 ]
adox rdi, r11
mov rdx, 0x0 
mov rcx, rdx
adcx rcx, [ rsp - 0x10 ]
movzx r10, r9b
lea r10, [ r10 + r13 ]
adcx r10, rdx
mov r9, [ rsp - 0x8 ]
clc
adcx r9, [ rsp - 0x38 ]
adcx r8, [ rsp - 0x48 ]
adcx rbp, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x20 ]
adcx r14, rdi
mov r12, 0x26 
mov rdx, r14
mulx r11, r14, r12
adox r15, rcx
adcx rbx, [ rsp - 0x28 ]
mov rdx, r12
mulx r13, r12, rbx
adcx r15, [ rsp - 0x30 ]
mov rdi, 0x0 
adox r10, rdi
mulx rbx, rcx, r15
adcx r10, rdi
mulx rdi, r15, r10
xor r10, r10
adox r12, r9
adox rcx, r8
adox r15, rbp
adcx r14, [ rsp - 0x18 ]
adcx r11, r12
adox rdi, r10
adcx r13, rcx
adcx rbx, r15
adc rdi, 0x0
mulx r8, r9, rdi
xor r8, r8
adox r9, r14
mov r10, r8
adox r10, r11
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r10
mov r12, r8
adox r12, r13
mov [ rbp + 0x10 ], r12
mov rcx, r8
adox rcx, rbx
mov r15, r8
cmovo r15, rdx
mov [ rbp + 0x18 ], rcx
adcx r9, r15
mov [ rbp + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6614
; seed 1218689670726071 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 752413 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=219, initial num_batches=31): 65205 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08666118209015528
; number reverted permutation / tried permutation: 66712 / 90154 =73.998%
; number reverted decision / tried decision: 51937 / 89845 =57.807%
; validated in 0.476s
