SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, r9
adox rax, rbp
adox r11, r10
adcx rdi, rax
adcx r13, r11
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, [ rsi + 0x18 ]
adox r10, rcx
mov rdx, 0x0 
mov rcx, rdx
adcx rcx, r10
adox r9, rdx
mov rbp, -0x3 
inc rbp
adox r8, r8
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, rdx
adox rbx, rbx
mov rdx, 0x0 
mov r10, rdx
adcx r10, r9
setc r9b
clc
adcx r11, r8
adcx r14, rbx
adox rdi, rdi
adox r13, r13
adcx r15, rdi
adox rcx, rcx
adcx r12, r13
adcx rcx, [ rsp - 0x48 ]
adox r10, r10
movzx r8, r9b
adox r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbx, rdx
adcx rbx, r10
mov rdx, 0x26 
mulx r10, r13, rbx
mulx rbp, rbx, rcx
movzx rcx, r9b
lea rcx, [ rcx + r8 ]
adcx rcx, rdi
mulx r8, r9, rcx
xor rdi, rdi
adox rbx, r11
adox r13, r14
adox r9, r15
adox r8, rdi
mulx r14, r11, r12
adcx r11, rax
adcx r14, rbx
adcx rbp, r13
adcx r10, r9
adc r8, 0x0
mulx r15, rax, r8
add rax, r11
mov r15, rdi
adcx r15, r14
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r15
mov rcx, rdi
adcx rcx, rbp
mov rbx, rdi
adcx rbx, r10
mov r13, rdi
cmovc r13, rdx
mov r9, -0x3 
inc r9
adox rax, r13
mov [ r12 + 0x0 ], rax
mov [ r12 + 0x10 ], rcx
mov [ r12 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4341
; seed 3405985126075593 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2450 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=442, initial num_batches=31): 365 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1489795918367347
; number reverted permutation / tried permutation: 387 / 491 =78.819%
; number reverted decision / tried decision: 317 / 508 =62.402%
; validated in 0.263s
