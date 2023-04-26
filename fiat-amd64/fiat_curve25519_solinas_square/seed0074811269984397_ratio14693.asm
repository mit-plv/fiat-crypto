SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
adcx r11, r10
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rsi + 0x8 ]
adcx r10, r9
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r9, rdx
adcx r12, rcx
mov rdx, 0x0 
adcx r13, rdx
clc
adcx rbx, r8
adcx rbp, r10
adox r11, r11
adox rbx, rbx
mov r8, rdx
adcx r8, r12
adox rbp, rbp
adox r8, r8
mov rcx, rdx
adcx rcx, r13
adox rcx, rcx
setc r10b
clc
adcx r14, rax
movzx rax, r10b
adox rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r12, rdx
adcx r12, r11
adcx r13, rbx
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
adcx r15, rbp
mov rdx, 0x26 
mov [ rsp - 0x48 ], r13
mulx r13, rbp, r15
movzx r15, r10b
lea r15, [ r15 + rax ]
adcx rdi, r8
adcx r11, rcx
mov r8, -0x2 
inc r8
adox rbp, r9
mulx r10, r9, rdi
adcx r15, rbx
clc
adcx r9, r14
mulx r14, rcx, r11
adox r13, r9
adcx rcx, r12
adox r10, rcx
mulx r12, rax, r15
adcx rax, [ rsp - 0x48 ]
adox r14, rax
mov rbx, 0x0 
adcx r12, rbx
adox r12, rbx
mulx r11, rdi, r12
xor r11, r11
adox rdi, rbp
mov rbx, r11
adox rbx, r13
mov rbp, r11
adox rbp, r10
mov r15, r11
adox r15, r14
mov r9, r11
cmovo r9, rdx
adcx rdi, r9
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rdi
mov [ r13 + 0x8 ], rbx
mov [ r13 + 0x18 ], r15
mov [ r13 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4693
; seed 0074811269984397 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3116 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=298, initial num_batches=31): 408 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.13093709884467267
; number reverted permutation / tried permutation: 377 / 494 =76.316%
; number reverted decision / tried decision: 247 / 505 =48.911%
; validated in 0.331s
