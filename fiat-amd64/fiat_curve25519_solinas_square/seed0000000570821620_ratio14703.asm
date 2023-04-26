SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
add r11, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
adcx r10, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rcx, [ rsi + 0x8 ]
adcx rcx, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
adcx rbx, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rax, rax
mov [ rsp - 0x60 ], r14
mov r14, 0x0 
adcx r12, r14
clc
adcx rbp, r10
adcx r13, rcx
mov r10, r14
adcx r10, rbx
mov rcx, r14
adcx rcx, r12
adox r11, r11
adox rbp, rbp
adox r13, r13
adox r10, r10
adox rcx, rcx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, rdx
setc dl
clc
adcx r9, rax
adcx rbx, r11
adcx r12, rbp
movzx rax, dl
adox rax, r14
movzx r11, dl
lea r11, [ r11 + rax ]
mov rdx, [ rsi + 0x10 ]
mulx rax, rbp, rdx
adcx rbp, r13
adcx rax, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, r13, rdx
adcx r13, rcx
mov rdx, 0x26 
mulx r14, rcx, r13
adcx r11, r10
mulx r13, r10, r11
mov [ rsp - 0x58 ], r15
mulx r15, r11, rbp
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, rax
xor rax, rax
adox r11, r8
adcx rbp, r9
adcx rcx, rbx
adcx r10, r12
adcx r13, rax
adox r15, rbp
adox rdi, rcx
adox r14, r10
adox r13, rax
mulx r9, r8, r13
xor r9, r9
adox r8, r11
mov rax, r9
adox rax, r15
mov rbx, r9
adox rbx, rdi
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rax
mov [ r12 + 0x10 ], rbx
mov r11, r9
adox r11, r14
mov rbp, r9
cmovo rbp, rdx
adcx r8, rbp
mov [ r12 + 0x0 ], r8
mov [ r12 + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4703
; seed 1304004513126332 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 433233 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=453, initial num_batches=31): 65607 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1514358324504366
; number reverted permutation / tried permutation: 75617 / 90135 =83.893%
; number reverted decision / tried decision: 54196 / 89864 =60.309%
; validated in 0.258s
