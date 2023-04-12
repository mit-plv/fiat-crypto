SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, rbx
adcx r12, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbp, [ rsi + 0x0 ]
adcx rbp, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rsi + 0x8 ]
adcx r13, r14
adcx r11, r15
mov rdx, 0x0 
adcx rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r14, [ rsi + 0x8 ]
clc
adcx r14, rbp
adcx r15, r13
mov rdx, 0x0 
mov rbp, rdx
adcx rbp, r11
mov r13, rdx
adcx r13, rcx
adox r12, r12
adox r14, r14
setc r11b
clc
adcx r10, rbx
adox r15, r15
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbx, rdx
adcx r8, r12
adcx r9, r14
adox rbp, rbp
adcx rbx, r15
adox r13, r13
mov rdx, 0x26 
mulx r14, r12, rbx
adcx rcx, rbp
movzx r15, r11b
mov rbp, 0x0 
adox r15, rbp
movzx rbx, r11b
lea rbx, [ rbx + r15 ]
mulx r15, r11, rcx
mov rdx, [ rsi + 0x18 ]
mulx rbp, rcx, rdx
adcx rcx, r13
adcx rbx, rbp
test al, al
adox r11, r10
mov rdx, 0x26 
mulx r13, r10, rcx
adox r10, r8
adcx r12, rax
adcx r14, r11
mulx r8, rax, rbx
adox rax, r9
adcx r15, r10
adcx r13, rax
mov r9, 0x0 
adox r8, r9
adc r8, 0x0
mulx rcx, rbp, r8
xor rcx, rcx
adox rbp, r12
mov r9, rcx
adox r9, r14
mov rbx, rcx
adox rbx, r15
mov [ rdi + 0x10 ], rbx
mov r11, rcx
adox r11, r13
mov [ rdi + 0x8 ], r9
mov r10, rcx
cmovo r10, rdx
adcx rbp, r10
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x18 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3346
; seed 3229881202654323 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 602600 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=272, initial num_batches=31): 68986 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1144805841354132
; number reverted permutation / tried permutation: 64685 / 90445 =71.519%
; number reverted decision / tried decision: 48141 / 89554 =53.756%
; validated in 0.416s
