SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
add rax, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rsi + 0x18 ]
adcx r8, r10
adcx rcx, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, r10, [ rsi + 0x10 ]
adcx r10, r14
adc r9, 0x0
add r12, r8
adcx r13, rcx
mov rdx, -0x2 
inc rdx
adox r11, r11
adox rax, rax
adox r12, r12
adox r13, r13
mov rdx, [ rsi + 0x0 ]
mulx r8, r14, rdx
mov rdx, 0x0 
mov rcx, rdx
adcx rcx, r10
mov r10, rdx
adcx r10, r9
adox rcx, rcx
setc r9b
clc
adcx r8, r11
adcx rbx, rax
adox r10, r10
adcx rbp, r12
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, rdx
adcx r11, r13
adcx rax, rcx
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, rdx
adcx r12, r10
mov rdx, 0x26 
mulx r10, rcx, r11
movzx r11, r9b
mov [ rsp - 0x58 ], r15
mov r15, 0x0 
adox r11, r15
movzx r15, r9b
lea r15, [ r15 + r11 ]
adcx r15, r13
mulx r13, r9, r12
mulx r11, r12, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rax
xor rax, rax
adox r15, r8
adox r9, rbx
adox r12, rbp
adox r11, rax
adcx rcx, r14
adcx r10, r15
adcx rdi, r9
adcx r13, r12
adc r11, 0x0
mulx r8, r14, r11
test al, al
adox r14, rcx
mov r8, rax
adox r8, r10
mov rbx, rax
adox rbx, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], rbx
mov [ rbp + 0x8 ], r8
mov r15, rax
adox r15, r13
mov r9, rax
cmovo r9, rdx
adcx r14, r9
mov [ rbp + 0x18 ], r15
mov [ rbp + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4700
; seed 4288661244848131 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 429185 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=453, initial num_batches=31): 65035 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.15153139089203957
; number reverted permutation / tried permutation: 77850 / 90220 =86.289%
; number reverted decision / tried decision: 54779 / 89779 =61.015%
; validated in 0.26s
