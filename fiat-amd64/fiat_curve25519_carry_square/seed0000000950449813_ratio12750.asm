SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, r11
imul rdx, [ rsi + 0x20 ], 0x26
mulx r11, r9, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
xor rdx, rdx
adox rcx, r9
adox r11, r8
imul r8, [ rsi + 0x18 ], 0x13
mov rdx, r8
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r12
xor rdx, rdx
adox r8, r15
adox rdi, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r12, rdx
mov rdx, 0x1 
shlx r15, [ rsi + 0x8 ], rdx
adcx rcx, r12
adcx r9, r11
mov rdx, r15
mulx r11, r15, [ rsi + 0x0 ]
add r8, r15
adcx r11, rdi
imul rdi, [ rsi + 0x10 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx r15, r12, rdi
mov rdx, rcx
shrd rdx, r9, 51
xor r9, r9
adox rbx, r13
adox r14, rbp
adcx rbx, r12
adcx r15, r14
imul rbp, [ rsi + 0x20 ], 0x13
xor r13, r13
adox r8, rdx
adox r11, r13
mov r9, r8
shrd r9, r11, 51
xor r12, r12
adox rbx, r9
adox r15, r12
mov rdx, [ rsi + 0x20 ]
mulx r14, r13, rbp
mov rdx, 0x33 
bzhi rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r11, rdi
adox r13, r11
adox r9, r14
shrd rbx, r15, 51
imul rdx, [ rsi + 0x18 ], 0x2
mulx r15, rdi, [ rsi + 0x8 ]
mulx r11, r14, [ rsi + 0x0 ]
add rax, rdi
adcx r15, r10
mov r10, [ rsi + 0x20 ]
lea rdx, [r10 + r10]
xor r10, r10
adox r13, r14
adox r11, r9
mulx r9, r12, [ rsi + 0x0 ]
adcx r13, rbx
adc r11, 0x0
mov rbx, r13
shrd rbx, r11, 51
mov rdi, 0x7ffffffffffff 
and rcx, rdi
adox rax, r12
adox r9, r15
adcx rax, rbx
adc r9, 0x0
mov r14, rax
shrd r14, r9, 51
imul r15, r14, 0x13
and r8, rdi
lea rcx, [ rcx + r15 ]
and rax, rdi
mov rdx, rcx
shr rdx, 51
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x20 ], rax
lea rdx, [ rdx + r8 ]
mov r11, rdx
and r11, rdi
shr rdx, 51
lea rdx, [ rdx + rbp ]
and rcx, rdi
mov [ r12 + 0x0 ], rcx
and r13, rdi
mov [ r12 + 0x18 ], r13
mov [ r12 + 0x8 ], r11
mov [ r12 + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2750
; seed 0054780562425985 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1097554 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=460, initial num_batches=31): 138805 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1264675815495183
; number reverted permutation / tried permutation: 75070 / 89851 =83.549%
; number reverted decision / tried decision: 67422 / 90148 =74.790%
; validated in 0.43s
