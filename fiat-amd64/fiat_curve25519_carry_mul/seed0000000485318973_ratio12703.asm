SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x18 ], 0x13
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, rax
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rax
imul rdx, [ r10 + 0x10 ], 0x13
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
imul rdx, [ r10 + 0x8 ], 0x13
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
test al, al
adox r14, rbx
adox rbp, r15
adcx r14, r8
adcx r9, rbp
mov r8, [ r10 + 0x20 ]
lea rbx, [r8 + 8 * r8]
lea rdx, [r8 + 2 * rbx]
test al, al
adox r12, r11
adox rcx, r13
mulx rbx, r8, [ rsi + 0x10 ]
mulx r13, r11, [ rsi + 0x18 ]
mulx rbp, r15, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r13
mulx r13, r15, [ rsi + 0x8 ]
adcx r14, rdi
adcx rbp, r9
mov rdx, [ r10 + 0x0 ]
mulx rdi, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, r9
adox rdi, rbp
mov rbp, r14
shrd rbp, rdi, 51
mov rdx, [ r10 + 0x8 ]
mulx rdi, r9, [ rsi + 0x0 ]
add r12, r8
adcx rbx, rcx
test al, al
adox r12, r15
adox r13, rbx
adcx r12, r9
adcx rdi, r13
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rax
xor rdx, rdx
adox r12, rbp
adox rdi, rdx
mov rdx, [ r10 + 0x0 ]
mulx r15, rax, [ rsi + 0x18 ]
mov rdx, 0x7ffffffffffff 
mov rbp, r12
and rbp, rdx
shrd r12, rdi, 51
mov rdx, [ r10 + 0x8 ]
mulx rbx, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r11
adox r8, [ rsp - 0x38 ]
mov rdx, [ r10 + 0x0 ]
mulx r13, r11, [ rsi + 0x10 ]
adcx rcx, r11
adcx r13, r8
mov rdx, [ r10 + 0x8 ]
mulx r8, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, r9
adox rbx, r13
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ r10 + 0x10 ]
adcx rcx, r9
adcx r11, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, [ r10 + 0x10 ]
mov rdx, rax
xor r9, r9
adox rdx, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
adcx rcx, r12
adc r11, 0x0
mov rax, rcx
shrd rax, r11, 51
add rdx, rdi
adcx r8, r15
add rdx, r13
adcx rbx, r8
mov r12, rdx
mov rdx, [ r10 + 0x0 ]
mulx r13, rdi, [ rsi + 0x20 ]
mov rdx, [ r10 + 0x18 ]
mulx r11, r15, [ rsi + 0x0 ]
mov rdx, [ r10 + 0x8 ]
mulx r9, r8, [ rsi + 0x18 ]
xor rdx, rdx
adox rdi, r8
adox r9, r13
adcx r12, r15
adcx r11, rbx
mov rdx, [ rsi + 0x10 ]
mulx r13, rbx, [ r10 + 0x10 ]
add rdi, rbx
adcx r13, r9
add r12, rax
adc r11, 0x0
mov rdx, [ r10 + 0x20 ]
mulx r15, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ r10 + 0x18 ]
mov rdx, 0x7ffffffffffff 
and r14, rdx
adox rdi, r8
adox r9, r13
adcx rdi, rax
adcx r15, r9
mov rbx, r12
shrd rbx, r11, 51
xor r13, r13
adox rdi, rbx
adox r15, r13
mov r11, rdi
shrd r11, r15, 51
imul rax, r11, 0x13
lea r14, [ r14 + rax ]
mov r8, r14
shr r8, 51
and r14, rdx
and rdi, rdx
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x20 ], rdi
lea r8, [ r8 + rbp ]
and rcx, rdx
mov rbp, r8
and rbp, rdx
and r12, rdx
mov [ r9 + 0x8 ], rbp
mov [ r9 + 0x18 ], r12
shr r8, 51
lea r8, [ r8 + rcx ]
mov [ r9 + 0x10 ], r8
mov [ r9 + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2703
; seed 1746328213885180 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 690822 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=404, initial num_batches=31): 77620 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1123588999771287
; number reverted permutation / tried permutation: 72823 / 89628 =81.250%
; number reverted decision / tried decision: 60586 / 90371 =67.041%
; validated in 0.255s
