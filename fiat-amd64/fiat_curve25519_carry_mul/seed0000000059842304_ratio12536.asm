SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x10 ], 0x13
mov r10, rdx
mov rdx, [ rdx + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ r10 + 0x0 ]
imul rdx, [ r10 + 0x20 ], 0x13
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
imul r12, [ r10 + 0x8 ], 0x13
test al, al
adox rbx, r8
adox r9, rbp
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, r12
mov rdx, r8
mulx r12, r8, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rcx
mulx rcx, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r11
mov [ rsp - 0x38 ], rcx
mulx rcx, r11, rax
adcx rbp, r11
adcx rcx, r13
mov rdx, [ r10 + 0x18 ]
lea r13, [rdx + 8 * rdx]
lea r11, [rdx + 2 * r13]
mov rdx, r11
mulx r13, r11, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rdi
mov rdi, rdx
mov rdx, [ r10 + 0x8 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r8
mulx r8, r12, [ rsi + 0x10 ]
add rbx, r12
adcx r8, r9
mov rdx, rax
mulx r9, rax, [ rsi + 0x20 ]
mov rdx, rdi
mulx r12, rdi, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r8
xor r8, r8
adox rbp, r11
adox r13, rcx
adcx rbp, r14
adcx r15, r13
mov r14, rdx
mov rdx, [ r10 + 0x0 ]
mulx r11, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, r14
xor rdx, rdx
adox rax, r13
adox r8, r9
adcx rbp, rcx
adcx r11, r15
mov r14, rbp
shrd r14, r11, 51
xor r9, r9
adox rax, [ rsp - 0x20 ]
adox r8, [ rsp - 0x28 ]
mov rdx, [ r10 + 0x8 ]
mulx rcx, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r11, r13, [ r10 + 0x0 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x10 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
adcx rax, r13
adcx r11, r8
xor rdx, rdx
adox rax, r15
adox rcx, r11
adcx rax, r14
adc rcx, 0x0
xor r14, r14
adox rdi, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r8, [ r10 + 0x8 ]
mov rdx, rax
shrd rdx, rcx, 51
xor r13, r13
adox rdi, r9
adox rbx, r12
adcx rdi, r8
adcx r15, rbx
add rdi, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
xor r14, r14
adox rdi, rdx
adox r15, r14
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, [ r10 + 0x18 ]
mov rdx, 0x33 
bzhi r11, rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, [ r10 + 0x8 ]
mov rdx, [ r10 + 0x10 ]
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], r11
mulx r11, r14, [ r10 + 0x10 ]
shrd rdi, r15, 51
mov rdx, r8
xor r15, r15
adox rdx, [ rsp - 0x10 ]
adox rbx, [ rsp - 0x18 ]
adcx rdx, r13
adcx r9, rbx
add rdx, rdi
adc r9, 0x0
mov r13, 0x33 
bzhi r8, rdx, r13
shrd rdx, r9, 51
mov rdi, rdx
mov rdx, [ r10 + 0x0 ]
mulx r9, rbx, [ rsi + 0x20 ]
test al, al
adox rbx, rcx
adox r12, r9
adcx rbx, r14
adcx r11, r12
mov rdx, [ rsi + 0x8 ]
mulx r14, rcx, [ r10 + 0x18 ]
mov rdx, [ r10 + 0x20 ]
mulx r12, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, rcx
adox r14, r11
bzhi r15, rbp, r13
adox rbx, r9
adox r12, r14
add rbx, rdi
adc r12, 0x0
mov rbp, rbx
shrd rbp, r12, 51
imul rdi, rbp, 0x13
bzhi r11, rbx, r13
lea r15, [ r15 + rdi ]
bzhi rcx, r15, r13
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x20 ], r11
bzhi r14, rax, r13
shr r15, 51
lea r15, [ r15 + r14 ]
mov rax, r15
shr rax, 51
add rax, [ rsp - 0x8 ]
bzhi rbx, r15, r13
mov [ r9 + 0x10 ], rax
mov [ r9 + 0x0 ], rcx
mov [ r9 + 0x8 ], rbx
mov [ r9 + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2536
; seed 3727770216855665 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1649526 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=329, initial num_batches=31): 149384 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09056177350341856
; number reverted permutation / tried permutation: 72759 / 90810 =80.122%
; number reverted decision / tried decision: 57432 / 89189 =64.394%
; validated in 0.702s
