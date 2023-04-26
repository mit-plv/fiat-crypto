SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
lea rcx, [rdx + 8 * rdx]
lea r8, [rdx + 2 * rcx]
imul rdx, [ rax + 0x18 ], 0x13
imul rcx, [ rax + 0x8 ], 0x13
mov r9, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
lea rbx, [r9 + 8 * r9]
lea rbp, [r9 + 2 * rbx]
xchg rdx, rcx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rbp
mov rdx, r8
mov [ rsp - 0x60 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
xor r15, r15
adox r9, r8
adox r14, rbx
mulx r8, rbx, [ rsi + 0x20 ]
mov rdx, rbp
mulx r15, rbp, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rax + 0x10 ]
mov rdx, rcx
mov [ rsp - 0x38 ], r12
mulx r12, rcx, [ rsi + 0x10 ]
adcx r9, rcx
adcx r12, r14
add r9, rbp
adcx r15, r12
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r13
mulx r13, r12, r14
xor rdx, rdx
adox r9, rbp
adox rcx, r15
mov r15, r9
shrd r15, rcx, 51
test al, al
adox rbx, r12
adox r13, r8
mov rdx, [ rsi + 0x10 ]
mulx rbp, r8, rdi
adcx rbx, r8
adcx rbp, r13
mov rdx, rdi
mulx r12, rdi, [ rsi + 0x18 ]
xor rdx, rdx
adox rbx, r10
adox r11, rbp
mov rdx, r14
mulx r10, r14, [ rsi + 0x20 ]
adcx r14, rdi
adcx r12, r10
mov rdx, [ rax + 0x8 ]
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx rbp, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, r8
adox rbp, r12
adcx r14, rcx
adcx r13, rbp
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x8 ]
add rbx, rdi
adcx r10, r11
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
add rbx, r15
adc r10, 0x0
mov rdx, rcx
xor r15, r15
adox rdx, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
mov rbp, 0x33 
bzhi rdi, rbx, rbp
shrd rbx, r10, 51
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r10, [ rax + 0x8 ]
xor rdx, rdx
adox r14, r11
adox r12, r13
adcx r14, rbx
adc r12, 0x0
mov r13, r14
shrd r13, r12, 51
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, [ rax + 0x18 ]
xor rdx, rdx
adox rcx, r10
adox r15, r8
mov rdx, [ rax + 0x10 ]
mulx r10, r8, [ rsi + 0x8 ]
adcx rcx, r8
adcx r10, r15
xor rdx, rdx
adox rcx, r11
adox rbx, r10
mov rdx, [ rax + 0x8 ]
mulx r11, r12, [ rsi + 0x18 ]
bzhi rdx, r14, rbp
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mulx r8, r15, [ rsi + 0x20 ]
adox rcx, r13
mov rdx, 0x0 
adox rbx, rdx
mov r13, rcx
shrd r13, rbx, 51
mov rdx, [ rax + 0x20 ]
mulx rbx, r10, [ rsi + 0x0 ]
test al, al
adox r15, r12
adox r11, r8
adcx r15, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rax + 0x18 ]
xor rdx, rdx
adox r15, r12
adox r8, r11
adcx r15, r10
adcx rbx, r8
xor r10, r10
adox r15, r13
adox rbx, r10
bzhi rdx, r15, rbp
shrd r15, rbx, 51
imul r13, r15, 0x13
bzhi r11, r9, rbp
lea r11, [ r11 + r13 ]
mov r9, r11
shr r9, 51
lea r9, [ r9 + rdi ]
mov rdi, r9
shr rdi, 51
bzhi r12, r11, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x0 ], r12
bzhi rbx, r9, rbp
mov [ r8 + 0x8 ], rbx
lea rdi, [ rdi + r14 ]
mov [ r8 + 0x10 ], rdi
mov [ r8 + 0x20 ], rdx
bzhi r14, rcx, rbp
mov [ r8 + 0x18 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2105
; seed 4385946232673071 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1227280 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 84437 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06880011081415814
; number reverted permutation / tried permutation: 70396 / 89845 =78.353%
; number reverted decision / tried decision: 56609 / 90154 =62.791%
; validated in 0.509s
