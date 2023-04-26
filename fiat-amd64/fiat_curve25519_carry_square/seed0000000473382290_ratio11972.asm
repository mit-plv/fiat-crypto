SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rdx, r11
mulx r10, rax, [ rsi + 0x18 ]
mov r11, [ rsi + 0x10 ]
lea rcx, [r11 + r11]
imul r11, [ rsi + 0x18 ], 0x26
mov rdx, r11
mulx r8, r11, [ rsi + 0x10 ]
mov r9, [ rsi + 0x20 ]
lea rdx, [r9 + r9]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
test al, al
adox r11, r14
adox r15, r8
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, rdx
adcx r11, rdi
adcx r14, r15
xor rdx, rdx
adox rax, r12
adox r13, r10
mov r10, [ rsi + 0x8 ]
lea r12, [r10 + r10]
mov r10, 0x7ffffffffffff 
mov r15, r11
and r15, r10
mov rdx, r12
mulx rdi, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
lea r10, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], r8
mulx r8, r15, rdx
shrd r11, r14, 51
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbp
mulx rbp, r14, r10
xor rdx, rdx
adox rax, r12
adox rdi, r13
adcx rax, r11
adc rdi, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r12, r13, rcx
add r15, r14
adcx rbp, r8
mov rdx, r9
mulx r8, r9, [ rsi + 0x0 ]
test al, al
adox r15, r9
adox r8, rbp
mov rdx, rbx
adcx rdx, [ rsp - 0x38 ]
mov r11, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x48 ]
mov rbx, rax
shrd rbx, rdi, 51
xor r14, r14
adox rdx, r13
adox r12, r11
adcx rdx, rbx
adc r12, 0x0
mov rdi, [ rsi + 0x20 ]
lea r13, [rdi + 8 * rdi]
lea rbp, [rdi + 2 * r13]
xchg rdx, rbp
mulx r13, rdi, [ rsi + 0x20 ]
mov r9, rbp
shrd r9, r12, 51
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, rcx
test al, al
adox rdi, rbx
adox r12, r13
adcx rdi, r10
adcx r11, r12
xor rdx, rdx
adox rdi, r9
adox r11, rdx
mov r14, rdi
shrd r14, r11, 51
xor rcx, rcx
adox r15, r14
adox r8, rcx
mov rdx, r15
shrd rdx, r8, 51
imul r13, rdx, 0x13
add r13, [ rsp - 0x40 ]
mov r9, r13
shr r9, 51
mov r10, 0x7ffffffffffff 
and r13, r10
and rax, r10
lea r9, [ r9 + rax ]
mov rbx, r9
shr rbx, 51
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], r13
and r9, r10
mov [ r12 + 0x8 ], r9
and rbp, r10
lea rbx, [ rbx + rbp ]
mov [ r12 + 0x10 ], rbx
and rdi, r10
and r15, r10
mov [ r12 + 0x18 ], rdi
mov [ r12 + 0x20 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1972
; seed 3749941024214649 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 682056 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=283, initial num_batches=31): 71654 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1050558898389575
; number reverted permutation / tried permutation: 73349 / 89895 =81.594%
; number reverted decision / tried decision: 58515 / 90104 =64.942%
; validated in 0.254s
