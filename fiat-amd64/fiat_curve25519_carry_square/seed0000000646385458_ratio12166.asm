SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
imul r10, [ rsi + 0x18 ], 0x26
mov r11, [ rsi + 0x10 ]
lea rdx, [r11 + r11]
xchg rdx, rax
mulx rcx, r11, [ rsi + 0x8 ]
xchg rdx, r10
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x18 ], rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r10
add r8, r11
adcx rcx, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r11, rdx
xor rdx, rdx
adox r8, r11
adox r9, rcx
imul rcx, [ rsi + 0x18 ], 0x13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, rcx
mov rdx, r8
shrd rdx, r9, 51
xchg rdx, r10
mulx rcx, r9, [ rsi + 0x10 ]
mov rdx, r13
mov [ rsp - 0x48 ], r12
mulx r12, r13, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r9
adox rcx, rdi
adcx r11, r13
adcx r12, rcx
mov rdi, [ rsi + 0x20 ]
lea r9, [rdi + 8 * rdi]
lea r13, [rdi + 2 * r9]
mov rdx, [ rsi + 0x8 ]
mulx r9, rdi, rdx
xor rdx, rdx
adox r14, rdi
adox r9, r15
mov rdx, [ rsi + 0x8 ]
mulx rcx, r15, rax
adcx r11, r10
adc r12, 0x0
mov rdx, rax
mulx r10, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, rax
adox r10, r9
mov rdi, 0x33 
bzhi r9, r11, rdi
mov rax, 0x1 
shlx rdx, [ rsi + 0x20 ], rax
xchg rdx, r13
mulx rdi, rax, [ rsi + 0x20 ]
adox rax, r15
adox rcx, rdi
shrd r11, r12, 51
xor rdx, rdx
adox r14, r11
adox r10, rdx
mov rdx, rbx
mulx r15, rbx, [ rsi + 0x8 ]
adcx rbp, rbx
adcx r15, [ rsp - 0x48 ]
mulx rdi, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r12
adox rdi, rcx
mov rcx, r14
shrd rcx, r10, 51
mov r11, 0x7ffffffffffff 
and r14, r11
adox rax, rcx
adox rdi, rdx
mov rdx, r13
mulx r10, r13, [ rsi + 0x0 ]
adcx rbp, r13
adcx r10, r15
mov rdx, rax
shrd rdx, rdi, 51
add rbp, rdx
adc r10, 0x0
mov rbx, rbp
shrd rbx, r10, 51
imul r15, rbx, 0x13
and r8, r11
lea r8, [ r8 + r15 ]
mov r12, r8
shr r12, 51
lea r12, [ r12 + r9 ]
mov r9, r12
shr r9, 51
and r8, r11
and r12, r11
lea r9, [ r9 + r14 ]
and rbp, r11
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x10 ], r9
mov [ rcx + 0x8 ], r12
and rax, r11
mov [ rcx + 0x20 ], rbp
mov [ rcx + 0x18 ], rax
mov [ rcx + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.2166
; seed 0737932286558254 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1071575 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=173, initial num_batches=31): 94305 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08800597251708933
; number reverted permutation / tried permutation: 79237 / 90204 =87.842%
; number reverted decision / tried decision: 57398 / 89795 =63.921%
; validated in 0.325s
