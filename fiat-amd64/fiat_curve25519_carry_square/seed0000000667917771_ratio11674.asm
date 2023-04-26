SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x8 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, [ rsi + 0x20 ]
lea r8, [rdx + 8 * rdx]
lea r9, [rdx + 2 * r8]
mov rdx, [ rsi + 0x18 ]
lea r8, [rdx + rdx]
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
xchg rdx, r11
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
add r12, r14
adcx r15, r13
xor rdx, rdx
adox r12, rax
adox r10, r15
imul rax, [ rsi + 0x18 ], 0x13
mov r13, r12
shrd r13, r10, 51
mov rdx, rcx
mulx r14, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, r11
add r15, rax
adcx rdi, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r11, rdx
add r15, rcx
adcx r14, rdi
mov rdx, [ rsi + 0x10 ]
lea rcx, [rdx + rdx]
mov rdx, rcx
mulx rax, rcx, [ rsi + 0x0 ]
xor rdi, rdi
adox r15, r13
adox r14, rdi
mulx rdi, r13, [ rsi + 0x8 ]
mov rdx, r9
mov [ rsp - 0x48 ], r8
mulx r8, r9, [ rsi + 0x20 ]
adcx rbx, r11
adcx r10, rbp
add rbx, rcx
adcx rax, r10
mov rdx, r15
shrd rdx, r14, 51
xor rbp, rbp
adox rbx, rdx
adox rax, rbp
mov r11, 0x33 
bzhi rcx, r15, r11
adox r9, r13
adox rdi, r8
mov rdx, [ rsp - 0x48 ]
mulx r14, r15, [ rsi + 0x0 ]
mulx r8, r13, [ rsi + 0x8 ]
mov rdx, rbx
shrd rdx, rax, 51
xor r10, r10
adox r9, r15
adox r14, rdi
adcx r9, rdx
adc r14, 0x0
mov rbp, [ rsi + 0x20 ]
lea rax, [rbp + rbp]
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, rdx
mov rdx, rax
mulx r15, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r13
adox r8, rdi
mov r10, r9
shrd r10, r14, 51
add rbp, rax
adcx r15, r8
add rbp, r10
adc r15, 0x0
bzhi r13, r12, r11
mov r12, rbp
shrd r12, r15, 51
imul r14, r12, 0x13
lea r13, [ r13 + r14 ]
bzhi rdi, r13, r11
shr r13, 51
lea r13, [ r13 + rcx ]
bzhi rcx, r13, r11
bzhi rax, rbp, r11
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rcx
shr r13, 51
bzhi r10, rbx, r11
lea r13, [ r13 + r10 ]
bzhi rbx, r9, r11
mov [ r8 + 0x18 ], rbx
mov [ r8 + 0x0 ], rdi
mov [ r8 + 0x10 ], r13
mov [ r8 + 0x20 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1674
; seed 0991637571863842 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1078595 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=175, initial num_batches=31): 94758 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08785317936760323
; number reverted permutation / tried permutation: 78786 / 90067 =87.475%
; number reverted decision / tried decision: 56901 / 89932 =63.271%
; validated in 0.319s
