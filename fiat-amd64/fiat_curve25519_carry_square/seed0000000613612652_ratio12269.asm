SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, rdx
imul rdx, [ rsi + 0x20 ], 0x26
imul rcx, [ rsi + 0x20 ], 0x13
mov r8, [ rsi + 0x10 ]
mov r9, r8
shl r9, 0x1
mov r8, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov rbx, r8
shl rbx, 0x1
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, rax
mov [ rsp - 0x68 ], r13
mulx r13, rax, [ rsi + 0x10 ]
mov rdx, r8
mov [ rsp - 0x60 ], r14
mulx r14, r8, [ rsi + 0x8 ]
test al, al
adox rax, r8
adox r14, r13
adcx rax, r10
adcx r11, r14
mov r10, rax
shrd r10, r11, 51
mov r13, [ rsi + 0x18 ]
lea r8, [r13 + 8 * r13]
lea r14, [r13 + 2 * r8]
xchg rdx, r14
mulx r13, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r11, r14
xor rdx, rdx
adox r8, r11
adox r15, r13
mov rdx, rbx
mulx r13, rbx, [ rsi + 0x0 ]
adcx r8, rbx
adcx r13, r15
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, r14
add r11, rbp
adcx r12, r15
xor rdx, rdx
adox r8, r10
adox r13, rdx
mov rdx, r9
mulx r14, r9, [ rsi + 0x0 ]
adcx r11, r9
adcx r14, r12
mulx r10, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov rbx, rdx
shl rbx, 0x1
mov rdx, rcx
mulx r15, rcx, [ rsi + 0x20 ]
test al, al
adox rcx, rbp
adox r10, r15
mov rdx, r8
shrd rdx, r13, 51
xor r12, r12
adox r11, rdx
adox r14, r12
mov rdx, rbx
mulx r13, rbx, [ rsi + 0x0 ]
adcx rcx, rbx
adcx r13, r10
mov r9, r11
shrd r9, r14, 51
mov rbp, 0x33 
bzhi r15, r11, rbp
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r14, rdx
mov rdx, [ rsi + 0x20 ]
mov r12, rdx
shl r12, 0x1
add rcx, r9
adc r13, 0x0
add r14, r10
adcx r11, rbx
mov rdx, r12
mulx r9, r12, [ rsi + 0x0 ]
xor r10, r10
adox r14, r12
adox r9, r11
mov rbx, rcx
shrd rbx, r13, 51
test al, al
adox r14, rbx
adox r9, r10
bzhi rdx, r14, rbp
bzhi r13, rax, rbp
shrd r14, r9, 51
imul rax, r14, 0x13
lea r13, [ r13 + rax ]
bzhi r11, r13, rbp
bzhi r12, r8, rbp
shr r13, 51
lea r13, [ r13 + r12 ]
bzhi r8, r13, rbp
bzhi rbx, rcx, rbp
shr r13, 51
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x18 ], rbx
lea r13, [ r13 + r15 ]
mov [ rdi + 0x20 ], rdx
mov [ rdi + 0x10 ], r13
mov [ rdi + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.2269
; seed 2889311046755118 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1036835 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=174, initial num_batches=31): 88633 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08548418986627573
; number reverted permutation / tried permutation: 79510 / 89862 =88.480%
; number reverted decision / tried decision: 57114 / 90137 =63.364%
; validated in 0.321s
