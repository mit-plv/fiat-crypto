SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
imul r10, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
imul rdx, [ rsi + 0x20 ], 0x13
mov [ rsp - 0x80 ], rbx
mov rbx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rbx + rbx]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
imul rdx, [ rsi + 0x18 ], 0x13
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r8
mulx r8, r9, rbp
xor rdx, rdx
adox r15, r11
adox rcx, rdi
adcx rbx, r9
adcx r8, r12
mov r11, [ rsi + 0x18 ]
lea rbp, [r11 + r11]
mov rdx, r13
mulx r13, r11, [ rsi + 0x0 ]
mov rdx, r14
mulx r12, r14, [ rsi + 0x0 ]
mov rdx, rbp
mulx rdi, rbp, [ rsi + 0x8 ]
test al, al
adox r15, r14
adox r12, rcx
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rbx
mulx rbx, r8, rax
adcx rcx, rbp
adcx rdi, r14
mov rdx, r10
mulx rbp, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, r14, rdx
xor rdx, rdx
adox r10, r8
adox rbx, rbp
adcx r10, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x38 ]
mov r8, r10
shrd r8, rbx, 51
add r15, r8
adc r12, 0x0
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, rax
mov rdx, 0x33 
bzhi rax, r15, rdx
bzhi r8, r10, rdx
adox rcx, r11
adox r13, [ rsp - 0x18 ]
xor r11, r11
adox rbp, r14
adox rdi, rbx
shrd r15, r12, 51
xor r14, r14
adox rbp, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
adcx rbp, r15
adc rdi, 0x0
mov r11, rbp
shrd r11, rdi, 51
mov rdx, r9
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, r9
xor r12, r12
adox rdx, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
adcx rdx, r11
adc r10, 0x0
mov r14, 0x33 
bzhi rbx, rbp, r14
bzhi r15, rdx, r14
shrd rdx, r10, 51
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r15
xor rdi, rdi
adox rcx, rdx
adox r13, rdi
bzhi r12, rcx, r14
shrd rcx, r13, 51
mov [ rbp + 0x20 ], r12
imul r11, rcx, 0x13
lea r8, [ r8 + r11 ]
mov r9, r8
shr r9, 51
lea r9, [ r9 + rax ]
bzhi rax, r9, r14
shr r9, 51
mov [ rbp + 0x8 ], rax
lea r9, [ r9 + rbx ]
bzhi r10, r8, r14
mov [ rbp + 0x0 ], r10
mov [ rbp + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1968
; seed 1908250801133956 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5097 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=250, initial num_batches=31): 432 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08475573866980576
; number reverted permutation / tried permutation: 395 / 500 =79.000%
; number reverted decision / tried decision: 370 / 499 =74.148%
; validated in 0.33s
