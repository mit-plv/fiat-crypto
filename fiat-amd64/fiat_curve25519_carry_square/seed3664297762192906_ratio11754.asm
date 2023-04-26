SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov r11, 0x1 
shlx rdx, [ rsi + 0x10 ], r11
imul rcx, [ rsi + 0x20 ], 0x13
mulx r9, r8, [ rsi + 0x8 ]
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x70 ], r12
mov r12, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rsi + 0x18 ], r12
mov [ rsp - 0x60 ], r14
mulx r14, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rcx
mov rdx, r13
mulx rcx, r13, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r10
xor r10, r10
adox r15, r8
adox r9, rdi
mulx rdi, r8, [ rsi + 0x0 ]
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x40 ], r9
mulx r9, r10, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
add r12, r10
adcx r9, r14
imul r14, [ rsi + 0x18 ], 0x13
test al, al
adox rbx, r13
adox rcx, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r8
lea r8, [rdx + rdx]
mov rdx, r8
mov [ rsp - 0x20 ], rax
mulx rax, r8, [ rsi + 0x0 ]
adcx r12, r13
adcx r10, r9
mov r9, r12
shrd r9, r10, 51
mov r13, [ rsi + 0x20 ]
mov rdx, r13
shl rdx, 0x1
mov r13, 0x33 
mov [ rsp - 0x18 ], r11
bzhi r11, r12, r13
mulx r10, r12, [ rsi + 0x0 ]
adox rbx, r12
adox r10, rcx
mov rdx, [ rsi + 0x18 ]
mulx r12, rcx, r14
add rcx, r15
adcx rdi, r12
xor rdx, rdx
adox rcx, r8
adox rax, rdi
adcx rcx, r9
adc rax, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r14, r15, rbp
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ rsp - 0x18 ]
add r15, [ rsp - 0x20 ]
adcx r14, [ rsp - 0x48 ]
mov rdx, rcx
shrd rdx, rax, 51
add r15, rbp
adcx r8, r14
xor r9, r9
adox r15, rdx
adox r8, r9
mov r12, [ rsp - 0x38 ]
adcx r12, [ rsp - 0x28 ]
mov rdi, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x30 ]
mov rax, r15
shrd rax, r8, 51
add r12, rax
adc rdi, 0x0
bzhi rbp, r12, r13
bzhi r14, r15, r13
shrd r12, rdi, 51
add rbx, r12
adc r10, 0x0
mov rdx, rbx
shrd rdx, r10, 51
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], rbp
imul r8, rdx, 0x13
lea r11, [ r11 + r8 ]
mov rax, r11
shr rax, 51
bzhi rdi, rcx, r13
lea rax, [ rax + rdi ]
bzhi rcx, rax, r13
mov [ r15 + 0x8 ], rcx
shr rax, 51
bzhi rbp, rbx, r13
mov [ r15 + 0x20 ], rbp
bzhi r12, r11, r13
lea rax, [ rax + r14 ]
mov [ r15 + 0x0 ], r12
mov [ r15 + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1754
; seed 3664297762192906 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4245 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=342, initial num_batches=31): 396 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09328621908127209
; number reverted permutation / tried permutation: 388 / 493 =78.702%
; number reverted decision / tried decision: 390 / 506 =77.075%
; validated in 0.31s
