SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rdx
imul rdx, [ rsi + 0x20 ], 0x26
mulx r8, rcx, [ rsi + 0x8 ]
mov r9, 0x1 
mov [ rsp - 0x80 ], rbx
shlx rbx, [ rsi + 0x10 ], r9
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r10
adox r11, rbp
mov rdx, rax
mulx r10, rax, [ rsi + 0x10 ]
imul rdx, [ rsi + 0x8 ], 0x2
add rax, rcx
adcx r8, r10
mulx rbp, rcx, [ rsi + 0x0 ]
mov r10, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
lea rdx, [r10 + 8 * r10]
lea r14, [r10 + 2 * rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, r14
mov rdx, [ rsi + 0x18 ]
lea r14, [rdx + rdx]
mov rdx, r14
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r11
imul r11, [ rsi + 0x18 ], 0x13
mov [ rsp - 0x40 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r14
mulx r14, rdi, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], rcx
mulx rcx, rbp, rdx
xor rdx, rdx
adox rax, rbp
adox rcx, r8
mov r8, 0x33 
bzhi rbp, rax, r8
adox r10, rdi
adox r14, r15
mov rdx, r11
mulx r15, r11, [ rsi + 0x18 ]
shrd rax, rcx, 51
xor rdx, rdx
adox r11, r12
adox r13, r15
mov r12, [ rsi + 0x20 ]
lea rdi, [r12 + r12]
adcx r11, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x28 ]
mov rdx, rdi
mulx r12, rdi, [ rsi + 0x0 ]
add r11, rax
adc r13, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r15, rcx, rbx
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, rdx
add rbx, [ rsp - 0x30 ]
adcx rax, [ rsp - 0x38 ]
mov rdx, r11
shrd rdx, r13, 51
mov r13, rcx
add r13, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
xor rcx, rcx
adox rbx, rdi
adox r12, rax
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, r9
adcx r13, rdi
adc r15, 0x0
mov rdx, r13
shrd rdx, r15, 51
xor r9, r9
adox r10, rax
adox rcx, r14
adcx r10, rdx
adc rcx, 0x0
bzhi r14, r13, r8
mov rdi, r10
shrd rdi, rcx, 51
xor rax, rax
adox rbx, rdi
adox r12, rax
bzhi r9, r10, r8
mov r13, rbx
shrd r13, r12, 51
imul r15, r13, 0x13
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r9
lea rbp, [ rbp + r15 ]
bzhi r10, rbp, r8
bzhi rcx, rbx, r8
shr rbp, 51
mov [ rdx + 0x20 ], rcx
bzhi rdi, r11, r8
lea rbp, [ rbp + rdi ]
bzhi r11, rbp, r8
mov [ rdx + 0x8 ], r11
shr rbp, 51
lea rbp, [ rbp + r14 ]
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2002
; seed 1762958340383791 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6750 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=472, initial num_batches=31): 817 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.12103703703703704
; number reverted permutation / tried permutation: 402 / 494 =81.377%
; number reverted decision / tried decision: 385 / 505 =76.238%
; validated in 0.453s
