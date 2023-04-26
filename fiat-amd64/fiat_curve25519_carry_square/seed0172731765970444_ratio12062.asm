SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x13
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, rdx
imul rdx, [ rsi + 0x20 ], 0x26
mulx r8, rcx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
lea r14, [rdx + rdx]
xor rdx, rdx
adox rcx, r12
adox r13, r8
mov r8, [ rsi + 0x20 ]
lea r12, [r8 + 8 * r8]
lea rdx, [r8 + 2 * r12]
mulx r12, r8, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rdx
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r15
mulx r15, rdi, rax
add rdi, r9
adcx rbx, r15
mov rdx, [ rsi + 0x8 ]
lea rax, [rdx + rdx]
mov rdx, rax
mulx r9, rax, [ rsi + 0x0 ]
xor r15, r15
adox rdi, rax
adox r9, rbx
mov rdx, [ rsi + 0x8 ]
mulx rax, rbx, rbp
mov rdx, [ rsi + 0x10 ]
lea rbp, [rdx + rdx]
adcx r11, rbx
adcx rax, r10
mov rdx, r14
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, rbp
xor rdx, rdx
adox rcx, rbx
adox r15, r13
mov rdx, [ rsi + 0x8 ]
mulx rbx, r13, rbp
adcx r8, r13
adcx rbx, r12
test al, al
adox r11, [ rsp - 0x28 ]
adox rax, [ rsp - 0x30 ]
mov rdx, r11
shrd rdx, rax, 51
xor r12, r12
adox rdi, rdx
adox r9, r12
mov rdx, [ rsp - 0x38 ]
mulx r13, rbp, [ rsi + 0x8 ]
mov rax, rbp
adcx rax, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mulx r12, rbp, [ rsi + 0x0 ]
add r8, rbp
adcx r12, rbx
mov rdx, rdi
shrd rdx, r9, 51
xor rbx, rbx
adox rcx, rdx
adox r15, rbx
mov r9, rcx
shrd r9, r15, 51
mov rbp, 0x33 
bzhi rdx, rcx, rbp
adox r8, r9
adox r12, rbx
bzhi rcx, r8, rbp
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], rcx
shrd r8, r12, 51
add rax, r14
adcx r10, r13
add rax, r8
adc r10, 0x0
mov r14, rax
shrd r14, r10, 51
imul r13, r14, 0x13
bzhi r9, r11, rbp
lea r9, [ r9 + r13 ]
mov r11, r9
shr r11, 51
bzhi r12, rdi, rbp
lea r11, [ r11 + r12 ]
bzhi rdi, r11, rbp
shr r11, 51
lea r11, [ r11 + rdx ]
bzhi rdx, rax, rbp
mov [ r15 + 0x10 ], r11
mov [ r15 + 0x20 ], rdx
bzhi rcx, r9, rbp
mov [ r15 + 0x8 ], rdi
mov [ r15 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2062
; seed 0172731765970444 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7380 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=237, initial num_batches=31): 649 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08794037940379404
; number reverted permutation / tried permutation: 380 / 474 =80.169%
; number reverted decision / tried decision: 383 / 525 =72.952%
; validated in 0.372s
