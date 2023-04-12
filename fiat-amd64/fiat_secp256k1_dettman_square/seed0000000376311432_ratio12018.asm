SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x8 ]
lea rdx, [r11 + r11]
mov r11, [ rsi + 0x0 ]
lea rcx, [r11 + r11]
mov r11, 0xfffffffffffff 
mov r8, rax
and r8, r11
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rcx
adox r9, r12
adox r13, rbx
mov rdx, 0x1000003d10 
mulx r12, rbx, r8
adcx rbx, r9
adcx r13, r12
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, r12, rdx
shrd rax, r10, 52
xor rdx, rdx
adox r12, r8
adox r9, r14
mov rdx, [ rsi + 0x20 ]
mulx r8, r10, rcx
mov rdx, 0x1000003d10 
mov [ rsp - 0x58 ], r15
mulx r15, r14, rax
mov rax, [ rsi + 0x10 ]
mov rdx, rax
shl rdx, 0x1
mov rax, rbx
shrd rax, r13, 52
xor r13, r13
adox r12, r10
adox r8, r9
adcx rax, r12
adc r8, 0x0
xor r9, r9
adox r14, rax
adox r8, r15
mov r13, r14
shrd r13, r8, 52
mulx r15, r10, [ rsi + 0x20 ]
mulx rax, r12, [ rsi + 0x18 ]
mov rdx, rbp
mulx r8, rbp, [ rsi + 0x20 ]
and r14, r11
adox r12, rbp
adox r8, rax
adcx r13, r12
adc r8, 0x0
mov rdx, r13
and rdx, r11
shl rdx, 4
shrd r13, r8, 52
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, rdx
xor rdx, rdx
adox rbp, r10
adox r15, r12
mov r9, r14
shr r9, 48
lea rax, [ rax + r9 ]
mov r10, 0x1000003d1 
mov rdx, r10
mulx r8, r10, rax
xor r12, r12
adox r13, rbp
adox r15, r12
mov rbp, r13
and rbp, r11
imul r9, [ rsi + 0x18 ], 0x2
mov rdx, r9
mulx rax, r9, [ rsi + 0x20 ]
shrd r13, r15, 52
add r13, r9
adc rax, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r9, r15, rdx
xor rdx, rdx
adox r10, r15
adox r9, r8
mov r12, r10
and r12, r11
shrd r10, r9, 52
mov rdx, [ rsi + 0x10 ]
mulx r15, r8, rcx
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x8 ]
xor rdx, rdx
adox r10, rcx
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rcx, rdx
adcx rcx, r8
adcx r15, r11
mov rdx, 0x1000003d10 
mulx r11, r8, rbp
add r8, r10
adcx r9, r11
mov rbp, r8
shrd rbp, r9, 52
mov [ rdi + 0x0 ], r12
xor r12, r12
adox rbp, rcx
adox r15, r12
mov r10, 0xfffffffffffff 
mov rcx, r13
and rcx, r10
mulx r9, r11, rcx
adox r11, rbp
adox r15, r9
and r8, r10
mov [ rdi + 0x8 ], r8
mov rbp, r11
shrd rbp, r15, 52
and rbx, r10
lea rbx, [ rbx + rbp ]
shrd r13, rax, 52
mulx rcx, rax, r13
add rax, rbx
adc rcx, 0x0
and r11, r10
mov [ rdi + 0x10 ], r11
mov r9, rax
shrd r9, rcx, 52
mov r15, 0xffffffffffff 
and r14, r15
lea r14, [ r14 + r9 ]
mov [ rdi + 0x20 ], r14
and rax, r10
mov [ rdi + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2018
; seed 0171085932788745 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 650350 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=451, initial num_batches=31): 78591 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12084416083647267
; number reverted permutation / tried permutation: 76718 / 89987 =85.255%
; number reverted decision / tried decision: 67604 / 90012 =75.106%
; validated in 0.163s
