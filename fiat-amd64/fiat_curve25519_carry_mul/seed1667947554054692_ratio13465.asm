SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
sub rsp, 136
imul rax, [ rdx + 0x18 ], 0x13
imul r10, [ rdx + 0x10 ], 0x13
xchg rdx, rax
mulx rcx, r11, [ rsi + 0x18 ]
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r8
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
imul rdx, [ rax + 0x8 ], 0x13
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, r10
mov rdx, r10
mov [ rsp - 0x28 ], r12
mulx r12, r10, [ rsi + 0x20 ]
imul rdx, [ rax + 0x20 ], 0x13
add rbx, rdi
adcx r15, r9
add r10, r11
adcx rcx, r12
mulx r9, r11, [ rsi + 0x8 ]
mov rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r12, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], r14
mulx r14, r8, [ rsi + 0x18 ]
mov rdx, rdi
mov [ rsp - 0x10 ], r13
mulx r13, rdi, [ rsi + 0x20 ]
test al, al
adox rdi, r8
adox r14, r13
adcx rbx, r12
adcx rbp, r15
mulx r12, r15, [ rsi + 0x10 ]
xor r8, r8
adox r10, r15
adox r12, rcx
adcx rbx, r11
adcx r9, rbp
mov rcx, rdx
mov rdx, [ rax + 0x8 ]
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, rbp, [ rax + 0x0 ]
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x18 ]
xor rdx, rdx
adox rdi, r11
adox r13, r14
mov r14, rcx
adcx r14, [ rsp - 0x10 ]
adcx r8, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], rdi
mulx rdi, r13, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r11
adox rcx, r9
adcx r10, r13
adcx rdi, r12
mov rdx, [ rsi + 0x10 ]
mulx r9, r12, [ rax + 0x10 ]
add r10, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
mov rdx, rbx
shrd rdx, rcx, 51
mov r11, 0x33 
bzhi r13, rbx, r11
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mulx r11, rcx, [ rsi + 0x18 ]
adox rbp, rcx
adox r11, r15
add rbp, r12
adcx r9, r11
add r10, rbx
adc rdi, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r12, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, rbx, [ rsi + 0x8 ]
mov rdx, 0x33 
bzhi r11, r10, rdx
shrd r10, rdi, 51
add rbp, rbx
adcx rcx, r9
mov rdx, [ rax + 0x0 ]
mulx rdi, r9, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, r9
adox rdi, r8
adcx r14, r15
adcx r12, rdi
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, [ rax + 0x10 ]
add r14, r8
adcx r15, r12
add r14, r10
adc r15, 0x0
mov rdx, r14
shrd rdx, r15, 51
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, r10, [ rsi + 0x8 ]
mov rdx, r10
add rdx, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x8 ]
mov rdi, 0x33 
bzhi r12, r14, rdi
adox rdx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
add rdx, rbx
adc r9, 0x0
xor r8, r8
adox rbp, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
bzhi r14, rdx, rdi
shrd rdx, r9, 51
add rbp, rdx
adc rcx, 0x0
mov r15, rbp
shrd r15, rcx, 51
imul rbx, r15, 0x13
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], r14
bzhi r9, rbp, rdi
mov [ r10 + 0x20 ], r9
lea r13, [ r13 + rbx ]
bzhi r14, r13, rdi
mov [ r10 + 0x0 ], r14
shr r13, 51
lea r13, [ r13 + r11 ]
bzhi r11, r13, rdi
shr r13, 51
lea r13, [ r13 + r12 ]
mov [ r10 + 0x10 ], r13
mov [ r10 + 0x8 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3465
; seed 1667947554054692 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8522 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=157, initial num_batches=31): 495 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05808495658296175
; number reverted permutation / tried permutation: 394 / 495 =79.596%
; number reverted decision / tried decision: 331 / 504 =65.675%
; validated in 0.532s
