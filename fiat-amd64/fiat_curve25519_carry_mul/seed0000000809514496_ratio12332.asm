SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x18 ], 0x13
mov r10, [ rdx + 0x8 ]
lea r11, [r10 + 8 * r10]
lea rcx, [r10 + 2 * r11]
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ r10 + 0x8 ]
imul rdx, [ r10 + 0x10 ], 0x13
mov r9, [ r10 + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
lea rbx, [r9 + 8 * r9]
lea rbp, [r9 + 2 * rbx]
mov r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ r10 + 0x10 ]
mov rdx, rax
mov [ rsp - 0x68 ], r13
mulx r13, rax, [ rsi + 0x20 ]
xchg rdx, r9
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x20 ]
mov rdx, rcx
mov [ rsp - 0x40 ], rbx
mulx rbx, rcx, [ rsi + 0x20 ]
xor rdx, rdx
adox rcx, r14
adox r15, rbx
mov rdx, r9
mulx r14, r9, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
adcx rcx, r9
adcx r14, r15
add rdi, rbx
adcx r13, r12
mov rdx, [ rsi + 0x10 ]
mulx r15, r12, rbp
xor rdx, rdx
adox rdi, r12
adox r15, r13
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, [ r10 + 0x0 ]
adcx rdi, r9
adcx rbx, r15
add rdi, r11
adcx r8, rbx
mov rdx, [ rsi + 0x8 ]
mulx r13, r11, rbp
mov rdx, rbp
mulx r12, rbp, [ rsi + 0x18 ]
xor r15, r15
adox rax, rbp
adox r12, [ rsp - 0x38 ]
adcx rcx, r11
adcx r13, r14
mov r14, rdx
mov rdx, [ r10 + 0x0 ]
mulx rbx, r9, [ rsi + 0x0 ]
add rcx, r9
adcx rbx, r13
mov rdx, rcx
shrd rdx, rbx, 51
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ r10 + 0x8 ]
add rdi, r11
adc r8, 0x0
mov rdx, [ rsi + 0x20 ]
mulx rbx, r9, r14
mov rdx, [ r10 + 0x0 ]
mulx r11, r14, [ rsi + 0x18 ]
add r9, r14
adcx r11, rbx
mov rdx, [ r10 + 0x8 ]
mulx r14, rbx, [ rsi + 0x8 ]
mov rdx, 0x33 
bzhi r15, rdi, rdx
adox r9, rbp
adox r13, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ r10 + 0x0 ]
test al, al
adox rax, rbp
adox r11, r12
adcx rax, rbx
adcx r14, r11
xor rdx, rdx
adox r9, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov rdx, [ r10 + 0x10 ]
mulx rbx, r12, [ rsi + 0x0 ]
shrd rdi, r8, 51
test al, al
adox rax, r12
adox rbx, r14
adcx rax, rdi
adc rbx, 0x0
mov rdx, rax
shrd rdx, rbx, 51
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ r10 + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ r10 + 0x18 ]
mov rdx, 0x33 
bzhi rdi, rax, rdx
mov rdx, [ r10 + 0x8 ]
mulx rbx, rax, [ rsi + 0x18 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r12
mov [ rsp - 0x18 ], r14
mulx r14, r12, [ r10 + 0x20 ]
adox r9, rbp
adox r11, r13
add rdi, rax
adcx rbx, r15
mov rdx, [ r10 + 0x10 ]
mulx rbp, r13, [ rsi + 0x10 ]
xor rdx, rdx
adox rdi, r13
adox rbp, rbx
adcx r9, r8
adc r11, 0x0
mov r8, r9
shrd r8, r11, 51
mov rax, 0x33 
bzhi r15, r9, rax
adox rdi, [ rsp - 0x18 ]
adox rbp, [ rsp - 0x20 ]
xor rbx, rbx
adox rdi, r12
adox r14, rbp
adcx rdi, r8
adc r14, 0x0
mov rdx, rdi
shrd rdx, r14, 51
bzhi r12, rcx, rax
lea rcx, [rdx + 8 * rdx]
lea r13, [rdx + 2 * rcx]
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], r15
lea r12, [ r12 + r13 ]
mov r9, r12
shr r9, 51
add r9, [ rsp - 0x28 ]
bzhi r11, r12, rax
bzhi r8, r9, rax
mov [ rcx + 0x8 ], r8
mov [ rcx + 0x0 ], r11
bzhi r15, rdi, rax
mov [ rcx + 0x20 ], r15
shr r9, 51
add r9, [ rsp - 0x30 ]
mov [ rcx + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2332
; seed 0229716801166038 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1895315 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=168, initial num_batches=31): 130448 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06882655389737326
; number reverted permutation / tried permutation: 68822 / 90069 =76.410%
; number reverted decision / tried decision: 55859 / 89930 =62.114%
; validated in 0.555s
