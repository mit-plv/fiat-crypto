SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x8 ], 0x13
mov r10, [ rdx + 0x10 ]
lea r11, [r10 + 8 * r10]
lea rcx, [r10 + 2 * r11]
mov r10, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ r10 + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ r10 + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rax
mov rdx, [ r10 + 0x10 ]
mov [ rsp - 0x68 ], r13
mulx r13, rax, [ rsi + 0x8 ]
imul rdx, [ r10 + 0x18 ], 0x13
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov rdi, [ r10 + 0x20 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rax
lea r13, [rdi + 8 * rdi]
lea rax, [rdi + 2 * r13]
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r8
mulx r8, r13, rcx
xor rdx, rdx
adox rbp, r13
adox r8, r12
mov rdx, rax
mulx r12, rax, [ rsi + 0x8 ]
adcx rbp, r14
adcx r15, r8
add rbp, rax
adcx r12, r15
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ r10 + 0x0 ]
xor rdx, rdx
adox rbp, r13
adox r8, r12
mov rdx, [ rsi + 0x18 ]
mulx r15, rax, rdi
mov rdx, rcx
mulx r12, rcx, [ rsi + 0x20 ]
adcx rcx, rax
adcx r15, r12
mov rdx, r14
mulx r13, r14, [ rsi + 0x10 ]
test al, al
adox rcx, r14
adox r13, r15
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r15, r12, [ r10 + 0x0 ]
adcx rcx, r12
adcx r15, r13
xor rdx, rdx
adox rcx, r9
adox rbx, r15
mov r9, rbp
shrd r9, r8, 51
test al, al
adox rcx, r9
adox rbx, rdx
mov r8, rcx
shrd r8, rbx, 51
mov r14, 0x33 
bzhi r13, rcx, r14
mov rdx, [ rsi + 0x18 ]
mulx r15, r12, rax
mov rdx, [ r10 + 0x0 ]
mulx rcx, r9, [ rsi + 0x18 ]
mov rdx, rdi
mulx rbx, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r13
mulx r13, r14, rax
adox r14, r9
adox rcx, r13
test al, al
adox rdi, r12
adox r15, rbx
mov rdx, [ r10 + 0x0 ]
mulx r12, rax, [ rsi + 0x10 ]
adcx rdi, rax
adcx r12, r15
mov rdx, [ r10 + 0x8 ]
mulx rbx, r9, [ rsi + 0x8 ]
test al, al
adox rdi, r9
adox rbx, r12
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, [ r10 + 0x8 ]
adcx rdi, r11
adcx rbx, [ rsp - 0x38 ]
add rdi, r8
adc rbx, 0x0
mov rdx, [ r10 + 0x0 ]
mulx r8, r11, [ rsi + 0x20 ]
mov rdx, rdi
shrd rdx, rbx, 51
mov rax, rdx
mov rdx, [ r10 + 0x10 ]
mulx r9, r12, [ rsi + 0x10 ]
add r11, r13
adcx r15, r8
add r11, r12
adcx r9, r15
mov rdx, [ r10 + 0x8 ]
mulx rbx, r13, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, r13
adox rbx, rcx
adcx r14, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ r10 + 0x18 ]
add r14, rcx
adcx r8, rbx
add r14, rax
adc r8, 0x0
mov rdx, [ r10 + 0x18 ]
mulx r12, rax, [ rsi + 0x8 ]
mov rdx, 0x33 
bzhi r15, r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r13, [ r10 + 0x20 ]
adox r11, rax
adox r12, r9
add r11, r13
adcx rbx, r12
shrd r14, r8, 51
add r11, r14
adc rbx, 0x0
mov rdx, 0x7ffffffffffff 
mov r9, r11
and r9, rdx
shrd r11, rbx, 51
lea rcx, [r11 + 8 * r11]
lea r8, [r11 + 2 * rcx]
and rbp, rdx
lea rbp, [ rbp + r8 ]
mov rcx, rbp
shr rcx, 51
and rbp, rdx
add rcx, [ rsp - 0x30 ]
mov rax, rcx
shr rax, 51
and rdi, rdx
lea rax, [ rax + rdi ]
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rbp
and rcx, rdx
mov [ r13 + 0x10 ], rax
mov [ r13 + 0x18 ], r15
mov [ r13 + 0x8 ], rcx
mov [ r13 + 0x20 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2278
; seed 2185309322036430 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1207575 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=182, initial num_batches=31): 84418 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06990704511106971
; number reverted permutation / tried permutation: 72067 / 89966 =80.105%
; number reverted decision / tried decision: 57551 / 90033 =63.922%
; validated in 0.525s
