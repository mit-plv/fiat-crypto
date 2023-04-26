SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x10 ], 0x13
imul r10, [ rdx + 0x20 ], 0x13
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ r11 + 0x8 ]
mov rdx, [ r11 + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, rax
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ r11 + 0x8 ]
mov rdx, [ r11 + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, r10
imul rdx, [ r11 + 0x8 ], 0x13
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
imul rdx, [ r11 + 0x18 ], 0x13
mov [ rsp - 0x28 ], r14
xor r14, r14
adox r8, rax
adox rbp, rcx
mulx rcx, rax, [ rsi + 0x10 ]
adcx r8, rax
adcx rcx, rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rax, [ r11 + 0x0 ]
mov rdx, r10
mov [ rsp - 0x20 ], r13
mulx r13, r10, [ rsi + 0x20 ]
add r8, rbx
adcx r9, rcx
mov rbx, rdx
mov rdx, [ r11 + 0x0 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rcx, [ rsi + 0x0 ]
test al, al
adox r10, rax
adox r14, r13
adcx r8, rcx
adcx rdi, r9
mov rdx, [ rsi + 0x20 ]
mulx r13, rax, rbp
mov rdx, r8
shrd rdx, rdi, 51
mov r9, 0x7ffffffffffff 
and r8, r9
xchg rdx, rbx
mulx rdi, rcx, [ rsi + 0x18 ]
adox rax, rcx
adox rdi, r13
adcx rax, r15
adcx rdi, [ rsp - 0x18 ]
mulx r13, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, rcx, r12
mov rdx, rbp
mulx r12, rbp, [ rsi + 0x18 ]
adcx rcx, rbp
adcx r12, r9
xor rdx, rdx
adox rcx, r15
adox r13, r12
mov rdx, [ rsi + 0x8 ]
mulx r9, r15, [ r11 + 0x0 ]
adcx rcx, r15
adcx r9, r13
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, [ r11 + 0x8 ]
xor rdx, rdx
adox rcx, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx rcx, rbx
adc r9, 0x0
mov rbx, rcx
shrd rbx, r9, 51
xor r13, r13
adox rax, [ rsp - 0x40 ]
adox rdi, [ rsp - 0x48 ]
mov rdx, [ r11 + 0x10 ]
mulx r9, r15, [ rsi + 0x8 ]
mov rdx, 0x33 
bzhi r13, rcx, rdx
adox rax, rbx
mov rcx, 0x0 
adox rdi, rcx
mov rdx, [ r11 + 0x0 ]
mulx rcx, rbx, [ rsi + 0x20 ]
xor rdx, rdx
adox rbx, rbp
adox r12, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbp, [ r11 + 0x8 ]
adcx r10, rbp
adcx rcx, r14
xor rdx, rdx
adox r10, r15
adox r9, rcx
mov rdx, [ r11 + 0x10 ]
mulx r15, r14, [ rsi + 0x10 ]
adcx rbx, r14
adcx r15, r12
mov rdx, [ r11 + 0x18 ]
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ r11 + 0x18 ]
mulx r14, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, rcx
adox r14, r9
mov r9, rax
shrd r9, rdi, 51
mov rdx, [ r11 + 0x20 ]
mulx rcx, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, r9
adox r14, rdx
mov r9, r10
shrd r9, r14, 51
mov r14, 0x7ffffffffffff 
and rax, r14
and r10, r14
adox rbx, r12
adox rbp, r15
adcx rbx, rdi
adcx rcx, rbp
xor r15, r15
adox rbx, r9
adox rcx, r15
mov rdx, rbx
shrd rdx, rcx, 51
imul r12, rdx, 0x13
lea r8, [ r8 + r12 ]
mov rdi, r8
shr rdi, 51
lea rdi, [ rdi + r13 ]
mov r13, rdi
and r13, r14
shr rdi, 51
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], r13
lea rdi, [ rdi + rax ]
and r8, r14
and rbx, r14
mov [ r9 + 0x20 ], rbx
mov [ r9 + 0x18 ], r10
mov [ r9 + 0x0 ], r8
mov [ r9 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2388
; seed 2558002046072018 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1907903 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 131150 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06874039193816457
; number reverted permutation / tried permutation: 69541 / 89855 =77.392%
; number reverted decision / tried decision: 56420 / 90144 =62.589%
; validated in 0.522s
