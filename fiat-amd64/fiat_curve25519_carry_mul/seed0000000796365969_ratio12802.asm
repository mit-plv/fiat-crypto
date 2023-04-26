SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x8 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r10, [ rsi + 0x10 ]
imul rdx, [ rax + 0x10 ], 0x13
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
lea r15, [rdx + 8 * rdx]
lea rdi, [rdx + 2 * r15]
mov rdx, rdi
mulx r15, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rcx
mulx rcx, r13, [ rax + 0x18 ]
imul rdx, [ rax + 0x20 ], 0x13
xchg rdx, r14
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r13
mulx r13, rcx, [ rsi + 0x20 ]
xchg rdx, r14
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r9
xor r9, r9
adox rbp, rdi
adox r15, r12
mulx rdi, r12, [ rsi + 0x18 ]
adcx rcx, r12
adcx rdi, r13
add rbp, r10
adcx rbx, r15
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r12, r8
mov rdx, r11
mulx r8, r11, [ rsi + 0x20 ]
add rbp, [ rsp - 0x10 ]
adcx rbx, [ rsp - 0x18 ]
add r11, r12
adcx r9, r8
mov rdx, r14
mulx r12, r14, [ rsi + 0x10 ]
add r11, r14
adcx r12, r9
xor rdx, rdx
adox rbp, r10
adox r15, rbx
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, r13
adcx r11, r10
adcx r8, r12
mov rdx, [ rsi + 0x8 ]
mulx r9, rbx, [ rax + 0x8 ]
test al, al
adox rcx, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x38 ]
adcx rcx, rbx
adcx r9, rdi
mov rdx, [ rsi + 0x0 ]
mulx r12, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r11, r14
adox r12, r8
mov rdx, r13
mulx r10, r13, [ rsi + 0x20 ]
mov rdx, r11
shrd rdx, r12, 51
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mulx rdi, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox rbp, r8
adox r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r12, r14, [ rsi + 0x0 ]
adcx rcx, r14
adcx r12, r9
test al, al
adox r13, rbx
adox rdi, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, r9, [ rax + 0x8 ]
adcx r13, r9
adcx r10, rdi
mov rdx, [ rax + 0x10 ]
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rdi, r14, [ rax + 0x10 ]
mov rdx, rbp
shrd rdx, r15, 51
xor r15, r15
adox r13, r8
adox rbx, r10
adcx rcx, rdx
adc r12, 0x0
test al, al
adox r13, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
mov rdx, [ rax + 0x20 ]
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, rcx
shrd rdx, r12, 51
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ rax + 0x0 ]
xor rdx, rdx
adox r13, r8
adox rbx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mulx r10, r8, [ rax + 0x8 ]
adcx r12, r8
adcx r10, r15
add r12, r14
adcx rdi, r10
xor rdx, rdx
adox r12, [ rsp - 0x28 ]
adox rdi, [ rsp - 0x30 ]
mov r14, 0x33 
bzhi r15, r13, r14
shrd r13, rbx, 51
add r12, r9
adcx rdi, [ rsp - 0x8 ]
bzhi r9, rbp, r14
adox r12, r13
adox rdi, rdx
mov rbp, r12
shrd rbp, rdi, 51
bzhi rbx, r12, r14
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], r15
lea r10, [rbp + 8 * rbp]
lea r15, [rbp + 2 * r10]
bzhi r10, r11, r14
lea r10, [ r10 + r15 ]
mov r11, r10
shr r11, 51
bzhi r13, r10, r14
mov [ r8 + 0x0 ], r13
lea r11, [ r11 + r9 ]
bzhi r9, r11, r14
bzhi r12, rcx, r14
shr r11, 51
lea r11, [ r11 + r12 ]
mov [ r8 + 0x10 ], r11
mov [ r8 + 0x8 ], r9
mov [ r8 + 0x20 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.2802
; seed 1357506269625441 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1682065 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=115, initial num_batches=31): 110428 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06565025727305425
; number reverted permutation / tried permutation: 75054 / 89925 =83.463%
; number reverted decision / tried decision: 43044 / 90074 =47.787%
; validated in 0.504s
