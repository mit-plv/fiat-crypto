SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
imul rdx, [ rax + 0x20 ], 0x13
mov r9, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
lea rbx, [r9 + 8 * r9]
lea rbp, [r9 + 2 * rbx]
mov r9, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rax + 0x0 ]
mov rdx, r9
mov [ rsp - 0x40 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rdi
xor rdi, rdi
adox r9, r13
adox r15, rbp
mov r13, rdx
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbp, [ rax + 0x0 ]
adcx rbp, r10
adcx r11, rdi
xor rdx, rdx
adox r9, rcx
adox r8, r15
mov rdx, [ rax + 0x18 ]
mulx rcx, r10, [ rsi + 0x0 ]
adcx r9, rbx
adcx r12, r8
test al, al
adox r9, r10
adox rcx, r12
mov rdx, r14
mulx rbx, r14, [ rsi + 0x20 ]
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, r13
imul rdx, [ rax + 0x10 ], 0x13
mulx r12, r10, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r9
mulx r9, rcx, [ rsi + 0x18 ]
mov rdx, [ rsp - 0x48 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], rbp
mulx rbp, r11, [ rsi + 0x20 ]
xor rdx, rdx
adox r11, rcx
adox r9, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, rcx, r15
adcx r14, rdi
adcx r8, rbx
xor rdx, rdx
adox r10, rcx
adox rbp, r12
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rax + 0x8 ]
adcx r14, [ rsp - 0x38 ]
adcx r8, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, r15
add r14, rbx
adcx rdi, r8
xor rdx, rdx
adox r11, r12
adox rcx, r9
mov rdx, r13
mulx r15, r13, [ rsi + 0x8 ]
adcx r11, r13
adcx r15, rcx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ rax + 0x8 ]
xor rdx, rdx
adox r10, r9
adox rbx, rbp
adcx r14, r8
adcx r12, rdi
mov rdx, [ rax + 0x0 ]
mulx rdi, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rax + 0x0 ]
xor rdx, rdx
adox r11, r9
adox r8, r15
mov rdx, [ rax + 0x18 ]
mulx r9, r15, [ rsi + 0x8 ]
adcx r10, rbp
adcx rdi, rbx
mov rdx, [ rax + 0x10 ]
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, rbx
add rdx, [ rsp - 0x18 ]
adcx rbp, [ rsp - 0x20 ]
mov rbx, r11
shrd rbx, r8, 51
xor r8, r8
adox r10, rcx
adox r13, rdi
adcx r10, rbx
adc r13, 0x0
mov rcx, r10
shrd rcx, r13, 51
xor rdi, rdi
adox r14, rcx
adox r12, rdi
mov r8, r14
shrd r8, r12, 51
mov rbx, 0x7ffffffffffff 
and r14, rbx
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mulx r12, rcx, [ rsi + 0x0 ]
and r10, rbx
adox r13, r15
adox r9, rbp
adcx r13, rcx
adcx r12, r9
mov rdx, r8
add rdx, [ rsp - 0x28 ]
mov r15, [ rsp - 0x30 ]
adc r15, 0x0
mov rbp, rdx
and rbp, rbx
shrd rdx, r15, 51
xor r8, r8
adox r13, rdx
adox r12, r8
mov rdi, r13
and rdi, rbx
shrd r13, r12, 51
imul rcx, r13, 0x13
and r11, rbx
lea r11, [ r11 + rcx ]
mov r9, r11
shr r9, 51
lea r9, [ r9 + r10 ]
mov r10, r9
shr r10, 51
lea r10, [ r10 + r14 ]
and r9, rbx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], r9
and r11, rbx
mov [ r14 + 0x0 ], r11
mov [ r14 + 0x18 ], rbp
mov [ r14 + 0x20 ], rdi
mov [ r14 + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2358
; seed 1673312760247152 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10173 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=335, initial num_batches=31): 858 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.0843409023886759
; number reverted permutation / tried permutation: 370 / 480 =77.083%
; number reverted decision / tried decision: 324 / 519 =62.428%
; validated in 0.705s
