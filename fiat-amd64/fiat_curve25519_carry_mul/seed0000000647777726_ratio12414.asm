SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, r11
imul rdx, [ rax + 0x8 ], 0x13
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
lea rbp, [rdx + 8 * rdx]
lea r12, [rdx + 2 * rbp]
mov rdx, r12
mulx r12, rbp, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r10
adox rcx, r12
mov rdx, r13
mulx r10, r13, [ rsi + 0x10 ]
mov r12, [ rax + 0x10 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
lea rbx, [r12 + 8 * r12]
lea rdi, [r12 + 2 * rbx]
xchg rdx, rdi
mulx r12, rbx, [ rsi + 0x20 ]
adcx rbp, r14
adcx r15, rcx
mulx rcx, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], rbp
mulx rbp, r15, rdi
xor rdx, rdx
adox rbx, r15
adox rbp, r12
mov rdx, r11
mulx rdi, r11, [ rsi + 0x10 ]
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r9
mulx r9, r15, r8
adcx r15, r14
adcx rcx, r9
xor rdx, rdx
adox rbx, r11
adox rdi, rbp
mov rdx, [ rax + 0x8 ]
mulx r14, r8, [ rsi + 0x8 ]
adcx r15, r13
adcx r10, rcx
mov rdx, r12
mulx r13, r12, [ rsi + 0x8 ]
test al, al
adox r15, r12
adox r13, r10
mov rbp, rdx
mov rdx, [ rax + 0x0 ]
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, rcx, [ rax + 0x0 ]
adcx r15, rcx
adcx r10, r13
mov rdx, 0x7ffffffffffff 
mov r12, r15
and r12, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x0 ]
adox rbx, r11
adox r9, rdi
adcx rbx, r13
adcx rcx, r9
mov rdx, rbp
mulx rdi, rbp, [ rsi + 0x20 ]
add rbp, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx r13, r11, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r12
mulx r12, r9, [ rsi + 0x18 ]
test al, al
adox r11, r9
adox r12, r13
mov rdx, [ rax + 0x10 ]
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r8
mulx r8, r14, [ rax + 0x8 ]
adcx rbp, r14
adcx r8, rdi
shrd r15, r10, 51
add rbx, r15
adc rcx, 0x0
xor rdx, rdx
adox r11, r13
adox r9, r12
mov rdx, [ rax + 0x10 ]
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, rbx
shrd rdx, rcx, 51
mov r12, [ rsp - 0x8 ]
mov r13, r12
xor r14, r14
adox r13, [ rsp - 0x28 ]
mov r15, [ rsp - 0x10 ]
adox r15, [ rsp - 0x30 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, rcx, [ rsi + 0x8 ]
adcx rbp, rcx
adcx r14, r8
xor rdx, rdx
adox r13, r10
adox rdi, r15
adcx r13, r12
adc rdi, 0x0
mov rdx, [ rax + 0x20 ]
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r15, r12, [ rsi + 0x8 ]
mov rdx, r13
shrd rdx, rdi, 51
xor rcx, rcx
adox rbp, [ rsp - 0x38 ]
adox r14, [ rsp - 0x40 ]
adcx rbp, rdx
adc r14, 0x0
mov rdi, rbp
shrd rdi, r14, 51
mov rdx, 0x7ffffffffffff 
and r13, rdx
adox r11, r12
adox r15, r9
adcx r11, r8
adcx r10, r15
xor r9, r9
adox r11, rdi
adox r10, r9
mov rcx, r11
shrd rcx, r10, 51
lea r8, [rcx + 8 * rcx]
lea r12, [rcx + 2 * r8]
add r12, [ rsp - 0x18 ]
mov r8, r12
shr r8, 51
and r12, rdx
and rbx, rdx
lea r8, [ r8 + rbx ]
mov r14, r8
and r14, rdx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r14
and rbp, rdx
shr r8, 51
lea r8, [ r8 + r13 ]
mov [ rdi + 0x10 ], r8
mov [ rdi + 0x18 ], rbp
and r11, rdx
mov [ rdi + 0x0 ], r12
mov [ rdi + 0x20 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2414
; seed 3671615803566052 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1078372 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=217, initial num_batches=31): 87104 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08077361059077943
; number reverted permutation / tried permutation: 70053 / 89998 =77.838%
; number reverted decision / tried decision: 47114 / 90001 =52.348%
; validated in 0.408s
