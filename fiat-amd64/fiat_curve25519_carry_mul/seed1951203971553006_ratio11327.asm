SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
lea r8, [rdx + 8 * rdx]
lea r9, [rdx + 2 * r8]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, r11
mov [ rsp - 0x68 ], r13
mulx r13, r11, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
lea r15, [r14 + 8 * r14]
lea rdi, [r14 + 2 * r15]
xchg rdx, rdi
mulx r15, r14, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], r15
mulx r15, r8, [ rsi + 0x18 ]
mov rdx, rbx
mov [ rsp - 0x30 ], r14
mulx r14, rbx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r11
mov [ rsp - 0x18 ], r9
mulx r9, r11, [ rax + 0x8 ]
test al, al
adox rbx, r8
adox r15, r14
mov rdx, [ rax + 0x8 ]
mulx r14, r8, [ rsi + 0x18 ]
adcx r10, r8
adcx r14, rcx
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
test al, al
adox r10, rcx
adox r8, r14
adcx rbx, r11
adcx r9, r15
mov rdx, [ rax + 0x18 ]
mulx r15, r11, [ rsi + 0x8 ]
add rbx, rbp
adcx r12, r9
mov rdx, [ rax + 0x18 ]
lea rbp, [rdx + 8 * rdx]
lea r14, [rdx + 2 * rbp]
mov rdx, [ rax + 0x0 ]
mulx rcx, rbp, [ rsi + 0x0 ]
test al, al
adox r10, r11
adox r15, r8
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, [ rsp - 0x18 ]
adcx r8, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mulx r15, r11, r14
test al, al
adox r8, r11
adox r15, r9
mov rdx, [ rsi + 0x8 ]
mulx r11, r9, r13
adcx r8, r9
adcx r11, r15
test al, al
adox r8, rbp
adox rcx, r11
mov rdx, [ rax + 0x8 ]
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r9, r14
mov rdx, rdi
mov [ rsp - 0x8 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
adcx rdi, r9
adcx r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, r9, [ rax + 0x0 ]
xor rdx, rdx
adox rdi, [ rsp - 0x30 ]
adox r11, [ rsp - 0x38 ]
adcx rdi, r9
adcx r10, r11
xor r9, r9
adox rdi, rbp
adox r15, r10
mov rdx, [ rax + 0x18 ]
mulx r11, rbp, [ rsi + 0x0 ]
mov rdx, r8
shrd rdx, rcx, 51
xchg rdx, r13
mulx r10, rcx, [ rsi + 0x18 ]
test al, al
adox rbx, rbp
adox r11, r12
mov rdx, [ rsi + 0x20 ]
mulx rbp, r12, r14
adcx rdi, r13
adc r15, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r12, rcx
adox r10, rbp
adcx r12, r14
adcx r13, r10
mov rdx, [ rsi + 0x0 ]
mulx rcx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r14, rbp, [ rsi + 0x8 ]
xor rdx, rdx
adox r12, rbp
adox r14, r13
adcx r12, r9
adcx rcx, r14
mov r10, rdi
shrd r10, r15, 51
mov r15, 0x7ffffffffffff 
and rdi, r15
adox r12, r10
adox rcx, rdx
mov r13, r12
and r13, r15
mov r9, [ rsp - 0x8 ]
adox r9, [ rsp - 0x40 ]
mov rbp, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x48 ]
shrd r12, rcx, 51
xor r14, r14
adox rbx, r12
adox r11, r14
mov rdx, rbx
shrd rdx, r11, 51
xor r10, r10
adox r9, rdx
adox rbp, r10
mov r14, r9
and r14, r15
shrd r9, rbp, 51
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x20 ], r14
imul r12, r9, 0x13
and r8, r15
lea r8, [ r8 + r12 ]
and rbx, r15
mov r11, r8
shr r11, 51
lea r11, [ r11 + rdi ]
mov [ rcx + 0x18 ], rbx
mov rdi, r11
shr rdi, 51
and r11, r15
mov [ rcx + 0x8 ], r11
and r8, r15
lea rdi, [ rdi + r13 ]
mov [ rcx + 0x0 ], r8
mov [ rcx + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1327
; seed 1951203971553006 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4980 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=200, initial num_batches=31): 364 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07309236947791165
; number reverted permutation / tried permutation: 358 / 516 =69.380%
; number reverted decision / tried decision: 285 / 483 =59.006%
; validated in 0.312s
