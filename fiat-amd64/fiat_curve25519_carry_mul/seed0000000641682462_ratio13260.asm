SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x8 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx rcx, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
lea r8, [rdx + 8 * rdx]
lea r9, [rdx + 2 * r8]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
mov rdx, r11
mulx r13, r11, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
imul rdx, [ rax + 0x18 ], 0x13
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r10
mulx r10, rcx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rdi
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r10
mulx r10, r15, [ rax + 0x0 ]
add r11, r8
adcx rbx, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r8, rdi
test al, al
adox r11, r8
adox r13, rbx
adcx r15, rbp
adcx r12, r10
mov rdx, [ rax + 0x10 ]
mulx r10, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox r15, rbp
adox r10, r12
mov rdx, [ rax + 0x0 ]
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, r14
mulx r12, r14, [ rsi + 0x8 ]
adcx r11, r14
adcx r12, r13
xor r13, r13
adox r11, rbx
adox r8, r12
xchg rdx, r9
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r14, rdi
adcx rbp, r14
adcx r12, rbx
mov rdx, r9
mulx rdi, r9, [ rsi + 0x10 ]
mov rbx, r11
shrd rbx, r8, 51
xor r8, r8
adox rbp, r9
adox rdi, r12
mov r13, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r15
mulx r15, r10, [ rsi + 0x10 ]
adcx rbp, r14
adcx r12, rdi
mov rdx, [ rsi + 0x18 ]
mulx r14, rdi, r13
test al, al
adox rcx, rdi
adox r14, [ rsp - 0x28 ]
adcx rbp, r9
adcx r8, r12
mov rdx, [ rax + 0x8 ]
mulx r12, r9, [ rsi + 0x8 ]
test al, al
adox rcx, r10
adox r15, r14
mov rdx, r13
mulx r10, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x10 ]
adcx rcx, r9
adcx r12, r15
xor rdx, rdx
adox r13, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx r15, r9, [ rax + 0x8 ]
adcx rbp, rbx
adc r8, 0x0
mov rdx, 0x7ffffffffffff 
mov rbx, rbp
and rbx, rdx
shrd rbp, r8, 51
xor r8, r8
adox rcx, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
adcx rcx, rbp
adc r12, 0x0
mov rdx, [ rax + 0x18 ]
mulx r8, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, r9
adox r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rax + 0x18 ]
adcx r13, rdi
adcx r14, r15
mov rdx, rcx
shrd rdx, r12, 51
test al, al
adox r13, rbp
adox r8, r14
adcx r13, rdx
adc r8, 0x0
mov rdi, 0x7ffffffffffff 
mov r12, r13
and r12, rdi
mov rdx, [ rax + 0x20 ]
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, r10
adox rdx, [ rsp - 0x18 ]
adox r9, [ rsp - 0x20 ]
adcx rdx, rbp
adcx r15, r9
shrd r13, r8, 51
add rdx, r13
adc r15, 0x0
mov r10, rdx
shrd r10, r15, 51
and r11, rdi
imul r14, r10, 0x13
lea r11, [ r11 + r14 ]
mov r8, r11
shr r8, 51
lea r8, [ r8 + rbx ]
mov rbx, r8
shr rbx, 51
and rdx, rdi
and r8, rdi
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x20 ], rdx
and r11, rdi
mov [ rbp + 0x8 ], r8
and rcx, rdi
lea rbx, [ rbx + rcx ]
mov [ rbp + 0x18 ], r12
mov [ rbp + 0x0 ], r11
mov [ rbp + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3260
; seed 4058600602015691 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1085534 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=213, initial num_batches=31): 86006 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07922920885020644
; number reverted permutation / tried permutation: 70525 / 89823 =78.516%
; number reverted decision / tried decision: 47157 / 90176 =52.294%
; validated in 0.388s
