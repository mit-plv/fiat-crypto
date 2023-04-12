SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, r11
mov rdx, [ rax + 0x18 ]
lea r8, [rdx + 8 * rdx]
lea r9, [rdx + 2 * r8]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, r9
imul rdx, [ rax + 0x10 ], 0x13
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
imul rdx, [ rax + 0x8 ], 0x13
mov [ rsp - 0x58 ], r15
xor r15, r15
adox r13, r8
adox rbx, r14
adcx r13, r10
adcx rcx, rbx
mulx r8, r10, [ rsi + 0x20 ]
xor r14, r14
adox r10, rbp
adox r12, r8
mov rdx, [ rax + 0x0 ]
mulx rbp, r15, [ rsi + 0x8 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x10 ]
adcx r10, r9
adcx rbx, r12
xor r8, r8
adox r13, r15
adox rbp, rcx
mov r14, rdx
mov rdx, [ rax + 0x0 ]
mulx r12, rcx, [ rsi + 0x0 ]
mov rdx, r11
mulx r15, r11, [ rsi + 0x8 ]
adcx r10, r11
adcx r15, rbx
xor r9, r9
adox r10, rcx
adox r12, r15
mulx rbx, r8, [ rsi + 0x18 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r11, [ rax + 0x8 ]
adcx r13, r11
adcx r15, rbp
mov rdx, [ rsi + 0x20 ]
mulx r11, rbp, r14
test al, al
adox rbp, r8
adox rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ rax + 0x0 ]
adcx rbp, r14
adcx r8, rbx
mov rdx, r10
shrd rdx, r12, 51
xor r12, r12
adox r13, rdx
adox r15, r12
mov r9, r13
shrd r9, r15, 51
mov rdx, [ rax + 0x8 ]
mulx rbx, r11, [ rsi + 0x8 ]
add rbp, r11
adcx rbx, r8
mov rdx, [ rax + 0x10 ]
mulx r8, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r14
adox r8, rbx
adcx rbp, r9
adc r8, 0x0
mov rdx, rcx
mulx r12, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r15, [ rax + 0x0 ]
xor rdx, rdx
adox rcx, r15
adox r9, r12
mov rdx, [ rsi + 0x10 ]
mulx rbx, r11, [ rax + 0x8 ]
adcx rcx, r11
adcx rbx, r9
mov rdx, [ rsi + 0x8 ]
mulx r12, r14, [ rax + 0x10 ]
xor rdx, rdx
adox rcx, r14
adox r12, rbx
mov r15, rbp
shrd r15, r8, 51
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x18 ]
xor rdx, rdx
adox rcx, r8
adox r9, r12
mov rdx, [ rax + 0x0 ]
mulx rbx, r11, [ rsi + 0x20 ]
adcx rcx, r15
adc r9, 0x0
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rax + 0x20 ]
xor rdx, rdx
adox r11, r14
adox r12, rbx
mov rdx, [ rax + 0x10 ]
mulx r14, rbx, [ rsi + 0x10 ]
adcx r11, rbx
adcx r14, r12
mov rdx, [ rax + 0x18 ]
mulx rbx, r12, [ rsi + 0x8 ]
xor rdx, rdx
adox r11, r12
adox rbx, r14
adcx r11, r15
adcx r8, rbx
mov r15, rcx
shrd r15, r9, 51
add r11, r15
adc r8, 0x0
mov r9, r11
shrd r9, r8, 51
imul r14, r9, 0x13
mov r12, 0x7ffffffffffff 
and r10, r12
lea r10, [ r10 + r14 ]
and r13, r12
mov rbx, r10
and rbx, r12
mov [ rdi + 0x0 ], rbx
shr r10, 51
and r11, r12
lea r10, [ r10 + r13 ]
mov [ rdi + 0x20 ], r11
mov r15, r10
and r15, r12
and rbp, r12
mov [ rdi + 0x8 ], r15
shr r10, 51
and rcx, r12
lea r10, [ r10 + rbp ]
mov [ rdi + 0x10 ], r10
mov [ rdi + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3008
; seed 2818044794215046 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 749803 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=337, initial num_batches=31): 78374 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10452612219476316
; number reverted permutation / tried permutation: 73763 / 89838 =82.107%
; number reverted decision / tried decision: 61572 / 90161 =68.291%
; validated in 0.289s
