SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
imul rax, [ rdx + 0x20 ], 0x13
imul r10, [ rdx + 0x10 ], 0x13
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, r10
mov rdx, [ rcx + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
imul rdx, [ rcx + 0x8 ], 0x13
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r10
test al, al
adox r12, r14
adox r15, r13
mov rdx, r11
mulx r10, r11, [ rsi + 0x10 ]
adcx r12, r11
adcx r10, r15
mulx r14, r13, [ rsi + 0x18 ]
mulx r11, r15, [ rsi + 0x20 ]
test al, al
adox r8, r13
adox r14, r9
mov rdx, [ rcx + 0x0 ]
mulx r13, r9, [ rsi + 0x0 ]
mov rdx, rax
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, [ rsi + 0x8 ]
adcx r12, rax
adcx rdi, r10
mulx rax, r10, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r11
xor r11, r11
adox r12, r9
adox r13, rdi
adcx r8, r10
adcx rax, r14
mulx r9, r14, [ rsi + 0x18 ]
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rcx + 0x0 ]
xor rdx, rdx
adox r8, r10
adox r11, rax
adcx r8, rbx
adcx rbp, r11
mov rbx, r12
shrd rbx, r13, 51
xor r13, r13
adox r8, rbx
adox rbp, r13
adcx r15, r14
adcx r9, [ rsp - 0x48 ]
mov rdx, r8
shrd rdx, rbp, 51
mov rax, rdx
mov rdx, [ rcx + 0x0 ]
mulx r10, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx rbx, r11, [ rcx + 0x8 ]
xor rdx, rdx
adox r15, r14
adox r10, r9
mov rdx, [ rcx + 0x8 ]
mulx rbp, r13, [ rsi + 0x8 ]
adcx r15, r13
adcx rbp, r10
mov rdx, [ rsi + 0x20 ]
mulx r14, r9, [ rcx + 0x0 ]
mov rdx, [ rcx + 0x10 ]
mulx r13, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r11
adox rbx, r14
adcx r15, r10
adcx r13, rbp
xor r11, r11
adox r15, rax
adox r13, r11
mov rdx, [ rcx + 0x18 ]
mulx rbp, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, r14, [ rcx + 0x10 ]
adcx r9, r14
adcx r10, rbx
mov rdx, [ rsi + 0x8 ]
mulx r14, rbx, [ rcx + 0x10 ]
xor rdx, rdx
adox r9, rax
adox rbp, r10
mov rdx, [ rcx + 0x0 ]
mulx rax, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbp
mulx rbp, r10, rdi
adcx r10, r11
adcx rax, rbp
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, [ rcx + 0x8 ]
add r10, rdi
adcx r11, rax
mov rdx, r15
shrd rdx, r13, 51
mov r13, 0x7ffffffffffff 
and r8, r13
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, [ rcx + 0x18 ]
and r12, r13
adox r10, rbx
adox r14, r11
adcx r10, rax
adcx rdi, r14
xor rdx, rdx
adox r10, rbp
adox rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, [ rcx + 0x20 ]
mov rdx, r10
shrd rdx, rdi, 51
and r10, r13
adox r9, rbx
adox r11, [ rsp - 0x40 ]
adcx r9, rdx
adc r11, 0x0
mov rbp, r9
shrd rbp, r11, 51
imul rax, rbp, 0x13
lea r12, [ r12 + rax ]
mov r14, r12
shr r14, 51
lea r14, [ r14 + r8 ]
mov r8, r14
and r8, r13
shr r14, 51
and r15, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r8
lea r14, [ r14 + r15 ]
mov [ rdi + 0x10 ], r14
and r12, r13
and r9, r13
mov [ rdi + 0x18 ], r10
mov [ rdi + 0x0 ], r12
mov [ rdi + 0x20 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2717
; seed 1768025985360423 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 777018 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=342, initial num_batches=31): 78833 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10145582213024666
; number reverted permutation / tried permutation: 74951 / 89760 =83.502%
; number reverted decision / tried decision: 61046 / 90239 =67.649%
; validated in 0.288s
