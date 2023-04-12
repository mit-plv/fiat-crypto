SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, r11
imul rdx, [ rax + 0x8 ], 0x13
mulx r9, r8, [ rsi + 0x20 ]
imul rdx, [ rax + 0x10 ], 0x13
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
test al, al
adox r8, rbx
adox rbp, r9
adcx r8, r10
adcx rcx, rbp
mov rdx, [ rsi + 0x18 ]
mulx r9, r10, r11
mov rdx, [ rax + 0x20 ]
lea rbx, [rdx + 8 * rdx]
lea rbp, [rdx + 2 * rbx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbx, rbp
xor rdx, rdx
adox r12, r10
adox r9, r13
mov rdx, rbp
mulx r13, rbp, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, [ rsi + 0x20 ]
adcx r8, rbp
adcx r13, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, [ rax + 0x0 ]
xor rdx, rdx
adox r8, rbp
adox rdi, r13
mov r13, r8
shrd r13, rdi, 51
test al, al
adox r12, rbx
adox r14, r9
mov rdx, [ rax + 0x0 ]
mulx r9, rbx, [ rsi + 0x8 ]
adcx r12, rbx
adcx r9, r14
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rax + 0x8 ]
xor rdx, rdx
adox r12, rbp
adox rdi, r9
mov rdx, rcx
mulx r14, rcx, [ rsi + 0x18 ]
mov rdx, r11
mulx rbx, r11, [ rsi + 0x20 ]
adcx r12, r13
adc rdi, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r9, r13, [ rax + 0x0 ]
test al, al
adox r11, rcx
adox r14, rbx
adcx r11, r13
adcx r9, r14
mov rdx, [ rax + 0x8 ]
mulx rcx, rbp, [ rsi + 0x8 ]
mov rdx, r12
shrd rdx, rdi, 51
test al, al
adox r11, rbp
adox rcx, r9
mov rbx, 0x7ffffffffffff 
and r12, rbx
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r13, [ rax + 0x10 ]
adox r11, r13
adox r14, rcx
adcx r11, rdi
adc r14, 0x0
mov rdx, [ rax + 0x0 ]
mulx rbp, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, rdi, [ rax + 0x10 ]
add r10, r9
adcx rbp, r15
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ rax + 0x8 ]
add r10, r15
adcx r13, rbp
add r10, rdi
adcx rcx, r13
mov rdx, [ rax + 0x8 ]
mulx rdi, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rbp, [ rsi + 0x20 ]
xor rdx, rdx
adox rbp, r9
adox rdi, r15
mov r13, r11
shrd r13, r14, 51
mov rdx, [ rax + 0x18 ]
mulx r9, r14, [ rsi + 0x0 ]
add r10, r14
adcx r9, rcx
xor rdx, rdx
adox r10, r13
adox r9, rdx
mov rdx, [ rax + 0x20 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, r9, 51
mov r13, rdx
mov rdx, [ rax + 0x10 ]
mulx r9, r14, [ rsi + 0x10 ]
add rbp, r14
adcx r9, rdi
mov rdx, [ rax + 0x18 ]
mulx r14, rdi, [ rsi + 0x8 ]
add rbp, rdi
adcx r14, r9
xor rdx, rdx
adox rbp, rcx
adox r15, r14
adcx rbp, r13
adc r15, 0x0
mov rcx, rbp
shrd rcx, r15, 51
and rbp, rbx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x20 ], rbp
imul r9, rcx, 0x13
and r8, rbx
lea r8, [ r8 + r9 ]
mov rdi, r8
shr rdi, 51
and r8, rbx
lea rdi, [ rdi + r12 ]
mov r12, rdi
shr r12, 51
and rdi, rbx
mov [ r13 + 0x0 ], r8
mov [ r13 + 0x8 ], rdi
and r11, rbx
lea r12, [ r12 + r11 ]
and r10, rbx
mov [ r13 + 0x18 ], r10
mov [ r13 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3076
; seed 3621371419544221 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 744949 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=337, initial num_batches=31): 77805 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10444339142679566
; number reverted permutation / tried permutation: 74820 / 90393 =82.772%
; number reverted decision / tried decision: 61369 / 89606 =68.488%
; validated in 0.285s
