SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, r11
mulx r8, r11, [ rsi + 0x18 ]
imul r9, [ rax + 0x18 ], 0x13
mov [ rsp - 0x80 ], rbx
imul rbx, [ rax + 0x8 ], 0x13
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x18 ]
imul rdx, [ rax + 0x20 ], 0x13
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r12
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
xor rdx, rdx
adox r14, rcx
adox r10, r15
mov rdx, rbp
mulx r15, rbp, [ rsi + 0x20 ]
mov rdx, r9
mulx rcx, r9, [ rsi + 0x18 ]
adcx rbp, r9
adcx rcx, r15
test al, al
adox rbp, rdi
adox r13, rcx
mulx r15, rdi, [ rsi + 0x20 ]
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r13
mulx r13, rcx, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, rbx, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r15
mulx r15, r9, r12
adcx rcx, r11
adcx r8, r13
xor rdx, rdx
adox rcx, rbx
adox rbp, r8
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rax + 0x0 ]
adcx rcx, r9
adcx r15, rbp
test al, al
adox rcx, r11
adox r13, r15
adcx r14, [ rsp - 0x30 ]
adcx r10, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rbx, r12
mov rdx, [ rax + 0x0 ]
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r11, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox rdi, rbx
adox r9, [ rsp - 0x18 ]
adcx rdi, rbp
adcx r11, r9
mov r15, r12
xor rbx, rbx
adox r15, [ rsp - 0x20 ]
adox r8, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, r12, [ rsi + 0x8 ]
adcx rdi, r12
adcx rbp, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x8 ]
xor rdx, rdx
adox r15, r9
adox r11, r8
mov rbx, rcx
shrd rbx, r13, 51
test al, al
adox r15, rbx
adox r11, rdx
mov r13, r15
shrd r13, r11, 51
mov rdx, [ rsi + 0x0 ]
mulx r12, r8, [ rax + 0x10 ]
xor rdx, rdx
adox rdi, r8
adox r12, rbp
adcx rdi, r13
adc r12, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r9, rbp, [ rax + 0x10 ]
mov rdx, rdi
shrd rdx, r12, 51
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mulx r13, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox r14, rbp
adox r9, r10
mov r10, 0x7ffffffffffff 
and rdi, r10
adox r14, r11
adox r13, r9
adcx r14, rbx
adc r13, 0x0
mov r8, r14
and r8, r10
mov rdx, [ rax + 0x0 ]
mulx rbp, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r11, rbx, [ rsi + 0x10 ]
shrd r14, r13, 51
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x8 ]
add r12, r9
adcx r13, rbp
xor rdx, rdx
adox r12, rbx
adox r11, r13
adcx r12, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
mov rdx, [ rax + 0x20 ]
mulx rbx, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, rbp
adox rbx, r11
adcx r12, r14
adc rbx, 0x0
and r15, r10
mov r14, r12
shrd r14, rbx, 51
imul r9, r14, 0x13
and rcx, r10
lea rcx, [ rcx + r9 ]
mov r13, rcx
shr r13, 51
lea r13, [ r13 + r15 ]
and r12, r10
mov r11, r13
and r11, r10
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r11
mov [ rbp + 0x20 ], r12
shr r13, 51
and rcx, r10
mov [ rbp + 0x18 ], r8
lea r13, [ r13 + rdi ]
mov [ rbp + 0x0 ], rcx
mov [ rbp + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.3148
; seed 0534936346471151 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1014074 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=231, initial num_batches=31): 76755 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.075689742563166
; number reverted permutation / tried permutation: 70179 / 89798 =78.152%
; number reverted decision / tried decision: 58137 / 90201 =64.453%
; validated in 0.464s
