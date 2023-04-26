SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x0 ]
mov rdx, r11
shl rdx, 0x1
mulx rcx, r11, [ rsi + 0x18 ]
mov r8, rax
shrd r8, r10, 52
mov r9, [ rsi + 0x8 ]
mov r10, r9
shl r10, 0x1
mov r9, 0xfffffffffffff 
and rax, r9
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r10
adox rbp, r11
adox rcx, r12
mov rdx, 0x1000003d10 
mulx r12, r11, rax
adcx r11, rbp
adcx rcx, r12
mov rax, r11
and rax, r9
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, rdx
mov rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, r10, [ rsi + 0x18 ]
shrd r11, rcx, 52
xor rcx, rcx
adox rbp, r10
adox r13, r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r10, rbx
adcx rbp, r10
adcx rcx, r13
mov rdx, 0x1000003d10 
mulx r10, r13, r8
xor r8, r8
adox r11, rbp
adox rcx, r8
adcx r13, r11
adcx rcx, r10
mov rbp, r13
shrd rbp, rcx, 52
mov r10, [ rsi + 0x10 ]
mov r11, r10
shl r11, 0x1
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, r11
mov rdx, r12
mulx r8, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox r10, r12
adox r8, rcx
adcx rbp, r10
adc r8, 0x0
and r13, r9
mov rcx, rbp
shrd rcx, r8, 52
mov r12, r13
shr r12, 48
and rbp, r9
shl rbp, 4
lea rbp, [ rbp + r12 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r10, rdx
mov rdx, r11
mulx r12, r11, [ rsi + 0x20 ]
mov rdx, 0x1000003d1 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
add r10, r11
adcx r12, r8
add rcx, r10
adc r12, 0x0
mov rbp, [ rsi + 0x18 ]
mov r8, rbp
shl r8, 0x1
mov rdx, [ rsi + 0x20 ]
mulx r11, rbp, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, rdx
mov rdx, rcx
and rdx, r9
shrd rcx, r12, 52
test al, al
adox r14, r10
adox r8, r15
adcx rcx, rbp
adc r11, 0x0
mov r15, r14
shrd r15, r8, 52
mov r12, rcx
shrd r12, r11, 52
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, rbx
add r15, r10
adc r8, 0x0
and r14, r9
mov rdx, 0x1000003d10 
mulx r10, r11, rbp
adox r11, r15
adox r8, r10
mov rbp, r11
shrd rbp, r8, 52
and r11, r9
mov rdx, rbx
mulx r15, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, rdx
adox r10, rbx
adox r15, r8
mov [ rdi + 0x0 ], r14
adcx rbp, r10
adc r15, 0x0
and rcx, r9
mov rdx, 0x1000003d10 
mulx rbx, r14, rcx
adox r14, rbp
adox r15, rbx
mov r8, r14
shrd r8, r15, 52
mulx rbp, r10, r12
and r14, r9
mov [ rdi + 0x10 ], r14
lea rax, [ rax + r8 ]
adox r10, rax
mov r12, 0x0 
adox rbp, r12
mov rcx, r10
shrd rcx, rbp, 52
and r10, r9
mov [ rdi + 0x18 ], r10
mov rbx, 0xffffffffffff 
and r13, rbx
lea r13, [ r13 + rcx ]
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x20 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2114
; seed 0062082873495733 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 662823 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=367, initial num_batches=31): 76150 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11488738320788507
; number reverted permutation / tried permutation: 78345 / 90284 =86.776%
; number reverted decision / tried decision: 69422 / 89715 =77.381%
; validated in 0.187s
