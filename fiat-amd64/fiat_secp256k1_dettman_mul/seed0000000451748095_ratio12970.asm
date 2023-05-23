SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
xor rdx, rdx
adox rbp, r10
adox r11, r12
mov rdx, [ rax + 0x18 ]
mulx r12, r10, [ rsi + 0x8 ]
adcx rbp, rcx
adcx r8, r11
mov rdx, [ rax + 0x18 ]
mulx r11, rcx, [ rsi + 0x0 ]
add rbp, rcx
adcx r11, r8
mov rdx, [ rsi + 0x18 ]
mulx rcx, r8, [ rax + 0x8 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x68 ], r13
mov r13, r9
and r13, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, r13
adox rdi, rbp
adox r11, r12
mov rbp, rdi
shrd rbp, r11, 52
add r14, r8
adcx rcx, r15
mov rdx, [ rax + 0x10 ]
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, [ rax + 0x20 ]
test al, al
adox r14, r8
adox r13, rcx
adcx r14, r10
adcx r13, [ rsp - 0x48 ]
test al, al
adox r14, r15
adox r12, r13
adcx rbp, r14
adc r12, 0x0
shrd r9, rbx, 52
mov rdx, 0x1000003d10 
mulx r10, rbx, r9
add rbx, rbp
adcx r12, r10
mov r11, rbx
shrd r11, r12, 52
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mulx rbp, r14, [ rsi + 0x20 ]
test al, al
adox r14, rcx
adox r8, rbp
mov rdx, [ rax + 0x18 ]
mulx r10, r9, [ rsi + 0x10 ]
adcx r14, r9
adcx r10, r8
add r14, r15
adcx r13, r10
mov rdx, [ rax + 0x18 ]
mulx rcx, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox r11, r14
adox r13, rdx
mov r15, 0xfffffffffffff 
mov rbp, r11
and rbp, r15
mov rdx, [ rax + 0x10 ]
mulx r9, r8, [ rsi + 0x20 ]
shl rbp, 4
and rbx, r15
adox r8, r12
adox rcx, r9
mov rdx, 0xffffffffffff 
mov r10, rbx
and r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, [ rax + 0x20 ]
shr rbx, 48
lea rbp, [ rbp + rbx ]
mov rdx, 0x1000003d1 
mulx rbx, r9, rbp
mov rdx, [ rax + 0x8 ]
mulx r15, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r15
mulx r15, r10, [ rax + 0x0 ]
shrd r11, r13, 52
test al, al
adox r8, r14
adox r12, rcx
adcx r11, r8
adc r12, 0x0
mov rdx, r11
shrd rdx, r12, 52
add r9, r10
adcx r15, rbx
mov r13, r9
shrd r13, r15, 52
mov rcx, 0xfffffffffffff 
and r11, rcx
mov r14, rdx
mov rdx, [ rax + 0x18 ]
mulx r10, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r12, r8, [ rax + 0x20 ]
adox rbx, r8
adox r12, r10
adcx r14, rbx
adc r12, 0x0
mov rdx, [ rsi + 0x8 ]
mulx r10, r15, [ rax + 0x0 ]
mov rdx, 0x1000003d10 
mulx rbx, r8, r11
mov r11, r14
shrd r11, r12, 52
xor r12, r12
adox r15, rbp
adox r10, [ rsp - 0x38 ]
adcx r13, r15
adc r10, 0x0
add r8, r13
adcx r10, rbx
mov rdx, [ rax + 0x0 ]
mulx rbx, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx rcx, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r15
adox r13, rbx
mov rbx, r8
shrd rbx, r10, 52
test al, al
adox rbp, r12
adox rcx, r13
adcx rbx, rbp
adc rcx, 0x0
mov r10, 0xfffffffffffff 
and r14, r10
mov r15, 0x1000003d10 
mov rdx, r15
mulx r12, r15, r14
adox r15, rbx
adox rcx, r12
mov r13, r15
shrd r13, rcx, 52
and r15, r10
and rdi, r10
lea rdi, [ rdi + r13 ]
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x10 ], r15
mulx r14, rbx, r11
adox rbx, rdi
mov r11, 0x0 
adox r14, r11
mov r12, rbx
shrd r12, r14, 52
add r12, [ rsp - 0x40 ]
and r9, r10
mov [ rbp + 0x0 ], r9
and r8, r10
and rbx, r10
mov [ rbp + 0x8 ], r8
mov [ rbp + 0x20 ], r12
mov [ rbp + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2970
; seed 1264522544272874 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 837498 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=325, initial num_batches=31): 80113 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0956575418687567
; number reverted permutation / tried permutation: 73615 / 89948 =81.842%
; number reverted decision / tried decision: 53670 / 90051 =59.600%
; validated in 0.248s
