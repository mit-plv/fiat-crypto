SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, r11, 52
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x18 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r15
mulx r15, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r11
mulx r11, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r15, rbp
adox r12, r11
mov rdx, [ rax + 0x8 ]
mulx r11, rbp, [ rsi + 0x10 ]
adcx rcx, rbp
adcx r11, r8
mov rdx, [ rax + 0x10 ]
mulx rbp, r8, [ rsi + 0x20 ]
xor rdx, rdx
adox r8, r14
adox r13, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r14, [ rax + 0x10 ]
adcx rcx, r14
adcx rbp, r11
mov rdx, [ rax + 0x18 ]
mulx r14, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r8
mulx r8, r13, [ rax + 0x8 ]
test al, al
adox rcx, r11
adox r14, rbp
mov rdx, 0xfffffffffffff 
and r10, rdx
mov rdx, [ rax + 0x18 ]
mulx r11, rbp, [ rsi + 0x10 ]
mov rdx, 0x1000003d10 
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r12
mulx r12, rdi, r10
adox rdi, rcx
adox r14, r12
adcx r9, r13
adcx r8, rbx
add r15, rbp
adcx r11, [ rsp + 0x8 ]
mov rbx, rdi
shrd rbx, r14, 52
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx rbp, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, [ rax + 0x10 ]
mov rdx, r13
test al, al
adox rdx, [ rsp - 0x30 ]
adox rcx, [ rsp - 0x38 ]
mov r13, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x10 ], r11
mov [ rsp + 0x18 ], r15
mulx r15, r11, [ rsi + 0x8 ]
adcx r13, r12
adcx r14, rcx
test al, al
adox r13, r11
adox r15, r14
adcx r9, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r12, [ rax + 0x20 ]
xor rdx, rdx
adox r13, r10
adox rbp, r15
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x20 ]
adcx rbx, r13
adc rbp, 0x0
mov rdx, rbx
test al, al
adox rdx, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x28 ]
mov r14, rdx
shrd r14, rbp, 52
mov r15, rdx
mov rdx, [ rax + 0x20 ]
mulx rbx, r13, [ rsi + 0x10 ]
mov rdx, 0xfffffffffffff 
and r15, rdx
mov rbp, r10
adox rbp, [ rsp + 0x18 ]
adox r11, [ rsp + 0x10 ]
adcx r14, rbp
adc r11, 0x0
mov r10, r14
shrd r10, r11, 52
mov rdx, [ rax + 0x18 ]
mulx r11, rbp, [ rsi + 0x20 ]
mov rdx, 0x34 
mov [ rsp + 0x20 ], r8
bzhi r8, r14, rdx
adox rbp, r12
adox rcx, r11
mov r12, r13
test al, al
adox r12, [ rsp - 0x8 ]
adox rbx, [ rsp - 0x10 ]
adcx r10, r12
adc rbx, 0x0
mov r13, r10
shrd r13, rbx, 52
xor r14, r14
adox r13, rbp
adox rcx, r14
bzhi r11, r10, rdx
mov rbp, 0x1000003d10 
mov rdx, r11
mulx r12, r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, r15
shr rdx, 48
mov r14, 0x30 
bzhi rbp, r15, r14
mov r15, r13
shrd r15, rcx, 52
shl r8, 4
lea r8, [ r8 + rdx ]
mov rdx, [ rsi + 0x0 ]
mulx r14, rcx, [ rax + 0x0 ]
mov rdx, 0x1000003d1 
mov [ rsp + 0x28 ], rbp
mov [ rsp + 0x30 ], r9
mulx r9, rbp, r8
xor r8, r8
adox rbp, rcx
adox r14, r9
mov rcx, rbp
shrd rcx, r14, 52
mov r9, r10
test al, al
adox r9, [ rsp - 0x18 ]
adox rbx, [ rsp - 0x20 ]
mov r10, 0xfffffffffffff 
and rbp, r10
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x0 ], rbp
adox rcx, r9
adox rbx, r8
adcx r11, rcx
adcx rbx, r12
mov r12, r11
and r12, r10
shrd r11, rbx, 52
mov r9, 0x1000003d10 
mov rdx, r15
mulx rbp, r15, r9
and r13, r10
mov rdx, r9
mulx rcx, r9, r13
adox r11, [ rsp + 0x30 ]
mov rbx, [ rsp + 0x20 ]
adox rbx, r8
mov [ r14 + 0x8 ], r12
adcx r9, r11
adcx rbx, rcx
mov r12, r9
and r12, r10
mov [ r14 + 0x10 ], r12
and rdi, r10
shrd r9, rbx, 52
lea rdi, [ rdi + r9 ]
add r15, rdi
adc rbp, 0x0
mov r13, r15
shrd r13, rbp, 52
add r13, [ rsp + 0x28 ]
mov [ r14 + 0x20 ], r13
and r15, r10
mov [ r14 + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 0.9830
; seed 3305037213716836 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8716 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=206, initial num_batches=31): 564 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06470858191831115
; number reverted permutation / tried permutation: 328 / 491 =66.802%
; number reverted decision / tried decision: 207 / 508 =40.748%
; validated in 0.458s
