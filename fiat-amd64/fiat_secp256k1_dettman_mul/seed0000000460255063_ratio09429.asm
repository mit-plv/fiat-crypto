SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, 0x34 
mov [ rsp - 0x58 ], r15
bzhi r15, r10, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r8
mulx r8, r9, r15
adox rbp, r13
adox r14, r12
mov rdx, [ rsi + 0x0 ]
mulx r13, r12, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r13
mulx r13, r15, [ rax + 0x18 ]
test al, al
adox rbp, rdi
adox rbx, r14
adcx rbp, r15
adcx r13, rbx
mov rdx, [ rax + 0x8 ]
mulx r14, rdi, [ rsi + 0x18 ]
test al, al
adox r9, rbp
adox r13, r8
mov rdx, [ rax + 0x0 ]
mulx r15, r8, [ rsi + 0x20 ]
adcx r8, rdi
adcx r14, r15
mov rdx, r9
shrd rdx, r13, 52
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbp, [ rax + 0x18 ]
xor rdx, rdx
adox r8, rcx
adox r14, [ rsp - 0x38 ]
adcx r8, rbp
adcx rdi, r14
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ rax + 0x20 ]
xor rdx, rdx
adox r8, rcx
adox r13, rdi
adcx rbx, r8
adc r13, 0x0
shrd r10, r11, 52
mov r11, 0x1000003d10 
mov rdx, r10
mulx r15, r10, r11
mov rdx, [ rax + 0x8 ]
mulx r14, rbp, [ rsi + 0x8 ]
test al, al
adox r10, rbx
adox r13, r15
mov rdx, [ rsi + 0x18 ]
mulx rcx, rdi, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r11, r15, [ rax + 0x8 ]
adcx r15, rdi
adcx rcx, r11
mov rdx, [ rax + 0x18 ]
mulx r11, rdi, [ rsi + 0x10 ]
mov rdx, r10
shrd rdx, r13, 52
add r15, rdi
adcx r11, rcx
mov r13, rdx
mov rdx, [ rax + 0x20 ]
mulx rdi, rcx, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, rcx
adox rdi, r11
adcx r13, r15
adc rdi, 0x0
add r8, rbp
adcx r14, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, rbp, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, r11, [ rsi + 0x18 ]
xor rdx, rdx
adox r8, r12
adox r14, [ rsp - 0x30 ]
mov r12, 0xfffffffffffff 
and r10, r12
mov r15, r13
and r15, r12
shl r15, 4
mov rdx, 0xffffffffffff 
mov r12, r10
and r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r14
mulx r14, r12, [ rax + 0x10 ]
shr r10, 48
add rbp, [ rsp - 0x40 ]
adcx rbx, [ rsp - 0x48 ]
lea r15, [ r15 + r10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r8
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, 0x1000003d1 
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], rbp
mulx rbp, rbx, r15
test al, al
adox r12, r11
adox rcx, r14
mov rdx, [ rax + 0x0 ]
mulx r14, r11, [ rsi + 0x0 ]
adcx rbx, r11
adcx r14, rbp
shrd r13, rdi, 52
test al, al
adox r12, r10
adox r8, rcx
mov rdx, rbx
shrd rdx, r14, 52
test al, al
adox r13, r12
mov rdi, 0x0 
adox r8, rdi
mov r15, r13
shrd r15, r8, 52
add r15, [ rsp - 0x8 ]
mov r10, [ rsp - 0x10 ]
adc r10, 0x0
mov rbp, r15
shrd rbp, r10, 52
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, [ rax + 0x8 ]
mov rdx, 0x1000003d10 
mulx rdi, r10, rbp
mov rbp, 0xfffffffffffff 
and r13, rbp
adox r11, r12
adox r8, r14
adcx rcx, r11
adc r8, 0x0
and rbx, rbp
mulx r12, r14, r13
adox r14, rcx
adox r8, r12
mov r13, r14
and r13, rbp
shrd r14, r8, 52
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], rbx
and r15, rbp
adox r14, [ rsp - 0x18 ]
mov rcx, [ rsp - 0x20 ]
mov rbx, 0x0 
adox rcx, rbx
mulx r8, r12, r15
adcx r12, r14
adcx rcx, r8
and r9, rbp
mov r15, r12
shrd r15, rcx, 52
lea r9, [ r9 + r15 ]
and r12, rbp
adox r10, r9
adox rdi, rbx
mov r14, r10
shrd r14, rdi, 52
and r10, rbp
add r14, [ rsp - 0x28 ]
mov [ r11 + 0x20 ], r14
mov [ r11 + 0x18 ], r10
mov [ r11 + 0x8 ], r13
mov [ r11 + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9429
; seed 1630032793123719 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2247943 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 129805 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.057743901869397936
; number reverted permutation / tried permutation: 69392 / 90292 =76.853%
; number reverted decision / tried decision: 31909 / 89707 =35.570%
; validated in 0.511s
