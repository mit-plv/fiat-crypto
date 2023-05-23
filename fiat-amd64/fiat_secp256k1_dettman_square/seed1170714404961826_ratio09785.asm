SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov r11, 0x1 
shlx rdx, [ rsi + 0x8 ], r11
mulx r8, rcx, [ rsi + 0x10 ]
mov r9, [ rsi + 0x10 ]
mov r11, r9
shl r11, 0x1
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, r11
mov [ rsp - 0x70 ], r12
mulx r12, r11, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov r13, rbx
shrd r13, rbp, 52
mov rbp, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, rbp
shl r14, 0x1
mov rbp, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
lea r15, [rbp + rbp]
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rdi
mulx rdi, r14, r9
xor rdx, rdx
adox rax, r14
adox rdi, r10
mov rdx, [ rsi + 0x20 ]
mulx r14, r10, r15
mov rdx, 0x1000003d10 
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], r11
mulx r11, r12, r13
adcx rax, r10
adcx r14, rdi
mov rdx, r15
mulx r13, r15, [ rsi + 0x18 ]
mov rdi, 0xfffffffffffff 
and rbx, rdi
mov r10, 0x1000003d10 
xchg rdx, rbx
mov [ rsp - 0x20 ], r11
mulx r11, rdi, r10
adox rcx, r15
adox r13, r8
mov rdx, [ rsi + 0x10 ]
mulx r15, r8, rbx
adcx rdi, rcx
adcx r13, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, rbx, rdx
mov rdx, r9
mulx rcx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mulx r12, r10, rbp
xor rdx, rdx
adox r10, r9
adox rcx, r12
adcx rbx, r8
adcx r15, r11
mov rbp, rdi
shrd rbp, r13, 52
xor r8, r8
adox rbp, rax
adox r14, r8
mov rdx, 0xfffffffffffff 
and rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, rax, rdx
adox rax, [ rsp - 0x28 ]
adox r13, [ rsp - 0x30 ]
mov rdx, rbp
adcx rdx, [ rsp - 0x18 ]
adcx r14, [ rsp - 0x20 ]
mov r11, 0x34 
bzhi r9, rdx, r11
shrd rdx, r14, 52
add rdx, r10
adc rcx, 0x0
mov r12, r9
shr r12, 48
bzhi r10, rdx, r11
shrd rdx, rcx, 52
add rdx, rax
adc r13, 0x0
mov rbp, rdx
mov rdx, [ rsp - 0x48 ]
mulx r14, rax, [ rsi + 0x20 ]
mov rdx, rbp
shrd rdx, r13, 52
shl r10, 4
add rdx, rax
adc r14, 0x0
mov rcx, rdx
shrd rcx, r14, 52
bzhi rax, rbp, r11
bzhi rbp, rdx, r11
mov r13, 0x1000003d10 
mov rdx, r13
mulx r14, r13, rax
mov rdx, [ rsi + 0x0 ]
mulx r8, rax, rdx
lea r10, [ r10 + r12 ]
mov rdx, 0x1000003d1 
mulx r11, r12, r10
adox r12, rax
adox r8, r11
mov rax, 0x30 
bzhi r10, r9, rax
mov r9, 0xfffffffffffff 
mov r11, r12
and r11, r9
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x0 ], r11
shrd r12, r8, 52
add r12, [ rsp - 0x38 ]
mov r8, [ rsp - 0x40 ]
adc r8, 0x0
mov r11, 0x1000003d10 
mov rdx, rbp
mulx r9, rbp, r11
add r13, r12
adcx r8, r14
mov rdx, r13
shrd rdx, r8, 52
mov r14, 0x34 
bzhi r12, r13, r14
adox rdx, rbx
mov r13, 0x0 
adox r15, r13
test al, al
adox rbp, rdx
adox r15, r9
bzhi rbx, rbp, r14
mov rdx, r11
mulx r9, r11, rcx
shrd rbp, r15, 52
lea rdi, [ rdi + rbp ]
add r11, rdi
adc r9, 0x0
mov [ rax + 0x10 ], rbx
bzhi rcx, r11, r14
shrd r11, r9, 52
lea r10, [ r10 + r11 ]
mov [ rax + 0x20 ], r10
mov [ rax + 0x18 ], rcx
mov [ rax + 0x8 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9785
; seed 1170714404961826 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4154 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=237, initial num_batches=31): 371 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08931150698122292
; number reverted permutation / tried permutation: 403 / 485 =83.093%
; number reverted decision / tried decision: 349 / 514 =67.899%
; validated in 0.206s
