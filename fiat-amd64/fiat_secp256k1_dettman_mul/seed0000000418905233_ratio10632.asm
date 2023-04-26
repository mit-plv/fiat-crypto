SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
test al, al
adox r13, r10
adox r11, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r10
mulx r10, r14, [ rax + 0x8 ]
adcx r15, r14
adcx r10, rdi
mov rdx, 0xfffffffffffff 
mov rdi, rcx
and rdi, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r14, [ rsi + 0x8 ]
adox r13, r14
adox rbx, r11
mov rdx, [ rsi + 0x0 ]
mulx r14, r11, [ rax + 0x18 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r12
mulx r12, r9, rdi
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, rdi, [ rax + 0x18 ]
adcx r13, r11
adcx r14, rbx
add r9, r13
adcx r14, r12
mov rdx, 0x34 
bzhi rbx, r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, r11, [ rax + 0x10 ]
shrd r9, r14, 52
mov rdx, [ rsi + 0x10 ]
mulx r14, r13, [ rax + 0x10 ]
test al, al
adox r15, r13
adox r14, r10
adcx r15, rdi
adcx rbp, r14
xor rdx, rdx
adox r15, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x28 ]
adcx r9, r15
adc rbp, 0x0
mov r10, r11
add r10, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rdi, [ rax + 0x18 ]
shrd rcx, r8, 52
mov rdx, 0x1000003d10 
mulx r13, r8, rcx
add r8, r9
adcx rbp, r13
add r10, rdi
adcx r11, r12
mov r14, 0x34 
bzhi r15, r8, r14
mov r9, r15
shr r9, 48
mov rdx, [ rax + 0x10 ]
mulx rdi, r12, [ rsi + 0x20 ]
mov rdx, 0xffffffffffff 
and r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, [ rax + 0x18 ]
adox r12, rcx
adox r13, rdi
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x18 ], r15
mulx r15, r14, [ rsi + 0x18 ]
adcx r12, rdi
adcx rcx, r13
shrd r8, rbp, 52
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x8 ]
test al, al
adox r10, rbp
adox r13, r11
adcx r8, r10
adc r13, 0x0
mov rdx, [ rax + 0x18 ]
mulx rdi, r11, [ rsi + 0x20 ]
mov rdx, r8
shrd rdx, r13, 52
xor rbp, rbp
adox r11, r14
adox r15, rdi
adcx rdx, r12
adc rcx, 0x0
mov r14, rdx
shrd r14, rcx, 52
mov r12, 0x34 
bzhi r10, rdx, r12
adox r14, r11
adox r15, rbp
mov r13, 0x1000003d10 
mov rdx, r10
mulx rdi, r10, r13
mov r11, r14
shrd r11, r15, 52
bzhi rcx, r8, r12
bzhi r8, r14, r12
shl rcx, 4
mov rdx, r8
mulx r14, r8, r13
mov rdx, [ rax + 0x0 ]
mulx rbp, r15, [ rsi + 0x8 ]
lea rcx, [ rcx + r9 ]
mov rdx, 0x1000003d1 
mulx r12, r9, rcx
mov rdx, [ rax + 0x8 ]
mulx r13, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rbx
mov [ rsp - 0x8 ], r11
mulx r11, rbx, [ rax + 0x0 ]
test al, al
adox r9, rbx
adox r11, r12
mov rdx, 0x34 
bzhi r12, r9, rdx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], r12
shrd r9, r11, 52
xor r11, r11
adox r15, rcx
adox r13, rbp
adcx r9, r15
adc r13, 0x0
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbp, [ rax + 0x8 ]
mov rdx, rbp
test al, al
adox rdx, [ rsp - 0x40 ]
adox rcx, [ rsp - 0x48 ]
mov r12, rdx
mov rdx, [ rax + 0x10 ]
mulx rbp, r15, [ rsi + 0x0 ]
adcx r10, r9
adcx r13, rdi
add r12, r15
adcx rbp, rcx
mov rdx, r10
shrd rdx, r13, 52
xor rdi, rdi
adox rdx, r12
adox rbp, rdi
adcx r8, rdx
adcx rbp, r14
mov r11, r8
shrd r11, rbp, 52
mov r14, 0x34 
bzhi r9, r8, r14
mov rcx, 0x1000003d10 
mov rdx, rcx
mulx r15, rcx, [ rsp - 0x8 ]
add r11, [ rsp - 0x10 ]
xor r13, r13
adox rcx, r11
adox r15, r13
mov rdi, rcx
shrd rdi, r15, 52
bzhi r12, r10, r14
mov [ rbx + 0x8 ], r12
bzhi r10, rcx, r14
mov [ rbx + 0x18 ], r10
add rdi, [ rsp - 0x18 ]
mov [ rbx + 0x10 ], r9
mov [ rbx + 0x20 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0632
; seed 0800742874428658 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1417083 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=177, initial num_batches=31): 90849 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06410986512434345
; number reverted permutation / tried permutation: 71428 / 89979 =79.383%
; number reverted decision / tried decision: 52316 / 90020 =58.116%
; validated in 0.559s
