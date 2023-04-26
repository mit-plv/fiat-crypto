SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
add r13, r9
adcx rbx, r14
mov rdx, [ rax + 0x18 ]
mulx r14, r9, [ rsi + 0x0 ]
test al, al
adox r13, r15
adox rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x8 ]
adcx r13, r9
adcx r14, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r15
mulx r15, rbx, [ rsi + 0x20 ]
test al, al
adox rbx, rbp
adox r12, r15
adcx rbx, r9
adcx rdi, r12
mov rdx, [ rax + 0x20 ]
mulx r9, rbp, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, r11, 52
mov r11, 0x1000003d10 
mulx r12, r15, r11
add rbx, rcx
adcx r8, rdi
mov rcx, 0xfffffffffffff 
and r10, rcx
mov rdx, r11
mulx rdi, r11, r10
adox r11, r13
adox r14, rdi
adcx rbx, rbp
adcx r9, r8
mov r13, r11
shrd r13, r14, 52
mov rdx, [ rsi + 0x18 ]
mulx r8, rbp, [ rax + 0x10 ]
add r13, rbx
adc r9, 0x0
mov rdx, [ rsi + 0x20 ]
mulx rdi, r10, [ rax + 0x8 ]
xor rdx, rdx
adox r15, r13
adox r9, r12
mov rdx, [ rsi + 0x20 ]
mulx r14, r12, [ rax + 0x10 ]
mov rdx, r15
shrd rdx, r9, 52
mov rbx, rdx
mov rdx, [ rax + 0x20 ]
mulx r9, r13, [ rsi + 0x8 ]
test al, al
adox r10, rbp
adox r8, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, [ rax + 0x18 ]
adcx r10, rbp
adcx rdi, r8
and r15, rcx
adox r10, r13
adox r9, rdi
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x18 ]
mov rdx, 0x30 
bzhi rbp, r15, rdx
adox r12, r13
adox r8, r14
xor r14, r14
adox rbx, r10
adox r9, r14
mov rdx, [ rsi + 0x10 ]
mulx r10, rdi, [ rax + 0x20 ]
mov rdx, rbx
and rdx, rcx
shl rdx, 4
shr r15, 48
lea rdx, [ rdx + r15 ]
shrd rbx, r9, 52
mov r13, rdx
mov rdx, [ rax + 0x0 ]
mulx r15, r9, [ rsi + 0x8 ]
mov rdx, 0x1000003d1 
mulx rcx, r14, r13
xor r13, r13
adox r12, rdi
adox r10, r8
adcx rbx, r12
adc r10, 0x0
mov r8, rbx
shrd r8, r10, 52
mov rdx, [ rax + 0x0 ]
mulx r12, rdi, [ rsi + 0x0 ]
add r14, rdi
adcx r12, rcx
mov rdx, 0xfffffffffffff 
mov rcx, r14
and rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, [ rax + 0x0 ]
shrd r14, r12, 52
mov rdx, [ rsi + 0x20 ]
mulx r13, r12, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], rbp
mulx rbp, rcx, [ rax + 0x20 ]
add r12, rcx
adcx rbp, r13
mov rdx, 0xfffffffffffff 
and rbx, rdx
adox r8, r12
mov r13, 0x0 
adox rbp, r13
mov rdx, [ rax + 0x8 ]
mulx r12, rcx, [ rsi + 0x8 ]
adcx r10, rcx
adcx r12, rdi
test al, al
adox r9, [ rsp - 0x40 ]
adox r15, [ rsp - 0x48 ]
mov rdx, 0x1000003d10 
mulx rcx, rdi, rbx
adcx r14, r9
adc r15, 0x0
add rdi, r14
adcx r15, rcx
mov rdx, [ rax + 0x10 ]
mulx r9, rbx, [ rsi + 0x0 ]
test al, al
adox r10, rbx
adox r9, r12
mov rdx, 0x34 
bzhi r12, r8, rdx
bzhi rcx, rdi, rdx
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], rcx
mov rbx, 0x1000003d10 
mov rdx, rbx
mulx rcx, rbx, r12
shrd rdi, r15, 52
xor r15, r15
adox rdi, r10
adox r9, r15
adcx rbx, rdi
adcx r9, rcx
mov r13, rbx
shrd r13, r9, 52
mov r10, 0x34 
bzhi r12, r11, r10
shrd r8, rbp, 52
bzhi r11, rbx, r10
lea r12, [ r12 + r13 ]
mulx rcx, rbp, r8
adox rbp, r12
adox rcx, r15
mov rdi, rbp
shrd rdi, rcx, 52
bzhi rbx, rbp, r10
mov [ r14 + 0x18 ], rbx
add rdi, [ rsp - 0x30 ]
mov r9, [ rsp - 0x38 ]
mov [ r14 + 0x0 ], r9
mov [ r14 + 0x20 ], rdi
mov [ r14 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0975
; seed 3669198900705881 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2174500 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=174, initial num_batches=31): 140731 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06471878592779949
; number reverted permutation / tried permutation: 71553 / 90056 =79.454%
; number reverted decision / tried decision: 52204 / 89943 =58.041%
; validated in 0.539s
