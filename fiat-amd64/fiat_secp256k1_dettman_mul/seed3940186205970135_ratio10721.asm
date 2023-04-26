SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
xor rdx, rdx
adox r9, r14
adox r13, rbx
mov rdx, [ rax + 0x18 ]
mulx r14, rbx, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x8 ], rbp
mov [ rsp + 0x0 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
adcx rbx, rcx
adcx r8, r14
xor rdx, rdx
adox r10, r15
adox rdi, r11
mov rdx, [ rax + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r14, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r8
mov [ rsp + 0x10 ], rbx
mulx rbx, r8, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x18 ], rdi
mov [ rsp + 0x20 ], r10
mulx r10, rdi, [ rax + 0x8 ]
adcx r11, rdi
adcx r10, rcx
add r11, r8
adcx rbx, r10
xor rdx, rdx
adox r9, r15
adox r14, r13
mov rdx, [ rax + 0x10 ]
mulx rcx, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, r15, [ rax + 0x8 ]
adcx r15, r13
adcx rcx, r8
mov rdx, [ rsi + 0x0 ]
mulx r10, rdi, [ rax + 0x18 ]
xor rdx, rdx
adox r11, rdi
adox r10, rbx
mov rbx, 0xfffffffffffff 
mov r13, rbp
and r13, rbx
mov r8, 0x1000003d10 
mov rdx, r13
mulx rdi, r13, r8
adox r13, r11
adox r10, rdi
mov r11, r13
and r11, rbx
mov rdx, [ rsi + 0x0 ]
mulx r8, rdi, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x28 ], r11
mulx r11, rbx, [ rsi + 0x8 ]
adox r15, [ rsp - 0x10 ]
adox rcx, [ rsp - 0x18 ]
shrd r13, r10, 52
mov rdx, [ rsp - 0x20 ]
mov r10, rdx
test al, al
adox r10, [ rsp + 0x20 ]
mov [ rsp + 0x30 ], r14
mov r14, [ rsp - 0x28 ]
adox r14, [ rsp + 0x18 ]
adcx r10, [ rsp - 0x30 ]
adcx r14, [ rsp - 0x38 ]
shrd rbp, r12, 52
xor rdx, rdx
adox r10, rdi
adox r8, r14
adcx r13, r10
adc r8, 0x0
mov r12, 0x1000003d10 
mov rdx, rbp
mulx rdi, rbp, r12
xor r14, r14
adox rbp, r13
adox r8, rdi
mov rdx, rbp
shrd rdx, r8, 52
mov r10, 0x34 
bzhi r13, rbp, r10
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rbp, [ rax + 0x10 ]
mov rdx, r13
shr rdx, 48
xor r10, r10
adox r15, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
adcx rdi, r15
adc rcx, 0x0
mov r14, rdi
shrd r14, rcx, 52
mov r15, 0x34 
bzhi r10, rdi, r15
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, [ rax + 0x18 ]
shl r10, 4
lea r10, [ r10 + rdi ]
xor rdx, rdx
adox rbp, rcx
adox r15, r8
adcx rbp, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
mov r8, 0x30 
bzhi rdi, r13, r8
adox r14, rbp
adox r15, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r13, [ rsi + 0x0 ]
add rbx, r13
adcx rcx, r11
mov rdx, [ rax + 0x0 ]
mulx rbp, r11, [ rsi + 0x0 ]
mov rdx, 0x1000003d1 
mulx r8, r13, r10
mov r10, 0x34 
bzhi rdx, r14, r10
adox r13, r11
adox rbp, r8
bzhi r11, r13, r10
shrd r13, rbp, 52
test al, al
adox r13, rbx
mov r8, 0x0 
adox rcx, r8
mulx rbp, rbx, r12
adcx rbx, r13
adcx rcx, rbp
bzhi rdx, rbx, r10
shrd rbx, rcx, 52
xor r13, r13
adox rbx, r9
mov r8, [ rsp + 0x30 ]
adox r8, r13
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], rdx
shrd r14, r15, 52
xor r15, r15
adox r14, [ rsp + 0x10 ]
mov r13, [ rsp + 0x8 ]
adox r13, r15
mov rbp, r14
shrd rbp, r13, 52
mov rdx, r12
mulx rcx, r12, rbp
bzhi rbp, r14, r10
mulx r13, r14, rbp
adox r14, rbx
adox r8, r13
bzhi rbx, r14, r10
mov [ r9 + 0x10 ], rbx
shrd r14, r8, 52
add r14, [ rsp + 0x28 ]
add r12, r14
adc rcx, 0x0
mov rbp, r12
shrd rbp, rcx, 52
lea rdi, [ rdi + rbp ]
mov [ r9 + 0x20 ], rdi
bzhi r13, r12, r10
mov [ r9 + 0x0 ], r11
mov [ r9 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.0721
; seed 3940186205970135 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8437 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=220, initial num_batches=31): 491 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05819604124688871
; number reverted permutation / tried permutation: 353 / 487 =72.485%
; number reverted decision / tried decision: 318 / 512 =62.109%
; validated in 0.567s
