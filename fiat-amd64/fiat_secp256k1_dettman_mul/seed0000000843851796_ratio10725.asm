SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x10 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
add r15, r10
adcx r11, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r8
mov [ rsp - 0x20 ], rcx
mulx rcx, r8, [ rsi + 0x18 ]
xor rdx, rdx
adox r13, r8
adox rcx, r14
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, [ rax + 0x10 ]
adcx r15, r10
adcx rdi, r11
mov rdx, [ rsi + 0x20 ]
mulx r10, r11, [ rax + 0x10 ]
add r13, r14
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, [ rax + 0x18 ]
test al, al
adox r13, r9
adox rbx, r8
adcx r11, rcx
adcx r14, r10
mov rdx, [ rsi + 0x20 ]
mulx r10, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r11
mulx r11, r14, [ rsi + 0x10 ]
add rbp, r14
adcx r11, r12
xor rdx, rdx
adox rbp, r8
adox rcx, r11
mov r12, 0xfffffffffffff 
mov r8, r9
and r8, r12
mov rdx, [ rax + 0x18 ]
mulx r11, r14, [ rsi + 0x0 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x8 ], rdi
mulx rdi, r12, r8
adox rbp, r14
adox r11, rcx
adcx r12, rbp
adcx r11, rdi
mov rcx, r12
shrd rcx, r11, 52
mov rdx, [ rax + 0x20 ]
mulx r14, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, r8
adox r14, rbx
shrd r9, r10, 52
add rcx, r13
adc r14, 0x0
mov rbx, 0x1000003d10 
mov rdx, rbx
mulx r10, rbx, r9
test al, al
adox rbx, rcx
adox r14, r10
mov rdi, 0xfffffffffffff 
and r12, rdi
mov rbp, rbx
shrd rbp, r14, 52
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, [ rax + 0x20 ]
and rbx, rdi
adox r15, r11
adox r8, [ rsp - 0x8 ]
mov rdx, 0xffffffffffff 
mov r13, rbx
and r13, rdx
shr rbx, 48
add rbp, r15
adc r8, 0x0
mov r9, rbp
and r9, rdi
shrd rbp, r8, 52
mov rdx, [ rax + 0x20 ]
mulx r10, rcx, [ rsi + 0x10 ]
shl r9, 4
lea r9, [ r9 + rbx ]
mov rdx, rcx
add rdx, [ rsp - 0x10 ]
adcx r10, [ rsp - 0x18 ]
mov r14, rdx
mov rdx, [ rax + 0x20 ]
mulx r15, r11, [ rsi + 0x18 ]
mov rdx, 0x1000003d1 
mulx r8, rbx, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ rax + 0x0 ]
xor rdx, rdx
adox rbp, r14
adox r10, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r14, [ rsi + 0x20 ]
adcx r14, r11
adcx r15, rdi
mov rdx, 0x34 
bzhi r11, rbp, rdx
adox rbx, rcx
adox r9, r8
shrd rbp, r10, 52
bzhi r8, rbx, rdx
adox rbp, r14
mov rcx, 0x0 
adox r15, rcx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, [ rax + 0x0 ]
mov rdx, 0x1000003d10 
mulx rcx, r14, r11
test al, al
adox r10, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
shrd rbx, r9, 52
mov r11, rbp
shrd r11, r15, 52
xor r9, r9
adox rbx, r10
adox rdi, r9
adcx r14, rbx
adcx rdi, rcx
mov r15, r14
shrd r15, rdi, 52
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, [ rax + 0x8 ]
mov rdx, 0xfffffffffffff 
and r14, rdx
mov rbx, 0x1000003d10 
mov rdx, rbx
mulx rdi, rbx, r11
mov r11, rcx
adox r11, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
mov rcx, 0x34 
bzhi r9, rbp, rcx
adox r11, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
xor rbp, rbp
adox r15, r11
adox r10, rbp
mulx rbp, r11, r9
adcx r11, r15
adcx r10, rbp
bzhi r9, r11, rcx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], r9
shrd r11, r10, 52
lea r12, [ r12 + r11 ]
xor rbp, rbp
adox rbx, r12
adox rdi, rbp
bzhi r10, rbx, rcx
mov [ r15 + 0x8 ], r14
shrd rbx, rdi, 52
lea r13, [ r13 + rbx ]
mov [ r15 + 0x0 ], r8
mov [ r15 + 0x20 ], r13
mov [ r15 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0725
; seed 1206382180236178 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1957870 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=339, initial num_batches=31): 164549 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08404490594370413
; number reverted permutation / tried permutation: 70311 / 90024 =78.103%
; number reverted decision / tried decision: 51961 / 89975 =57.750%
; validated in 0.713s
