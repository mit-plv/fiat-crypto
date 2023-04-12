SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rax + 0x18 ]
mov rdx, r9
shrd rdx, rbx, 52
mov rbx, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], r8
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, [ rsi + 0x20 ]
test al, al
adox r8, r14
adox r13, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r14, [ rax + 0x8 ]
adcx rbp, r14
adcx rcx, r12
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, [ rax + 0x10 ]
test al, al
adox rbp, r12
adox r14, rcx
mov rdx, [ rax + 0x18 ]
mulx r12, rcx, [ rsi + 0x8 ]
mov rdx, 0x34 
mov [ rsp - 0x8 ], rbx
bzhi rbx, r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r14
mulx r14, r9, [ rax + 0x20 ]
adox r8, r15
adox rdi, r13
test al, al
adox r8, rcx
adox r12, rdi
mov rdx, 0x1000003d10 
mulx r13, r15, rbx
adcx rbp, r10
adcx r11, [ rsp + 0x0 ]
add r15, rbp
adcx r11, r13
test al, al
adox r8, r9
adox r14, r12
mov r10, r15
shrd r10, r11, 52
test al, al
adox r10, r8
mov rcx, 0x0 
adox r14, rcx
mulx r9, rbx, [ rsp - 0x8 ]
adcx rbx, r10
adcx r14, r9
mov rdi, rbx
shrd rdi, r14, 52
mov r12, 0xfffffffffffff 
and r15, r12
mov rdx, [ rax + 0x8 ]
mulx rbp, r13, [ rsi + 0x20 ]
adox r13, [ rsp - 0x10 ]
adox rbp, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, r11, [ rax + 0x18 ]
adcx r13, r11
adcx r8, rbp
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rax + 0x20 ]
test al, al
adox r13, r10
adox r9, r8
adcx rdi, r13
adc r9, 0x0
mov rdx, [ rax + 0x18 ]
mulx rbp, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, r11, [ rax + 0x10 ]
test al, al
adox r11, r14
adox rbp, r8
adcx r11, [ rsp - 0x20 ]
adcx rbp, [ rsp - 0x28 ]
mov rdx, rdi
shrd rdx, r9, 52
test al, al
adox rdx, r11
adox rbp, rcx
mov r10, rdx
shrd r10, rbp, 52
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r9, [ rax + 0x20 ]
mov rdx, r9
xor r8, r8
adox rdx, [ rsp - 0x30 ]
adox r14, [ rsp - 0x38 ]
adcx r10, rdx
adc r14, 0x0
mov rcx, r10
and rcx, r12
and rbx, r12
mov r11, 0x30 
bzhi rbp, rbx, r11
and rdi, r12
shl rdi, 4
mov rdx, [ rax + 0x8 ]
mulx r8, r9, [ rsi + 0x0 ]
shr rbx, 48
mov rdx, [ rax + 0x0 ]
mulx r12, r11, [ rsi + 0x0 ]
lea rdi, [ rdi + rbx ]
mov rdx, 0x1000003d1 
mov [ rsp + 0x8 ], rbp
mulx rbp, rbx, rdi
xor rdi, rdi
adox rbx, r11
adox r12, rbp
shrd r10, r14, 52
mov rdx, [ rsi + 0x8 ]
mulx r11, r14, [ rax + 0x0 ]
mov rdx, 0x34 
bzhi rbp, rbx, rdx
shrd rbx, r12, 52
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], rbp
xor rbp, rbp
adox r14, r9
adox r8, r11
bzhi rdi, r13, rdx
mov r13, 0x1000003d10 
mov rdx, r13
mulx r9, r13, rdi
adox rbx, r14
adox r8, rbp
mov rdx, [ rax + 0x10 ]
mulx r14, r11, [ rsi + 0x0 ]
add r13, rbx
adcx r8, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, rdi, [ rax + 0x8 ]
mov rdx, rdi
test al, al
adox rdx, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
adcx rdx, r11
adcx r14, r9
mov rbx, 0x1000003d10 
xchg rdx, rbx
mulx rdi, r11, rcx
mov rcx, r13
shrd rcx, r8, 52
add rcx, rbx
adc r14, 0x0
add r11, rcx
adcx r14, rdi
mov r8, r11
shrd r8, r14, 52
mulx rbx, r9, r10
lea r15, [ r15 + r8 ]
xor r10, r10
adox r9, r15
adox rbx, r10
mov rbp, 0x34 
bzhi rdi, r9, rbp
shrd r9, rbx, 52
bzhi rcx, r11, rbp
add r9, [ rsp + 0x8 ]
bzhi r11, r13, rbp
mov [ r12 + 0x20 ], r9
mov [ r12 + 0x18 ], rdi
mov [ r12 + 0x8 ], r11
mov [ r12 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0038
; seed 0581699663046300 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1269110 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=184, initial num_batches=31): 88117 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06943212172309729
; number reverted permutation / tried permutation: 67477 / 90049 =74.934%
; number reverted decision / tried decision: 37309 / 89950 =41.477%
; validated in 0.417s
