SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x20 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0x34 
mov [ rsp - 0x58 ], r15
bzhi r15, r10, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
adox rcx, r9
adox rbx, r8
mov rdx, [ rax + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
shrd r10, r11, 52
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r9
mulx r9, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r11
adox r9, rbx
mov rbx, 0x1000003d10 
mov rdx, r10
mulx r11, r10, rbx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
adcx rcx, rbx
adcx r8, r9
mov rdx, 0x1000003d10 
mulx rbx, r9, r15
test al, al
adox r9, rcx
adox r8, rbx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], rdi
mulx rdi, rbx, [ rsi + 0x20 ]
adcx rbx, r15
adcx rcx, rdi
test al, al
adox rbx, rbp
adox r12, rcx
adcx rbx, r13
adcx r14, r12
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x0 ]
test al, al
adox rbx, rbp
adox r13, r14
mov rdx, [ rax + 0x10 ]
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx r12, rcx, [ rsi + 0x20 ]
mov rdx, r9
shrd rdx, r8, 52
test al, al
adox rcx, r15
adox rdi, r12
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r12, r15, [ rsi + 0x10 ]
adcx r8, rbx
adc r13, 0x0
test al, al
adox rcx, r15
adox r12, rdi
mov rdx, [ rax + 0x20 ]
mulx rdi, rbx, [ rsi + 0x8 ]
adcx r10, r8
adcx r13, r11
mov rdx, r10
shrd rdx, r13, 52
mov r11, 0xfffffffffffff 
and r10, r11
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx r13, r8, [ rsi + 0x20 ]
adox r8, r14
adox rbp, r13
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, [ rax + 0x8 ]
adcx rcx, rbx
adcx rdi, r12
mov rdx, [ rax + 0x0 ]
mulx rbx, r12, [ rsi + 0x0 ]
test al, al
adox r15, rcx
mov rdx, 0x0 
adox rdi, rdx
mov rcx, r15
and rcx, r11
shl rcx, 4
mov rdx, r10
shr rdx, 48
lea rcx, [ rcx + rdx ]
mov rdx, 0x1000003d1 
mov [ rsp - 0x18 ], r13
mulx r13, r11, rcx
xor rcx, rcx
adox r11, r12
adox rbx, r13
mov rdx, [ rsi + 0x10 ]
mulx r13, r12, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
mov rcx, r11
and rcx, rdx
shrd r11, rbx, 52
add r8, r12
adcx r13, rbp
shrd r15, rdi, 52
mov rdx, [ rax + 0x8 ]
mulx rdi, rbp, [ rsi + 0x8 ]
mov rdx, r14
xor rbx, rbx
adox rdx, [ rsp - 0x20 ]
mov r12, [ rsp - 0x38 ]
adox r12, [ rsp - 0x18 ]
adcx r11, rdx
adc r12, 0x0
test al, al
adox r15, r8
adox r13, rbx
mov r14, 0x34 
bzhi r8, r15, r14
shrd r15, r13, 52
mov rdx, 0x1000003d10 
mulx rbx, r13, r8
mov rdx, [ rax + 0x0 ]
mulx r14, r8, [ rsi + 0x10 ]
test al, al
adox r8, rbp
adox rdi, r14
adcx r8, [ rsp - 0x28 ]
adcx rdi, [ rsp - 0x30 ]
test al, al
adox r13, r11
adox r12, rbx
mov rdx, [ rax + 0x20 ]
mulx r11, rbp, [ rsi + 0x18 ]
mov rdx, rbp
adcx rdx, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
mov rbx, 0xfffffffffffff 
mov r14, r13
and r14, rbx
adox r15, rdx
mov rbp, 0x0 
adox r11, rbp
mov rdx, r15
shrd rdx, r11, 52
and r15, rbx
shrd r13, r12, 52
test al, al
adox r13, r8
adox rdi, rbp
mov r8, 0x1000003d10 
xchg rdx, r15
mulx r11, r12, r8
adcx r12, r13
adcx rdi, r11
and r9, rbx
mov rdx, r12
shrd rdx, rdi, 52
lea r9, [ r9 + rdx ]
mov rdx, r15
mulx r13, r15, r8
test al, al
adox r15, r9
adox r13, rbp
mov rdx, 0xffffffffffff 
and r10, rdx
mov r11, r15
shrd r11, r13, 52
and r15, rbx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r14
mov [ rdi + 0x0 ], rcx
and r12, rbx
lea r10, [ r10 + r11 ]
mov [ rdi + 0x18 ], r15
mov [ rdi + 0x20 ], r10
mov [ rdi + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0034
; seed 0309980762122920 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1313279 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=210, initial num_batches=31): 95813 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07295707918880907
; number reverted permutation / tried permutation: 66771 / 89664 =74.468%
; number reverted decision / tried decision: 37287 / 90335 =41.276%
; validated in 0.394s
