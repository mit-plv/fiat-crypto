SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x18 ]
xor rdx, rdx
adox rcx, r13
adox r14, r8
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, [ rax + 0x10 ]
adcx rcx, r8
adcx r13, r14
mov rdx, [ rsi + 0x0 ]
mulx r8, r14, [ rax + 0x18 ]
mov rdx, r9
shrd rdx, rbx, 52
mov rbx, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, [ rsi + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rdi
mulx rdi, r15, rbx
mov rbx, 0xfffffffffffff 
and r9, rbx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, rbx, [ rsi + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x20 ], rdi
mov [ rsp - 0x18 ], rbx
mulx rbx, rdi, r9
adox rcx, r14
adox r8, r13
mov rdx, [ rax + 0x0 ]
mulx r14, r13, [ rsi + 0x20 ]
adcx r13, r10
adcx r11, r14
test al, al
adox r13, rbp
adox r12, r11
mov rdx, [ rax + 0x20 ]
mulx rbp, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mulx r14, r9, [ rsi + 0x8 ]
adcx rdi, rcx
adcx r8, rbx
test al, al
adox r13, r9
adox r14, r12
mov rdx, 0x34 
bzhi rbx, rdi, rdx
shrd rdi, r8, 52
test al, al
adox r13, r10
adox rbp, r14
adcx rdi, r13
adc rbp, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x10 ]
xor rdx, rdx
adox r15, rdi
adox rbp, [ rsp - 0x28 ]
mov rdx, [ rax + 0x8 ]
mulx r10, r12, [ rsi + 0x20 ]
adcx r12, rcx
adcx r11, r10
mov rdx, [ rsi + 0x20 ]
mulx r8, r9, [ rax + 0x10 ]
mov rdx, 0xfffffffffffff 
mov r14, r15
and r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x20 ]
adox r12, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
adcx r12, r13
adcx rdi, r11
mov rdx, r14
shr rdx, 48
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx r13, r10, [ rsi + 0x0 ]
mov rdx, 0x30 
bzhi r11, r14, rdx
shrd r15, rbp, 52
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r11
mov [ rsp - 0x8 ], rbx
mulx rbx, r11, [ rax + 0x20 ]
xor rdx, rdx
adox r15, r12
adox rdi, rdx
mov r12, r15
shrd r12, rdi, 52
xor rdi, rdi
adox r9, rbp
adox r14, r8
adcx r9, r11
adcx rbx, r14
mov rdx, 0xfffffffffffff 
and r15, rdx
shl r15, 4
mov rdx, [ rsi + 0x18 ]
mulx rbp, r8, [ rax + 0x20 ]
lea r15, [ r15 + rcx ]
mov rdx, 0x1000003d1 
mulx r11, rcx, r15
add r12, r9
adc rbx, 0x0
mov r14, r12
shrd r14, rbx, 52
mov r9, r8
test al, al
adox r9, [ rsp - 0x18 ]
adox rbp, [ rsp - 0x20 ]
adcx rcx, r10
adcx r13, r11
test al, al
adox r14, r9
adox rbp, rdi
mov r10, 0xfffffffffffff 
mov r8, rcx
and r8, r10
mov r15, r14
shrd r15, rbp, 52
mov rdx, [ rsi + 0x10 ]
mulx rbx, r11, [ rax + 0x0 ]
and r14, r10
mov rdx, [ rax + 0x8 ]
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r10, rdi, [ rsi + 0x8 ]
mov rdx, 0xfffffffffffff 
and r12, rdx
adox rdi, r9
adox rbp, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r9, [ rax + 0x10 ]
shrd rcx, r13, 52
xor rdx, rdx
adox r11, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx rcx, rdi
adc rbp, 0x0
test al, al
adox r11, r9
adox r10, rbx
mov r13, 0x1000003d10 
mov rdx, r13
mulx rdi, r13, r12
adcx r13, rcx
adcx rbp, rdi
mov r12, r13
shrd r12, rbp, 52
xor r9, r9
adox r12, r11
adox r10, r9
mulx rcx, rbx, r14
adcx rbx, r12
adcx r10, rcx
mov r14, 0x34 
bzhi r11, r13, r14
mov rdi, rbx
shrd rdi, r10, 52
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r11
mulx r12, rbp, r15
add rdi, [ rsp - 0x8 ]
bzhi r15, rbx, r14
mov [ r13 + 0x10 ], r15
adox rbp, rdi
adox r12, r9
mov rcx, rbp
shrd rcx, r12, 52
bzhi rbx, rbp, r14
mov [ r13 + 0x0 ], r8
add rcx, [ rsp - 0x10 ]
mov [ r13 + 0x20 ], rcx
mov [ r13 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 0.9924
; seed 3553878266742847 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1305849 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=194, initial num_batches=31): 88538 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06780110104613933
; number reverted permutation / tried permutation: 68123 / 90354 =75.396%
; number reverted decision / tried decision: 37192 / 89645 =41.488%
; validated in 0.39s
