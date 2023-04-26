SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x0 ]
add r10, r15
adcx rdi, r11
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x10 ]
add r13, r11
adcx r15, r14
test al, al
adox rbx, rcx
adox r8, r9
mov rdx, [ rsi + 0x10 ]
mulx r14, rcx, [ rax + 0x10 ]
adcx rbx, rcx
adcx r14, r8
mov rdx, [ rax + 0x18 ]
mulx r11, r9, [ rsi + 0x8 ]
test al, al
adox rbx, r9
adox r11, r14
adcx rbx, rbp
adcx r12, r11
mov rdx, [ rax + 0x8 ]
mulx r8, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r14, rcx, [ rax + 0x20 ]
mov rdx, rcx
shrd rdx, r14, 52
mov r9, 0x34 
bzhi r11, rcx, r9
mov rcx, rbp
adox rcx, [ rsp - 0x40 ]
adox r8, [ rsp - 0x48 ]
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r14, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r10
mulx r10, rdi, [ rsi + 0x8 ]
add rcx, rdi
adcx r10, r8
add rcx, r14
adcx r9, r10
mov rdx, 0x1000003d10 
mulx r14, r8, r11
test al, al
adox r8, rcx
adox r9, r14
mov r11, r8
shrd r11, r9, 52
xor rdi, rdi
adox r11, rbx
adox r12, rdi
mulx r10, rbx, rbp
adcx rbx, r11
adcx r12, r10
mov rbp, 0xfffffffffffff 
and r8, rbp
mov rdx, [ rax + 0x18 ]
mulx r14, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r11, r9, [ rsi + 0x8 ]
adox r13, rcx
adox r14, r15
adcx r13, r9
adcx r11, r14
mov rdx, rbx
shrd rdx, r12, 52
xor r15, r15
adox rdx, r13
adox r11, r15
mov rdi, rdx
and rdi, rbp
and rbx, rbp
shl rdi, 4
mov r10, rbx
shr r10, 48
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, [ rax + 0x8 ]
lea rdi, [ rdi + r10 ]
mov rdx, 0xffffffffffff 
and rbx, rdx
adox rcx, r14
adox r13, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r13
mulx r13, r8, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r13
mov [ rsp - 0x8 ], r8
mulx r8, r13, [ rax + 0x20 ]
adcx r14, r10
adcx r9, r15
mov rdx, 0x1000003d1 
mulx r15, r10, rdi
test al, al
adox r10, rbp
adox rbx, r15
mov rdi, 0x34 
bzhi rbp, r10, rdi
shrd r10, rbx, 52
xor r15, r15
adox r10, rcx
mov rbx, [ rsp - 0x18 ]
adox rbx, r15
shrd r12, r11, 52
mov rdx, [ rax + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r14, r13
adox r8, r9
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], rbp
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, [ rax + 0x10 ]
adcx r12, r14
adc r8, 0x0
bzhi rdx, r12, rdi
mov rbp, 0x1000003d10 
mulx rdi, r14, rbp
shrd r12, r8, 52
xor r8, r8
adox r11, [ rsp - 0x8 ]
adox rcx, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x30 ]
mov rdx, [ rsp - 0x38 ]
adc rdx, 0x0
mov r8, 0x34 
bzhi rbp, r12, r8
shrd r12, rdx, 52
xor rdx, rdx
adox r14, r10
adox rbx, rdi
adcx r11, r13
adcx r9, rcx
bzhi r10, r14, r8
shrd r14, rbx, 52
mov r13, 0x1000003d10 
mov rdx, r13
mulx rdi, r13, rbp
xor rcx, rcx
adox r14, r11
adox r9, rcx
adcx r13, r14
adcx r9, rdi
mov rbp, r13
shrd rbp, r9, 52
bzhi rbx, r13, r8
add rbp, [ rsp - 0x20 ]
mulx rdi, r11, r12
test al, al
adox r11, rbp
adox rdi, rcx
mov r12, r11
shrd r12, rdi, 52
add r12, [ rsp - 0x28 ]
bzhi r14, r11, r8
mov [ r15 + 0x20 ], r12
mov [ r15 + 0x18 ], r14
mov [ r15 + 0x8 ], r10
mov [ r15 + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0660
; seed 1184052693197515 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1467040 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=182, initial num_batches=31): 91374 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06228460028356418
; number reverted permutation / tried permutation: 70402 / 90181 =78.067%
; number reverted decision / tried decision: 52292 / 89818 =58.220%
; validated in 0.538s
