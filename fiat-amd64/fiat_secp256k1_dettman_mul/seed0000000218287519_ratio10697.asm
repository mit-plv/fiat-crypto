SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x38 ], r9
mov r9, rcx
and r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r12
mulx r12, rbx, [ rsi + 0x18 ]
adox rbx, r10
adox r11, r12
adcx rbx, r15
adcx rdi, r11
test al, al
adox rbx, r13
adox r14, rdi
shrd rcx, r8, 52
mov rdx, [ rsi + 0x20 ]
mulx r8, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, [ rax + 0x8 ]
add r10, r13
adcx r15, r8
mov rdx, [ rsi + 0x10 ]
mulx r11, r12, [ rax + 0x10 ]
mov rdx, 0x1000003d10 
mulx r8, rdi, r9
mulx r13, r9, rcx
add rdi, rbx
adcx r14, r8
add r10, r12
adcx r11, r15
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rax + 0x18 ]
test al, al
adox r10, rbx
adox rcx, r11
mov rdx, 0x34 
bzhi r15, rdi, rdx
mov rdx, [ rax + 0x8 ]
mulx r8, r12, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, r11, [ rsi + 0x18 ]
adox r12, r11
adox rbx, r8
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, [ rax + 0x18 ]
test al, al
adox r12, r8
adox r11, rbx
shrd rdi, r14, 52
xor rdx, rdx
adox r10, rbp
adox rcx, [ rsp - 0x28 ]
adcx rdi, r10
adc rcx, 0x0
mov rdx, [ rax + 0x20 ]
mulx r14, rbp, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, rdi
adox rcx, r13
mov r13, r9
shrd r13, rcx, 52
xor rbx, rbx
adox r12, rbp
adox r14, r11
adcx r13, r12
adc r14, 0x0
mov rdx, r13
shrd rdx, r14, 52
mov r8, 0x34 
bzhi r11, r13, r8
bzhi r10, r9, r8
mov rdi, r10
shr rdi, 48
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r9, [ rax + 0x18 ]
shl r11, 4
lea r11, [ r11 + rdi ]
mov rdx, 0x1000003d1 
mulx r13, r12, r11
mov rdx, [ rsi + 0x0 ]
mulx rdi, r14, [ rax + 0x0 ]
test al, al
adox r12, r14
adox rdi, r13
mov rdx, [ rsi + 0x20 ]
mulx r13, r11, [ rax + 0x10 ]
adcx r11, r9
adcx rcx, r13
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rax + 0x20 ]
xor rdx, rdx
adox r11, r9
adox r14, rcx
bzhi rbx, r12, r8
shrd r12, rdi, 52
xor rdi, rdi
adox rbp, r11
adox r14, rdi
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], rbx
bzhi r13, rbp, r8
mov rcx, [ rsp - 0x30 ]
mov r9, rcx
adox r9, [ rsp - 0x40 ]
mov r11, [ rsp - 0x38 ]
adox r11, [ rsp - 0x48 ]
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbx, [ rax + 0x8 ]
shrd rbp, r14, 52
xor rdx, rdx
adox rbp, r9
adox r11, rdx
bzhi r14, rbp, r8
shrd rbp, r11, 52
mov rdx, [ rax + 0x0 ]
mulx r11, r9, [ rsi + 0x8 ]
test al, al
adox r9, rbx
adox rdi, r11
mov rdx, 0x1000003d10 
mulx r11, rbx, r13
adcx r12, r9
adc rdi, 0x0
xor r13, r13
adox rbx, r12
adox rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r8, [ rax + 0x8 ]
adcx r12, r8
adcx rcx, r13
xor rdx, rdx
adox r12, r9
adox r11, rcx
mov r9, rbx
shrd r9, rdi, 52
xor rdi, rdi
adox r9, r12
adox r11, rdi
mov rdx, 0x1000003d10 
mulx r8, r13, r14
adcx r13, r9
adcx r11, r8
mov r14, 0x34 
bzhi rcx, r13, r14
mulx r9, r12, rbp
shrd r13, r11, 52
lea r15, [ r15 + r13 ]
add r12, r15
adc r9, 0x0
bzhi rbp, rbx, r14
bzhi rbx, r12, r14
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], rbx
mov r11, 0x30 
bzhi r13, r10, r11
shrd r12, r9, 52
lea r13, [ r13 + r12 ]
mov [ r8 + 0x20 ], r13
mov [ r8 + 0x8 ], rbp
mov [ r8 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0697
; seed 0757023763997057 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2179788 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=152, initial num_batches=31): 140036 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06424294472673489
; number reverted permutation / tried permutation: 71202 / 90172 =78.962%
; number reverted decision / tried decision: 52572 / 89827 =58.526%
; validated in 0.593s
