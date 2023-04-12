SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r15, rbx
adox r9, rdi
mov rbx, 0xfffffffffffff 
mov rdi, rcx
and rdi, rbx
mov rdx, 0x1000003d10 
mov [ rsp - 0x18 ], r12
mulx r12, rbx, rdi
adox r15, r13
adox r14, r9
shrd rcx, r8, 52
mov rdx, [ rax + 0x8 ]
mulx r13, r8, [ rsi + 0x10 ]
test al, al
adox r10, r8
adox r13, r11
mov rdx, [ rax + 0x10 ]
mulx r9, r11, [ rsi + 0x8 ]
adcx r10, r11
adcx r9, r13
mov rdx, [ rax + 0x18 ]
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r11, r13, [ rax + 0x0 ]
test al, al
adox r10, rdi
adox r8, r9
mov rdx, [ rsi + 0x10 ]
mulx rdi, r9, [ rax + 0x10 ]
adcx rbx, r10
adcx r8, r12
mov rdx, [ rax + 0x18 ]
mulx r10, r12, [ rsi + 0x8 ]
mov rdx, rbx
shrd rdx, r8, 52
add r13, rbp
adcx r11, [ rsp - 0x18 ]
xor rbp, rbp
adox r13, r9
adox rdi, r11
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r8, [ rax + 0x20 ]
adcx r13, r12
adcx r10, rdi
test al, al
adox r13, r8
adox r11, r10
mov rdx, 0x1000003d10 
mulx rdi, r12, rcx
adcx r9, r13
adc r11, 0x0
xor rcx, rcx
adox r12, r9
adox r11, rdi
mov rbp, r12
shrd rbp, r11, 52
mov r8, 0xfffffffffffff 
and r12, r8
mov rdx, [ rax + 0x20 ]
mulx r13, r10, [ rsi + 0x8 ]
mov rdx, r12
shr rdx, 48
xor rdi, rdi
adox r15, r10
adox r13, r14
adcx rbp, r15
adc r13, 0x0
mov rcx, rdx
mov rdx, [ rax + 0x18 ]
mulx r9, r14, [ rsi + 0x18 ]
mov rdx, rbp
shrd rdx, r13, 52
mov r11, r14
add r11, [ rsp - 0x20 ]
adcx r9, [ rsp - 0x28 ]
mov r10, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, r15, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r15
adox r13, r9
adcx r10, r11
adc r13, 0x0
and rbp, r8
shl rbp, 4
mov rdx, [ rax + 0x0 ]
mulx r14, rdi, [ rsi + 0x0 ]
lea rbp, [ rbp + rcx ]
mov rdx, 0x1000003d1 
mulx r9, rcx, rbp
mov rdx, [ rax + 0x18 ]
mulx r11, r15, [ rsi + 0x20 ]
add rcx, rdi
adcx r14, r9
mov rdx, r10
and rdx, r8
mov rdi, 0x1000003d10 
mulx r9, rbp, rdi
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, [ rax + 0x20 ]
shrd r10, r13, 52
add r15, rdi
adcx r8, r11
add r10, r15
adc r8, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r11, r13, [ rax + 0x8 ]
mov rdx, rcx
shrd rdx, r14, 52
mov r14, r13
xor rdi, rdi
adox r14, [ rsp - 0x30 ]
adox r11, [ rsp - 0x38 ]
mov r15, r10
shrd r15, r8, 52
xor r8, r8
adox rdx, r14
adox r11, r8
mov rdi, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rax + 0x8 ]
mov rdx, r13
adcx rdx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], r15
mulx r15, r8, [ rax + 0x10 ]
xor rdx, rdx
adox r13, r8
adox r15, r14
adcx rbp, rdi
adcx r11, r9
mov r9, 0x34 
bzhi rdi, rbp, r9
shrd rbp, r11, 52
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x8 ], rdi
xor r8, r8
adox rbp, r13
adox r15, r8
bzhi rdx, r10, r9
mov r10, 0x1000003d10 
mulx r11, r13, r10
adox r13, rbp
adox r15, r11
mov rdi, r13
shrd rdi, r15, 52
bzhi rbp, rbx, r9
mov rdx, [ rsp - 0x10 ]
mulx r11, rbx, r10
lea rbp, [ rbp + rdi ]
mov rdx, 0x30 
bzhi r15, r12, rdx
adox rbx, rbp
adox r11, r8
mov r12, rbx
shrd r12, r11, 52
bzhi rdi, rbx, r9
mov [ r14 + 0x18 ], rdi
lea r15, [ r15 + r12 ]
mov [ r14 + 0x20 ], r15
bzhi rbp, rcx, r9
bzhi rcx, r13, r9
mov [ r14 + 0x10 ], rcx
mov [ r14 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1215
; seed 2397821302094452 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1203093 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=219, initial num_batches=31): 83659 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06953660273977157
; number reverted permutation / tried permutation: 68443 / 89316 =76.630%
; number reverted decision / tried decision: 52223 / 90683 =57.589%
; validated in 0.495s
