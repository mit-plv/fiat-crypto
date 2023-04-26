SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x20 ]
mov rdx, r15
shrd rdx, rdi, 52
mov rdi, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, 0xfffffffffffff 
and r15, rdx
adox r13, r12
adox rbp, r14
mov rdx, [ rax + 0x8 ]
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r13
mulx r13, rbp, [ rax + 0x0 ]
adcx rbp, r14
adcx r12, r13
xor rdx, rdx
adox r9, r10
adox r11, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r10, [ rsi + 0x0 ]
adcx rbp, rcx
adcx r8, r12
add rbp, r10
adcx rbx, r8
mov rdx, 0x1000003d10 
mulx r14, rcx, r15
xor r15, r15
adox rcx, rbp
adox rbx, r14
mov r13, rcx
shrd r13, rbx, 52
mov rdx, [ rax + 0x18 ]
mulx r10, r12, [ rsi + 0x8 ]
mov rdx, 0x1000003d10 
mulx rbp, r8, rdi
xor rdi, rdi
adox r9, [ rsp - 0x40 ]
adox r11, [ rsp - 0x48 ]
adcx r9, r12
adcx r10, r11
mov rdx, [ rax + 0x20 ]
mulx r14, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r15
adox r14, r10
adcx r13, r9
adc r14, 0x0
xor rdi, rdi
adox r8, r13
adox r14, rbp
mov rdx, [ rax + 0x8 ]
mulx r12, rbx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r11, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r10, [ rsi + 0x18 ]
adcx rbx, r10
adcx r15, r12
mov rdx, [ rsi + 0x8 ]
mulx r13, r9, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
and rcx, rdx
adox rbx, rbp
adox r11, r15
adcx rbx, r9
adcx r13, r11
mov r12, r8
shrd r12, r14, 52
test al, al
adox r12, rbx
adox r13, rdi
mov r14, r12
and r14, rdx
shrd r12, r13, 52
and r8, rdx
mov rdx, [ rax + 0x18 ]
mulx r10, rbp, [ rsi + 0x18 ]
mov rdx, 0x30 
bzhi r15, r8, rdx
shr r8, 48
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, rbx, [ rax + 0x10 ]
shl r14, 4
lea r14, [ r14 + r8 ]
xor rdx, rdx
adox rbx, rbp
adox r10, r13
mov rdx, [ rsi + 0x0 ]
mulx rbp, rdi, [ rax + 0x10 ]
mov rdx, 0x1000003d1 
mulx r13, r8, r14
mov r14, rdi
adcx r14, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x38 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x28 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, rdi
adox r15, r10
adcx r12, rbx
adc r15, 0x0
mov r10, r12
shrd r10, r15, 52
mov rdx, [ rax + 0x0 ]
mulx rbx, rdi, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r15, [ rax + 0x20 ]
add r8, r9
adcx r11, r13
mov rdx, r8
shrd rdx, r11, 52
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r13, [ rax + 0x8 ]
test al, al
adox rdi, r13
adox r11, rbx
adcx r9, rdi
adc r11, 0x0
mov rdx, [ rsi + 0x20 ]
mulx r13, rbx, [ rax + 0x18 ]
xor rdx, rdx
adox rbx, r15
adox rcx, r13
adcx r10, rbx
adc rcx, 0x0
mov r15, 0xfffffffffffff 
mov rdi, r10
and rdi, r15
shrd r10, rcx, 52
and r12, r15
mov r13, 0x1000003d10 
mov rdx, r13
mulx rbx, r13, r12
mulx r12, rcx, rdi
adox r13, r9
adox r11, rbx
mov r9, r13
and r9, r15
shrd r13, r11, 52
and r8, r15
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], r8
adox r13, r14
mov rbx, 0x0 
adox rbp, rbx
adcx rcx, r13
adcx rbp, r12
mov r14, rcx
shrd r14, rbp, 52
mulx r11, r12, r10
mov [ rdi + 0x8 ], r9
add r14, [ rsp - 0x20 ]
xor r10, r10
adox r12, r14
adox r11, r10
and rcx, r15
mov [ rdi + 0x10 ], rcx
mov rbx, r12
shrd rbx, r11, 52
add rbx, [ rsp - 0x28 ]
and r12, r15
mov [ rdi + 0x18 ], r12
mov [ rdi + 0x20 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1480
; seed 0344365453752609 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1229135 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=225, initial num_batches=31): 83922 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06827728443173452
; number reverted permutation / tried permutation: 70175 / 90389 =77.637%
; number reverted decision / tried decision: 52551 / 89610 =58.644%
; validated in 0.467s
