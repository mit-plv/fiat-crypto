SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
test al, al
adox rbp, r13
adox r14, r12
mov rdx, [ rsi + 0x20 ]
mulx r13, r12, [ rax + 0x18 ]
adcx rcx, r10
adcx r11, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rsi + 0x8 ]
test al, al
adox rcx, r10
adox r8, r11
mov rdx, [ rsi + 0x20 ]
mulx r10, r11, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], rcx
mulx rcx, r8, [ rsi + 0x0 ]
adcx rbp, r13
adcx r12, r14
add rbp, r8
adcx rcx, r12
mov rdx, 0xfffffffffffff 
mov r14, r11
and r14, rdx
mov r13, 0x1000003d10 
mov rdx, r13
mulx r8, r13, r14
adox r13, rbp
adox rcx, r8
mov rdx, [ rsi + 0x20 ]
mulx rbp, r12, [ rax + 0x0 ]
mov rdx, r13
shrd rdx, rcx, 52
xor r14, r14
adox r12, r15
adox rdi, rbp
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, [ rax + 0x10 ]
adcx r12, r8
adcx rcx, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mulx r14, r8, [ rsi + 0x0 ]
add r12, rbp
adcx rdi, rcx
test al, al
adox r12, r8
adox r14, rdi
adcx r15, r12
adc r14, 0x0
shrd r11, r10, 52
mov rdx, 0x1000003d10 
mulx rcx, r10, r11
add r10, r15
adcx r14, rcx
mov rbp, r10
shrd rbp, r14, 52
mov rdx, [ rax + 0x8 ]
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox r8, r12
adox r15, rdi
mov rdx, [ rax + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
adcx r8, r11
adcx rcx, r15
mov rdx, [ rsi + 0x8 ]
mulx rdi, r14, [ rax + 0x20 ]
xor rdx, rdx
adox r8, r14
adox rdi, rcx
adcx rbp, r8
adc rdi, 0x0
mov r12, 0xfffffffffffff 
mov r15, rbp
and r15, r12
shl r15, 4
and r10, r12
mov r11, r10
shr r11, 48
mov rcx, 0xffffffffffff 
and r10, rcx
mov rdx, [ rsi + 0x20 ]
mulx r8, r14, [ rax + 0x10 ]
lea r15, [ r15 + r11 ]
adox r14, r9
adox rbx, r8
mov rdx, [ rsi + 0x10 ]
mulx r11, r9, [ rax + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, 0x1000003d1 
mov [ rsp - 0x28 ], r10
mulx r10, r12, r15
shrd rbp, rdi, 52
xor rdi, rdi
adox r14, r9
adox r11, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r15, [ rax + 0x0 ]
adcx r12, r15
adcx rbx, r10
mov rdx, [ rax + 0x0 ]
mulx r10, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rbp, r14
adox r11, rdx
mov rdi, rbp
shrd rdi, r11, 52
mov r14, r8
add r14, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x48 ]
test al, al
adox rdi, r14
adox rcx, rdx
mov r8, r12
shrd r8, rbx, 52
mov r15, 0xfffffffffffff 
mov rbx, rdi
and rbx, r15
mov rdx, [ rax + 0x8 ]
mulx r14, r11, [ rsi + 0x0 ]
and rbp, r15
adox r9, r11
adox r14, r10
adcx r8, r9
adc r14, 0x0
mov rdx, 0x1000003d10 
mulx r11, r10, rbp
xor rbp, rbp
adox r10, r8
adox r14, r11
mov r9, r10
shrd r9, r14, 52
mulx r11, r8, rbx
and r10, r15
and r13, r15
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], r10
adox r9, [ rsp - 0x30 ]
mov r14, [ rsp - 0x38 ]
adox r14, rbp
adcx r8, r9
adcx r14, r11
mov r11, r8
and r11, r15
shrd r8, r14, 52
lea r13, [ r13 + r8 ]
mov [ rbx + 0x10 ], r11
shrd rdi, rcx, 52
and r12, r15
mov [ rbx + 0x0 ], r12
mulx r10, rcx, rdi
adox rcx, r13
adox r10, rbp
mov r9, rcx
shrd r9, r10, 52
add r9, [ rsp - 0x28 ]
and rcx, r15
mov [ rbx + 0x18 ], rcx
mov [ rbx + 0x20 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3085
; seed 3286769594682671 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 889878 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=260, initial num_batches=31): 80876 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09088436841904171
; number reverted permutation / tried permutation: 73777 / 90129 =81.857%
; number reverted decision / tried decision: 53607 / 89870 =59.649%
; validated in 0.288s
