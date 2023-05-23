SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x78 ], rbp
mov rbp, r9
and rbp, rdx
shrd r9, rbx, 52
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
test al, al
adox r10, rbx
adox r12, r11
adcx r10, r13
adcx r14, r12
test al, al
adox r10, rcx
adox r8, r14
mov rdx, 0x1000003d10 
mulx rcx, r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r12, r13, [ rsi + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x58 ], r15
mulx r15, r14, r9
adcx r11, r10
adcx r8, rcx
xor r9, r9
adox r13, rbp
adox rbx, r12
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ rax + 0x18 ]
adcx r13, r10
adcx rcx, rbx
add r13, rbp
adcx r12, rcx
mov rdx, [ rsi + 0x0 ]
mulx r10, rbx, [ rax + 0x20 ]
mov rdx, r11
shrd rdx, r8, 52
add r13, rbx
adcx r10, r12
xor r8, r8
adox rdx, r13
adox r10, r8
adcx r14, rdx
adcx r10, r15
mov r9, r14
shrd r9, r10, 52
mov rdx, [ rax + 0x8 ]
mulx rbp, r15, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx r12, rcx, [ rsi + 0x18 ]
xor rdx, rdx
adox r15, rcx
adox r12, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbx, r8, [ rax + 0x18 ]
adcx r15, r8
adcx rbx, r12
mov rdx, [ rax + 0x20 ]
mulx r10, r13, [ rsi + 0x8 ]
add r15, r13
adcx r10, rbx
mov rdx, 0xfffffffffffff 
and r14, rdx
adox r9, r15
mov rbp, 0x0 
adox r10, rbp
mov rcx, r9
and rcx, rdx
mov r12, 0xffffffffffff 
mov r8, r14
and r8, r12
shl rcx, 4
shrd r9, r10, 52
mov rdx, [ rax + 0x18 ]
mulx r13, rbx, [ rsi + 0x18 ]
shr r14, 48
mov rdx, [ rax + 0x20 ]
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r12, rbp, [ rax + 0x10 ]
xor rdx, rdx
adox rbp, rbx
adox r13, r12
adcx rbp, r15
adcx r10, r13
lea rcx, [ rcx + r14 ]
xor rbx, rbx
adox r9, rbp
adox r10, rbx
mov rdx, 0x1000003d1 
mulx r15, r14, rcx
mov r12, r9
shrd r12, r10, 52
mov rdx, [ rax + 0x0 ]
mulx rbp, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
test al, al
adox r14, r13
adox rbp, r15
mov rdx, r14
shrd rdx, rbp, 52
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbp, r13, [ rax + 0x8 ]
test al, al
adox rcx, rbx
adox rdi, r10
mov rdx, [ rsi + 0x10 ]
mulx rbx, r10, [ rax + 0x0 ]
adcx r15, rcx
adc rdi, 0x0
add r10, r13
adcx rbp, rbx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, 0xfffffffffffff 
and r9, rdx
adox r10, rbx
adox r8, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbx, rbp, [ rax + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], r10
mulx r10, r8, r9
adcx r8, r15
adcx rdi, r10
add r13, rbp
adcx rbx, rcx
add r12, r13
adc rbx, 0x0
mov r15, 0xfffffffffffff 
mov rcx, r12
and rcx, r15
shrd r12, rbx, 52
mulx rbp, r9, rcx
mov r10, r8
shrd r10, rdi, 52
and r11, r15
mulx r13, rdi, r12
adox r10, [ rsp - 0x38 ]
mov rbx, [ rsp - 0x40 ]
mov rcx, 0x0 
adox rbx, rcx
adcx r9, r10
adcx rbx, rbp
mov r12, r9
shrd r12, rbx, 52
lea r11, [ r11 + r12 ]
and r9, r15
adox rdi, r11
adox r13, rcx
mov rbp, rdi
shrd rbp, r13, 52
add rbp, [ rsp - 0x48 ]
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x10 ], r9
and rdi, r15
mov [ r10 + 0x18 ], rdi
and r14, r15
mov [ r10 + 0x0 ], r14
and r8, r15
mov [ r10 + 0x20 ], rbp
mov [ r10 + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.3610
; seed 3833716287073554 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 892151 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=260, initial num_batches=31): 80726 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09048468252571594
; number reverted permutation / tried permutation: 72622 / 90210 =80.503%
; number reverted decision / tried decision: 53957 / 89789 =60.093%
; validated in 0.283s
