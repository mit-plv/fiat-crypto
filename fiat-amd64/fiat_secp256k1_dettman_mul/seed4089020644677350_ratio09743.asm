SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 184
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, rcx
shrd rdx, r8, 52
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
and rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r12
mulx r12, rbp, [ rax + 0x10 ]
adox rbp, r10
adox r11, r12
mov rdx, [ rsi + 0x18 ]
mulx r12, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], rbp
mulx rbp, r11, [ rax + 0x0 ]
adcx r9, r10
adcx r12, rbx
xor rdx, rdx
adox r11, r15
adox rdi, rbp
mov rdx, [ rax + 0x0 ]
mulx r15, rbx, [ rsi + 0x10 ]
adcx rbx, r13
adcx r14, r15
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, [ rax + 0x10 ]
mov rdx, 0x1000003d10 
mulx r15, rbp, rcx
xor rcx, rcx
adox r9, r13
adox r10, r12
mulx r13, r12, r8
mov rdx, [ rax + 0x18 ]
mulx rcx, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], rbx
mulx rbx, r14, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adcx r14, rdi
adcx r11, rbx
mov rdx, [ rax + 0x8 ]
mulx rdi, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r13
mov [ rsp + 0x10 ], r12
mulx r12, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r15
mov [ rsp + 0x20 ], rbp
mulx rbp, r15, [ rsi + 0x8 ]
test al, al
adox r14, r13
adox r12, r11
adcx r8, [ rsp - 0x30 ]
adcx rcx, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, [ rax + 0x0 ]
xor rdx, rdx
adox r11, rbx
adox rdi, r13
mov rdx, [ rax + 0x20 ]
mulx r13, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], r8
mulx r8, rcx, [ rax + 0x18 ]
adcx r9, rcx
adcx r8, r10
test al, al
adox r11, r15
adox rbp, rdi
mov rdx, [ rax + 0x18 ]
mulx r15, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x20 ]
mulx rcx, rdi, [ rsi + 0x8 ]
adcx r11, r10
adcx r15, rbp
mov rdx, r11
add rdx, [ rsp + 0x20 ]
adcx r15, [ rsp + 0x18 ]
mov rbp, rdx
shrd rbp, r15, 52
xor r10, r10
adox r9, rbx
adox r13, r8
adcx rbp, r9
adc r13, 0x0
test al, al
adox r14, rdi
adox rcx, r12
mov r12, rbp
adcx r12, [ rsp + 0x10 ]
adcx r13, [ rsp + 0x8 ]
mov rbx, 0xfffffffffffff 
mov r8, r12
and r8, rbx
shrd r12, r13, 52
add r12, r14
adc rcx, 0x0
mov rdi, r12
and rdi, rbx
mov r11, rdx
mov rdx, [ rax + 0x20 ]
mulx r9, r15, [ rsi + 0x10 ]
shl rdi, 4
mov rdx, r15
test al, al
adox rdx, [ rsp - 0x20 ]
adox r9, [ rsp - 0x28 ]
mov rbp, r8
shr rbp, 48
shrd r12, rcx, 52
lea rdi, [ rdi + rbp ]
test al, al
adox r12, rdx
adox r9, r10
mov r14, r12
and r14, rbx
shrd r12, r9, 52
mov rdx, [ rax + 0x0 ]
mulx rcx, r13, [ rsi + 0x0 ]
test al, al
adox r12, [ rsp + 0x30 ]
mov rdx, [ rsp + 0x28 ]
adox rdx, r10
mov r15, 0x1000003d1 
xchg rdx, r15
mulx r9, rbp, rdi
adcx rbp, r13
adcx rcx, r9
mov rdi, rbp
shrd rdi, rcx, 52
mov r13, r12
and r13, rbx
mov r9, 0x1000003d10 
mov rdx, r9
mulx rcx, r9, r14
adox rdi, [ rsp + 0x0 ]
mov r14, [ rsp - 0x8 ]
adox r14, r10
adcx r9, rdi
adcx r14, rcx
and rbp, rbx
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], rbp
mov rdi, [ rsp - 0x40 ]
mov rbp, rdi
adox rbp, [ rsp - 0x10 ]
mov rbx, [ rsp - 0x48 ]
adox rbx, [ rsp - 0x18 ]
mov rdi, r9
shrd rdi, r14, 52
xor r14, r14
adox rdi, rbp
adox rbx, r14
mov r10, 0xfffffffffffff 
and r9, r10
mov [ rcx + 0x8 ], r9
mulx r9, rbp, r13
adox rbp, rdi
adox rbx, r9
mov r13, rbp
shrd r13, rbx, 52
mov rdi, 0xffffffffffff 
and r8, rdi
shrd r12, r15, 52
mulx r9, r15, r12
and r11, r10
lea r11, [ r11 + r13 ]
adox r15, r11
adox r9, r14
mov rbx, r15
and rbx, r10
mov [ rcx + 0x18 ], rbx
shrd r15, r9, 52
and rbp, r10
mov [ rcx + 0x10 ], rbp
lea r8, [ r8 + r15 ]
mov [ rcx + 0x20 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 0.9743
; seed 4089020644677350 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8375 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=183, initial num_batches=31): 511 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06101492537313433
; number reverted permutation / tried permutation: 304 / 460 =66.087%
; number reverted decision / tried decision: 217 / 539 =40.260%
; validated in 0.452s
