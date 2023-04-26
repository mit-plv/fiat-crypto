SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, rcx
shrd rdx, r8, 52
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x38 ], r11
mulx r11, r8, [ rsi + 0x18 ]
test al, al
adox r8, r9
adox rbx, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r9, [ rax + 0x0 ]
adcx r9, r15
adcx rdi, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, r15, [ rax + 0x10 ]
test al, al
adox r8, r15
adox r11, rbx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbx, [ rax + 0x0 ]
adcx rbx, r13
adcx r14, r15
mov rdx, [ rax + 0x18 ]
mulx r15, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r13
adox r15, r11
mov rdx, [ rsi + 0x0 ]
mulx r13, r11, [ rax + 0x20 ]
adcx rbx, rdi
adcx r9, r14
mov rdx, 0xfffffffffffff 
and rcx, rdx
mov r14, 0x1000003d10 
mov rdx, rcx
mulx rdi, rcx, r14
adox rcx, r8
adox r15, rdi
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, [ rax + 0x18 ]
adcx rbx, r8
adcx rdi, r9
mov rdx, rcx
shrd rdx, r15, 52
test al, al
adox rbx, r11
adox r13, rdi
adcx rdx, rbx
adc r13, 0x0
add r12, rdx
adcx r13, rbp
mov rdx, [ rax + 0x20 ]
mulx r11, rbp, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mulx r15, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mulx rdi, r8, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
mulx r14, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], r13
mulx r13, r10, [ rax + 0x18 ]
add r8, r9
adcx r15, rdi
test al, al
adox r8, rbx
adox r14, r15
adcx r8, rbp
adcx r11, r14
mov rdx, [ rsp - 0x18 ]
mov rbp, r12
shrd rbp, rdx, 52
xor rdx, rdx
adox rbp, r8
adox r11, rdx
mov r9, rbp
shrd r9, r11, 52
mov rdx, [ rsi + 0x10 ]
mulx rbx, rdi, [ rax + 0x20 ]
mov rdx, r10
add rdx, [ rsp - 0x20 ]
adcx r13, [ rsp - 0x38 ]
mov r10, 0xfffffffffffff 
and rbp, r10
adox rdx, rdi
adox rbx, r13
adcx r9, rdx
adc rbx, 0x0
and r12, r10
mov r15, r12
shr r15, 48
shl rbp, 4
lea rbp, [ rbp + r15 ]
mov r14, r9
shrd r14, rbx, 52
and r9, r10
mov rdx, [ rsi + 0x20 ]
mulx r11, r8, [ rax + 0x18 ]
mov rdx, 0x1000003d1 
mulx r13, rdi, rbp
adox rdi, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov rbx, rdi
and rbx, r10
mov r15, 0xffffffffffff 
and r12, r15
mov rdx, [ rax + 0x20 ]
mulx r15, rbp, [ rsi + 0x18 ]
adox r8, rbp
adox r15, r11
adcx r14, r8
adc r15, 0x0
mov rdx, r14
shrd rdx, r15, 52
mov r11, rdx
mov rdx, [ rax + 0x0 ]
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r10, r15, [ rax + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], rbx
mulx rbx, r12, r11
mov r11, 0xfffffffffffff 
and r14, r11
adox rbp, r15
adox r10, r8
shrd rdi, r13, 52
add rdi, rbp
adc r10, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, [ rax + 0x10 ]
mov rdx, 0x1000003d10 
mulx rbp, r15, r9
xor r9, r9
adox r15, rdi
adox r10, rbp
mov rdi, r13
adcx rdi, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x30 ]
mov r13, r15
shrd r13, r10, 52
mulx r10, rbp, r14
test al, al
adox r13, rdi
adox r8, r9
adcx rbp, r13
adcx r8, r10
and rcx, r11
mov r14, rbp
shrd r14, r8, 52
lea rcx, [ rcx + r14 ]
xor rdi, rdi
adox r12, rcx
adox rbx, rdi
and rbp, r11
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rbp
mov r10, r12
shrd r10, rbx, 52
mov r13, [ rsp - 0x8 ]
mov [ r9 + 0x0 ], r13
add r10, [ rsp - 0x10 ]
mov [ r9 + 0x20 ], r10
and r15, r11
and r12, r11
mov [ r9 + 0x18 ], r12
mov [ r9 + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0469
; seed 3714386728258788 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 993126 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=181, initial num_batches=31): 71864 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07236141234848348
; number reverted permutation / tried permutation: 69222 / 90159 =76.778%
; number reverted decision / tried decision: 46813 / 89840 =52.107%
; validated in 0.312s
