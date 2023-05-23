SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x10 ]
lea rdx, [r11 + r11]
mulx rcx, r11, [ rsi + 0x20 ]
mov r8, rax
shrd r8, r10, 52
mulx r10, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, rbx
mov [ rsp - 0x68 ], r13
mulx r13, rbx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov r15, r14
shl r15, 0x1
imul r14, [ rsi + 0x8 ], 0x2
xchg rdx, r14
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r8
xor r8, r8
adox rdi, rbx
adox r13, r15
mov rbx, 0x34 
bzhi r15, rax, rbx
mov rax, 0x1000003d10 
xchg rdx, r15
mulx rbx, r8, rax
mov rdx, r14
mulx rax, r14, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r12
mulx r12, r14, rdx
adox r14, r11
adox rcx, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r11, rdx
test al, al
adox r8, rdi
adox r13, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, rdi, r15
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x20 ], r12
mov r12, r8
and r12, rdx
adox r9, rdi
adox rbx, r10
mov rdx, [ rsi + 0x10 ]
mulx rdi, r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r11
mulx r11, r12, r15
adcx r10, r12
adcx r11, rdi
xor rdx, rdx
adox r10, rbp
adox r11, [ rsp - 0x28 ]
shrd r8, r13, 52
mov rbp, 0x1000003d10 
mov rdx, [ rsp - 0x40 ]
mulx r13, r15, rbp
xor rdx, rdx
adox r8, r10
adox r11, rdx
adcx r15, r8
adcx r11, r13
mov rdi, r15
shrd rdi, r11, 52
mov r12, 0xfffffffffffff 
and r15, r12
adox rdi, r9
adox rbx, rdx
mov r9, rdi
shrd r9, rbx, 52
and rdi, r12
shl rdi, 4
mov r10, r15
shr r10, 48
mov rdx, [ rsi + 0x0 ]
mulx r8, r13, rdx
lea rdi, [ rdi + r10 ]
mov rdx, 0x1000003d1 
mulx rbx, r11, rdi
mov r10, 0xffffffffffff 
and r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rdi, rax
adox r9, r14
mov rdx, 0x0 
adox rcx, rdx
adcx r11, r13
adcx r8, rbx
mov rax, r11
and rax, r12
mov r14, r9
shrd r14, rcx, 52
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rax
and r9, r12
mov rdx, [ rsi + 0x20 ]
mulx rcx, rbx, [ rsp - 0x48 ]
mov rdx, rbp
mulx rax, rbp, r9
shrd r11, r8, 52
add r14, rbx
adc rcx, 0x0
mov r8, r14
and r8, r12
mov r9, [ rsp - 0x10 ]
adox r9, [ rsp - 0x30 ]
mov rbx, [ rsp - 0x20 ]
adox rbx, [ rsp - 0x38 ]
adcx r11, rdi
adc r10, 0x0
add rbp, r11
adcx r10, rax
mulx rax, rdi, r8
mov r8, rbp
and r8, r12
shrd r14, rcx, 52
shrd rbp, r10, 52
mov [ r13 + 0x8 ], r8
xor rcx, rcx
adox rbp, r9
adox rbx, rcx
mulx r11, r9, r14
adcx rdi, rbp
adcx rbx, rax
mov r10, rdi
shrd r10, rbx, 52
add r10, [ rsp - 0x18 ]
add r9, r10
adc r11, 0x0
mov rax, r9
and rax, r12
and rdi, r12
shrd r9, r11, 52
lea r15, [ r15 + r9 ]
mov [ r13 + 0x20 ], r15
mov [ r13 + 0x10 ], rdi
mov [ r13 + 0x18 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 0.9742
; seed 3093611607776169 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5798 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=244, initial num_batches=31): 445 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07675060365643326
; number reverted permutation / tried permutation: 405 / 496 =81.653%
; number reverted decision / tried decision: 313 / 503 =62.227%
; validated in 0.27s
