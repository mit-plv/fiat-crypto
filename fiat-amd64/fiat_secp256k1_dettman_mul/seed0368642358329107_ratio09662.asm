SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 200
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], rbx
mulx rbx, r9, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r14
mulx r14, r13, [ rax + 0x10 ]
test al, al
adox rbp, r15
adox rdi, r12
mov rdx, [ rsi + 0x20 ]
mulx r15, r12, [ rax + 0x20 ]
mov rdx, r12
shrd rdx, r15, 52
mov r15, 0xfffffffffffff 
and r12, r15
mov r15, 0x1000003d10 
xchg rdx, r15
mov [ rsp - 0x8 ], rdi
mov [ rsp + 0x0 ], rbp
mulx rbp, rdi, r12
mov [ rsp + 0x8 ], rbp
mulx rbp, r12, r15
mov rdx, [ rax + 0x0 ]
mov [ rsp + 0x10 ], rbp
mulx rbp, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x18 ], r12
mov [ rsp + 0x20 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x28 ], rbx
mov [ rsp + 0x30 ], r9
mulx r9, rbx, [ rax + 0x8 ]
adox rcx, r12
adox rdi, r8
adcx r15, rbx
adcx r9, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx rbx, r12, [ rax + 0x0 ]
xor rdx, rdx
adox rcx, r8
adox rbp, rdi
mov rdx, [ rsi + 0x8 ]
mulx r8, rdi, [ rax + 0x20 ]
adcx r12, r10
adcx r11, rbx
xor rdx, rdx
adox rcx, rdi
adox r8, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbx, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx rdi, rbp, [ rsi + 0x20 ]
adcx r12, r13
adcx r14, r11
mov rdx, [ rsi + 0x20 ]
mulx r11, r13, [ rax + 0x0 ]
xor rdx, rdx
adox r15, [ rsp + 0x30 ]
adox r9, [ rsp + 0x28 ]
adcx r15, r10
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, [ rax + 0x20 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x38 ], r14
mov [ rsp + 0x40 ], r12
mulx r12, r14, [ rsi + 0x18 ]
test al, al
adox r13, r14
adox r12, r11
adcx rbp, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
mov rdx, r15
xor r11, r11
adox rdx, [ rsp + 0x20 ]
adox rbx, [ rsp + 0x8 ]
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r14, [ rax + 0x18 ]
mov rdx, r15
shrd rdx, rbx, 52
mov rbx, 0xfffffffffffff 
and r15, rbx
adox r13, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
adcx r13, r14
adcx r11, r12
add r13, [ rsp - 0x40 ]
adcx r11, [ rsp - 0x48 ]
add rdx, r13
adc r11, 0x0
mov r14, rdx
test al, al
adox r14, [ rsp + 0x18 ]
adox r11, [ rsp + 0x10 ]
mov r12, r14
and r12, rbx
shrd r14, r11, 52
mov r13, r12
shr r13, 48
xor rdx, rdx
adox r14, rcx
adox r8, rdx
mov rcx, r14
shrd rcx, r8, 52
xor r11, r11
adox rbp, r10
adox r9, rdi
mov rdx, [ rax + 0x0 ]
mulx rdi, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r8, [ rax + 0x20 ]
adcx rcx, rbp
adc r9, 0x0
mov rdx, rcx
shrd rdx, r9, 52
and r14, rbx
shl r14, 4
mov rbp, r8
test al, al
adox rbp, [ rsp - 0x10 ]
adox r11, [ rsp - 0x18 ]
adcx rdx, rbp
adc r11, 0x0
mov r8, rdx
shrd r8, r11, 52
and rdx, rbx
and rcx, rbx
lea r14, [ r14 + r13 ]
mov r13, 0x1000003d1 
xchg rdx, r13
mulx rbp, r9, r14
adox r9, r10
adox rdi, rbp
mov r10, 0x1000003d10 
mov rdx, r10
mulx r11, r10, r8
mulx r14, r8, rcx
mov rcx, r9
shrd rcx, rdi, 52
and r9, rbx
adox rcx, [ rsp + 0x0 ]
mov rbp, [ rsp - 0x8 ]
mov rdi, 0x0 
adox rbp, rdi
adcx r8, rcx
adcx rbp, r14
mov r14, r8
and r14, rbx
shrd r8, rbp, 52
mulx rbp, rcx, r13
test al, al
adox r8, [ rsp + 0x40 ]
mov r13, [ rsp + 0x38 ]
adox r13, rdi
adcx rcx, r8
adcx r13, rbp
mov rbp, rcx
and rbp, rbx
shrd rcx, r13, 52
lea r15, [ r15 + rcx ]
xor r8, r8
adox r10, r15
adox r11, r8
mov rdi, r10
shrd rdi, r11, 52
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r14
mov r14, 0xffffffffffff 
and r12, r14
lea r12, [ r12 + rdi ]
mov [ r13 + 0x20 ], r12
mov [ r13 + 0x10 ], rbp
and r10, rbx
mov [ r13 + 0x18 ], r10
mov [ r13 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 0.9662
; seed 0368642358329107 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 9025 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=206, initial num_batches=31): 571 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06326869806094183
; number reverted permutation / tried permutation: 355 / 515 =68.932%
; number reverted decision / tried decision: 213 / 484 =44.008%
; validated in 0.474s
