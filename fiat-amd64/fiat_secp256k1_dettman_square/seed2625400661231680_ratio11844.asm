SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
mov rax, [ rsi + 0x0 ]
mov r11, rax
shl r11, 0x1
mov rdx, [ rsi + 0x20 ]
mulx rcx, rax, rdx
mov rdx, r11
mulx r8, r11, [ rsi + 0x18 ]
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
mov rdx, r10
mov [ rsp - 0x70 ], r12
mulx r12, r10, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
xor r13, r13
adox r10, r11
adox r8, r12
mov r11, [ rsi + 0x10 ]
lea r12, [r11 + r11]
mov r11, 0xfffffffffffff 
mov r13, rax
and r13, r11
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r15
mulx r15, r13, rdx
adox r11, r10
adox r8, rdi
shrd rax, rcx, 52
mov rdx, [ rsi + 0x20 ]
mulx r10, rcx, r9
mov rdx, 0x1000003d10 
mov [ rsp - 0x40 ], r14
mulx r14, rdi, rax
add r13, rbx
adcx rbp, r15
mov rbx, r11
shrd rbx, r8, 52
xor r15, r15
adox r13, rcx
adox r10, rbp
mov rdx, [ rsi + 0x8 ]
mulx rax, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, r12
mulx rbp, r12, [ rsi + 0x18 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rax
mov [ rsp - 0x30 ], r8
mulx r8, rax, rcx
xor rdx, rdx
adox r12, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
adcx rbx, r13
adc r10, 0x0
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, rdx
add rdi, rbx
adcx r10, r14
mov rdx, [ rsi + 0x20 ]
mulx rbx, r14, r15
xor rdx, rdx
adox r13, r14
adox rbx, rcx
mov r15, 0xfffffffffffff 
mov rcx, rdi
and rcx, r15
shrd rdi, r10, 52
add rdi, r12
adc rbp, 0x0
mov r12, rdi
shrd r12, rbp, 52
and rdi, r15
adox r12, r13
adox rbx, rdx
mov r10, 0xffffffffffff 
mov r14, rcx
and r14, r10
shl rdi, 4
shr rcx, 48
mov r13, r12
shrd r13, rbx, 52
lea rdi, [ rdi + rcx ]
and r12, r15
adox r13, rax
adox r8, rdx
mov rax, 0x1000003d10 
mov rdx, rax
mulx rbp, rax, r12
mov rbx, r13
and rbx, r15
shrd r13, r8, 52
mulx r12, rcx, rbx
mulx rbx, r8, r13
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, rdx
mov rdx, 0x1000003d1 
mov [ rsp - 0x28 ], r14
mulx r14, r15, rdi
xor rdi, rdi
adox r15, r13
adox r10, r14
mov r13, r15
shrd r13, r10, 52
mov rdx, r9
mulx r14, r9, [ rsi + 0x8 ]
mov r10, 0xfffffffffffff 
and r15, r10
adox r13, r9
adox r14, rdi
adcx rax, r13
adcx r14, rbp
mov rbp, rax
shrd rbp, r14, 52
and rax, r10
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r15
mulx r13, r15, [ rsi + 0x10 ]
mov [ r9 + 0x8 ], rax
and r11, r10
mov rdx, r15
adox rdx, [ rsp - 0x30 ]
adox r13, [ rsp - 0x38 ]
adcx rbp, rdx
adc r13, 0x0
xor r14, r14
adox rcx, rbp
adox r13, r12
mov rdi, rcx
shrd rdi, r13, 52
and rcx, r10
lea r11, [ r11 + rdi ]
adox r8, r11
adox rbx, r14
mov r12, r8
shrd r12, rbx, 52
add r12, [ rsp - 0x28 ]
and r8, r10
mov [ r9 + 0x18 ], r8
mov [ r9 + 0x20 ], r12
mov [ r9 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.1844
; seed 2625400661231680 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4420 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=367, initial num_batches=31): 446 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.10090497737556561
; number reverted permutation / tried permutation: 369 / 483 =76.398%
; number reverted decision / tried decision: 351 / 516 =68.023%
; validated in 0.197s
