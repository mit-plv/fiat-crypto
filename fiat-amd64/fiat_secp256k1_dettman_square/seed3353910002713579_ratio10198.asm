SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x8 ]
mov rdx, r11
shl rdx, 0x1
mov r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x78 ], rbp
mov rbp, rax
and rbp, rdx
mov [ rsp - 0x70 ], r12
mov r12, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rsi + 0x10 ], r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r12, rdx
mov rdx, r13
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rsi + 0x20 ]
shrd rax, r10, 52
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x18 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, rbp
mov rdx, r11
mulx rbp, r11, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rax
mov rax, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r9
lea r9, [rax + rax]
xor rax, rax
adox r12, r13
adox r15, r14
mulx r13, r14, [ rsi + 0x20 ]
adcx r10, r14
adcx r13, rdi
mulx r14, rdi, [ rsi + 0x18 ]
test al, al
adox rcx, rdi
adox r14, r8
mov rdx, r9
mulx r8, r9, [ rsi + 0x18 ]
adcx r11, r9
adcx r8, rbp
add rbx, r11
adcx r8, [ rsp - 0x30 ]
mulx rdi, rbp, [ rsi + 0x10 ]
mov r9, 0x34 
bzhi r11, rbx, r9
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r11
mulx r11, r9, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r12
mulx r12, r15, rax
shrd rbx, r8, 52
add rcx, r15
adcx r12, r14
add r9, rbp
adcx rdi, r11
xor rdx, rdx
adox rbx, rcx
adox r12, rdx
mov r14, 0x1000003d10 
mov rdx, r14
mulx r8, r14, [ rsp - 0x38 ]
adcx r14, rbx
adcx r12, r8
mov rbp, r14
shrd rbp, r12, 52
mov r11, 0x34 
bzhi r15, r14, r11
imul rcx, [ rsi + 0x18 ], 0x2
xor rbx, rbx
adox rbp, r10
adox r13, rbx
bzhi r10, rbp, r11
shrd rbp, r13, 52
add rbp, [ rsp - 0x18 ]
mov r8, [ rsp - 0x20 ]
adc r8, 0x0
mov r14, rbp
shrd r14, r8, 52
mov rdx, rcx
mulx r12, rcx, [ rsi + 0x20 ]
mov rdx, 0x30 
bzhi r13, r15, rdx
adox r14, rcx
adox r12, rbx
bzhi r8, r14, r11
shr r15, 48
shl r10, 4
lea r10, [ r10 + r15 ]
mov rdx, rax
mulx rcx, rax, [ rsi + 0x8 ]
mov rdx, 0x1000003d1 
mulx rbx, r15, r10
test al, al
adox r15, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
mov r10, r15
shrd r10, rbx, 52
bzhi rdx, r15, r11
adox r10, rax
mov r15, 0x0 
adox rcx, r15
mov rax, [ rsp - 0x50 ]
mov [ rax + 0x0 ], rdx
shrd r14, r12, 52
mov r12, 0x1000003d10 
mov rdx, r12
mulx rbx, r12, r14
bzhi r14, rbp, r11
mulx r15, rbp, r14
mulx r11, r14, r8
adox rbp, r10
adox rcx, r15
mov r8, 0xfffffffffffff 
mov r10, rbp
and r10, r8
mov [ rax + 0x8 ], r10
shrd rbp, rcx, 52
xor r15, r15
adox rbp, r9
adox rdi, r15
adcx r14, rbp
adcx rdi, r11
mov r9, r14
shrd r9, rdi, 52
add r9, [ rsp - 0x28 ]
and r14, r8
mov [ rax + 0x10 ], r14
adox r12, r9
adox rbx, r15
mov r11, r12
and r11, r8
mov [ rax + 0x18 ], r11
shrd r12, rbx, 52
lea r13, [ r13 + r12 ]
mov [ rax + 0x20 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.0198
; seed 3353910002713579 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 10348 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=223, initial num_batches=31): 762 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07363741785852339
; number reverted permutation / tried permutation: 440 / 510 =86.275%
; number reverted decision / tried decision: 343 / 489 =70.143%
; validated in 0.389s
