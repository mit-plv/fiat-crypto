SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
lea rax, [rdx + rdx]
mov rdx, 0x34 
mov [ rsp - 0x80 ], rbx
bzhi rbx, r11, rdx
mov [ rsp - 0x78 ], rbp
mov rbp, 0x1000003d10 
mov rdx, rbx
mov [ rsp - 0x70 ], r12
mulx r12, rbx, rbp
shrd r11, rcx, 52
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
lea r14, [rdx + rdx]
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x0 ]
mov rbp, rdx
shl rbp, 0x1
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, r10
mov rdx, rbp
mov [ rsp - 0x40 ], r14
mulx r14, rbp, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], rcx
mov [ rsp - 0x28 ], r15
mulx r15, rcx, r10
test al, al
adox rcx, rbp
adox r14, r15
adcx rbx, rcx
adcx r14, r12
mov rdx, r10
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, 0x1000003d10 
mulx r15, rbp, r11
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r11
mulx r11, rcx, r13
xor rdx, rdx
adox r8, r10
adox r12, r9
adcx r8, rcx
adcx r11, r12
mov r9, 0x34 
bzhi r10, rbx, r9
shrd rbx, r14, 52
add rbx, r8
adc r11, 0x0
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, rax
xor rdx, rdx
adox rbp, rbx
adox r11, r15
bzhi r15, rbp, r9
shrd rbp, r11, 52
add r14, rdi
adcx rcx, [ rsp - 0x28 ]
xor rdi, rdi
adox rbp, r14
adox rcx, rdi
mov rdx, r15
shr rdx, 48
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r8, rax
mov rdx, r8
test al, al
adox rdx, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
bzhi rax, rbp, r9
mov r11, 0x30 
bzhi r14, r15, r11
shl rax, 4
shrd rbp, rcx, 52
xor r15, r15
adox rbp, rdx
adox rbx, r15
mov rdi, rbp
shrd rdi, rbx, 52
bzhi rcx, rbp, r9
lea rax, [ rax + r12 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, r12, rdx
mov rdx, 0x1000003d1 
mulx rbx, rbp, rax
adox rbp, r12
adox r8, rbx
bzhi rax, rbp, r9
adox rdi, [ rsp - 0x40 ]
mov r12, [ rsp - 0x48 ]
adox r12, r15
bzhi rbx, rdi, r9
mov rdx, r13
mulx r15, r13, [ rsi + 0x8 ]
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], rax
shrd rbp, r8, 52
shrd rdi, r12, 52
xor r8, r8
adox rbp, r13
adox r15, r8
mulx r12, rax, [ rsi + 0x10 ]
mov rdx, 0x1000003d10 
mulx r8, r13, rcx
adcx r13, rbp
adcx r15, r8
mov rcx, rax
xor rbp, rbp
adox rcx, [ rsp - 0x18 ]
adox r12, [ rsp - 0x20 ]
bzhi rax, r13, r9
shrd r13, r15, 52
mulx r15, r8, rbx
mov [ r11 + 0x8 ], rax
xor rbx, rbx
adox r13, rcx
adox r12, rbx
adcx r8, r13
adcx r12, r15
mov rbp, r8
shrd rbp, r12, 52
bzhi rcx, r8, r9
mulx r15, rax, rdi
lea r10, [ r10 + rbp ]
adox rax, r10
adox r15, rbx
mov rdi, rax
shrd rdi, r15, 52
bzhi r13, rax, r9
mov [ r11 + 0x18 ], r13
lea r14, [ r14 + rdi ]
mov [ r11 + 0x20 ], r14
mov [ r11 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1362
; seed 2811747862207902 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5790 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=280, initial num_batches=31): 426 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07357512953367876
; number reverted permutation / tried permutation: 387 / 491 =78.819%
; number reverted decision / tried decision: 349 / 508 =68.701%
; validated in 0.312s
