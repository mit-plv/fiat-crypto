SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x18 ]
lea rdx, [r11 + r11]
mov r11, 0x1 
shlx rcx, [ rsi + 0x10 ], r11
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r9, rdx
mov rdx, rcx
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov rbp, 0x34 
mov [ rsp - 0x70 ], r12
bzhi r12, r9, rbp
mov [ rsp - 0x68 ], r13
mov r13, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov r14, r13
shl r14, 0x1
shrd r9, r11, 52
mov r13, [ rsi + 0x0 ]
mov r11, r13
shl r11, 0x1
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx rbp, r15, r14
mov rdx, r11
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r8
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], rbx
mulx rbx, r9, r14
xor rdx, rdx
adox r9, r11
adox rdi, rbx
adcx rax, r15
adcx rbp, r10
mov rdx, r8
mulx r10, r8, [ rsi + 0x20 ]
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r11, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r13, rdx
xor rdx, rdx
adox r13, r11
adox rbx, rbp
mov r11, 0x1000003d10 
mov rdx, r12
mulx rbp, r12, r11
adcx r12, r9
adcx rdi, rbp
mov rdx, [ rsi + 0x20 ]
mulx rbp, r9, r14
xor rdx, rdx
adox rcx, r9
adox rbp, [ rsp - 0x28 ]
mov r14, r12
shrd r14, rdi, 52
add rax, r8
adcx r10, [ rsp - 0x20 ]
mov rdx, [ rsp - 0x40 ]
mulx rdi, r8, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, rax
adox r10, rdx
mov rdx, [ rsp - 0x48 ]
mulx rax, r9, r11
adcx r9, r14
adcx r10, rax
mov rdx, 0xfffffffffffff 
mov r14, r9
and r14, rdx
and r12, rdx
shrd r9, r10, 52
xor rax, rax
adox r9, rcx
adox rbp, rax
mov rcx, r9
shrd rcx, rbp, 52
mov r10, r14
shr r10, 48
mov rbp, 0xffffffffffff 
and r14, rbp
adox rcx, r13
adox rbx, rax
mov rdx, [ rsi + 0x0 ]
mulx rax, r13, rdx
mov rdx, 0xfffffffffffff 
mov rbp, rcx
and rbp, rdx
and r9, rdx
shl r9, 4
lea r9, [ r9 + r10 ]
shrd rcx, rbx, 52
mov r10, 0x1000003d1 
mov rdx, r10
mulx rbx, r10, r9
xor r9, r9
adox r10, r13
adox rax, rbx
adcx rcx, r8
adc rdi, 0x0
mov r8, 0x34 
bzhi r13, r10, r8
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], r13
mov rdx, [ rsi + 0x8 ]
mulx r9, r13, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, r15
adox r13, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
mov rdx, 0x1000003d10 
mulx rbx, r15, rbp
shrd r10, rax, 52
mov rbp, rcx
shrd rbp, rdi, 52
xor rax, rax
adox r10, r8
adox r11, rax
adcx r15, r10
adcx r11, rbx
mov rdi, r15
shrd rdi, r11, 52
test al, al
adox rdi, r13
adox r9, rax
mulx r13, r8, rbp
mov rbx, 0x34 
bzhi rbp, rcx, rbx
mulx r10, rcx, rbp
adox rcx, rdi
adox r9, r10
bzhi r11, rcx, rbx
shrd rcx, r9, 52
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], r11
lea r12, [ r12 + rcx ]
add r8, r12
adc r13, 0x0
bzhi rbp, r8, rbx
mov [ rdi + 0x18 ], rbp
shrd r8, r13, 52
lea r14, [ r14 + r8 ]
bzhi r10, r15, rbx
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1133
; seed 2716647052398798 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5474 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=280, initial num_batches=31): 458 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08366824990865912
; number reverted permutation / tried permutation: 427 / 527 =81.025%
; number reverted decision / tried decision: 320 / 472 =67.797%
; validated in 0.31s
