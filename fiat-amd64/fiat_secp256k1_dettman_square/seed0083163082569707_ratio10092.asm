SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
imul rax, [ rsi + 0x10 ], 0x2
mov r10, [ rsi + 0x0 ]
lea r11, [r10 + r10]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
mov rdx, [ rsi + 0x8 ]
lea r8, [rdx + rdx]
mov rdx, 0x1 
shlx r9, [ rsi + 0x18 ], rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, r8
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
test al, al
adox r14, r8
adox r12, r15
mov rdx, [ rsi + 0x20 ]
mulx r15, r8, r11
mov rdx, r11
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adcx r14, r8
adcx r15, r12
mulx r8, r12, [ rsi + 0x8 ]
mov rdx, r13
mov [ rsp - 0x38 ], r8
mulx r8, r13, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], r9
mulx r9, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox r13, rdi
adox r11, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, rdi, rax
adcx rdi, r12
adcx r9, r8
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x20 ], r8
mov r8, rbx
and r8, rdx
mov rdx, 0x1000003d10 
mov [ rsp - 0x18 ], r12
mov [ rsp - 0x10 ], r9
mulx r9, r12, r8
mov rdx, rax
mulx r8, rax, [ rsi + 0x20 ]
adox r10, rax
adox r8, rcx
shrd rbx, rbp, 52
mov rdx, 0x1000003d10 
mulx rbp, rcx, rbx
xor rax, rax
adox r12, r13
adox r11, r9
mov r13, r12
shrd r13, r11, 52
xor r9, r9
adox r13, r14
adox r15, r9
adcx rcx, r13
adcx r15, rbp
mov rax, 0x34 
bzhi r14, rcx, rax
mov rbx, 0x30 
bzhi rbp, r14, rbx
shrd rcx, r15, 52
xor r11, r11
adox rcx, rdi
mov r9, [ rsp - 0x10 ]
adox r9, r11
bzhi rdi, rcx, rax
shl rdi, 4
bzhi r13, r12, rax
shrd rcx, r9, 52
xor r12, r12
adox rcx, r10
adox r8, r12
mov r11, rcx
shrd r11, r8, 52
shr r14, 48
mov rdx, [ rsi + 0x0 ]
mulx r15, r10, rdx
lea rdi, [ rdi + r14 ]
mov rdx, 0x1000003d1 
mulx r8, r9, rdi
add r9, r10
adcx r15, r8
mov rdx, [ rsi + 0x20 ]
mulx r10, r14, [ rsp - 0x28 ]
add r11, r14
adc r10, 0x0
bzhi rdx, rcx, rax
bzhi rcx, r9, rax
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], rcx
bzhi r8, r11, rax
shrd r9, r15, 52
mov r15, 0x1000003d10 
mulx rcx, r14, r15
xor rdx, rdx
adox r9, [ rsp - 0x30 ]
mov r12, [ rsp - 0x38 ]
adox r12, rdx
mov rbx, [ rsp - 0x18 ]
adcx rbx, [ rsp - 0x40 ]
mov rax, [ rsp - 0x20 ]
adcx rax, [ rsp - 0x48 ]
shrd r11, r10, 52
mov rdx, r15
mulx r10, r15, r11
add r14, r9
adcx r12, rcx
mov rcx, r14
shrd rcx, r12, 52
mulx r11, r9, r8
add rcx, rbx
adc rax, 0x0
xor r8, r8
adox r9, rcx
adox rax, r11
mov rbx, r9
shrd rbx, rax, 52
lea r13, [ r13 + rbx ]
mov r11, 0x34 
bzhi rcx, r14, r11
bzhi r14, r9, r11
mov [ rdi + 0x8 ], rcx
adox r15, r13
adox r10, r8
mov r12, r15
shrd r12, r10, 52
lea rbp, [ rbp + r12 ]
mov [ rdi + 0x10 ], r14
bzhi r9, r15, r11
mov [ rdi + 0x18 ], r9
mov [ rdi + 0x20 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.0092
; seed 0083163082569707 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6420 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=244, initial num_batches=31): 469 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07305295950155763
; number reverted permutation / tried permutation: 432 / 502 =86.056%
; number reverted decision / tried decision: 377 / 497 =75.855%
; validated in 0.353s
