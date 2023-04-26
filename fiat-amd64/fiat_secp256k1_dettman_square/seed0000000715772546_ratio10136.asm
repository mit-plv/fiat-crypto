SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, r10
mov rdx, r11
shrd rdx, rcx, 52
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
lea rbp, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
imul rdx, [ rsi + 0x0 ], 0x2
mov [ rsp - 0x60 ], r14
mov r14, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov r15, r14
shl r15, 0x1
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r12
mov [ rsp - 0x38 ], rbp
mulx rbp, r12, rdx
xor rdx, rdx
adox r12, r8
adox r9, rbp
mov rdx, [ rsi + 0x20 ]
mulx rbp, r8, r13
mov rdx, r10
mov [ rsp - 0x30 ], rbx
mulx rbx, r10, [ rsi + 0x10 ]
adcx r12, r8
adcx rbp, r9
mov rdx, 0xfffffffffffff 
and r11, rdx
mov r9, 0x1000003d10 
mov rdx, r9
mulx r8, r9, r11
adox r10, r14
adox rdi, rbx
adcx r9, r10
adcx rdi, r8
mulx rbx, r14, rcx
mov rdx, r15
mulx rcx, r15, [ rsi + 0x18 ]
add r15, rax
adcx rcx, [ rsp - 0x30 ]
mov rax, r9
shrd rax, rdi, 52
xor r11, r11
adox rax, r12
adox rbp, r11
adcx r14, rax
adcx rbp, rbx
mov r12, 0x34 
bzhi r8, r14, r12
shrd r14, rbp, 52
xor r10, r10
adox r14, r15
adox rcx, r10
mov r11, r14
shrd r11, rcx, 52
bzhi rdi, r14, r12
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rax, r15, rdx
mov rdx, rbx
mulx rbp, rbx, [ rsi + 0x20 ]
adox r15, rbx
adox rbp, rax
mov rdx, 0xffffffffffff 
mov r14, r8
and r14, rdx
adox r11, r15
adox rbp, r10
shr r8, 48
shl rdi, 4
lea rdi, [ rdi + r8 ]
mov rdx, [ rsi + 0x0 ]
mulx rax, rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbx, [ rsp - 0x38 ]
mov rdx, 0x1000003d1 
mulx r10, r8, rdi
mov rdi, r11
shrd rdi, rbp, 52
test al, al
adox r8, rcx
adox rax, r10
adcx rdi, rbx
adc r15, 0x0
bzhi rbp, rdi, r12
mov rcx, r8
shrd rcx, rax, 52
mov rdx, r13
mulx rbx, r13, [ rsi + 0x8 ]
xor r10, r10
adox rcx, r13
adox rbx, r10
bzhi rax, r11, r12
mulx r13, r11, [ rsi + 0x10 ]
mov rdx, 0x1000003d10 
mulx r12, r10, rax
adox r10, rcx
adox rbx, r12
mov rcx, r11
test al, al
adox rcx, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov rax, 0x34 
bzhi r11, r10, rax
shrd r10, rbx, 52
xor r12, r12
adox r10, rcx
adox r13, r12
mulx rcx, rbx, rbp
adcx rbx, r10
adcx r13, rcx
bzhi rbp, rbx, rax
shrd rdi, r15, 52
mulx r10, r15, rdi
bzhi rcx, r9, rax
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rbp
shrd rbx, r13, 52
lea rcx, [ rcx + rbx ]
xor r13, r13
adox r15, rcx
adox r10, r13
bzhi r12, r8, rax
bzhi r8, r15, rax
mov [ r9 + 0x18 ], r8
shrd r15, r10, 52
lea r14, [ r14 + r15 ]
mov [ r9 + 0x0 ], r12
mov [ r9 + 0x8 ], r11
mov [ r9 + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0136
; seed 2337486353719921 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1452010 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=457, initial num_batches=31): 156359 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10768452007906282
; number reverted permutation / tried permutation: 75043 / 89811 =83.557%
; number reverted decision / tried decision: 64081 / 90188 =71.053%
; validated in 0.445s
