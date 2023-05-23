SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, rdx
mov rdx, r11
shrd rdx, rcx, 52
mov r8, 0x1000003d10 
mulx rcx, r9, r8
shlx rdx, [ rsi + 0x10 ], rax
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0x34 
mov [ rsp - 0x70 ], r12
bzhi r12, r11, rdx
mov r11, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
lea r13, [r11 + r11]
mov rdx, r13
mulx r13, r11, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r8, r15, r10
adox r15, r11
adox r13, r8
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, rdx
xor rdx, rdx
adox rdi, r11
adox r8, rbp
mov r11, 0x1000003d10 
mov rdx, r11
mulx rbp, r11, r12
adcx r11, r15
adcx r13, rbp
mov rdx, r14
mulx r12, r14, [ rsi + 0x20 ]
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, rax
xor rdx, rdx
adox rdi, r14
adox r12, r8
mov rdx, [ rsi + 0x20 ]
mulx r14, r8, r10
adcx rbp, r8
adcx r14, rbx
mov rdx, r11
shrd rdx, r13, 52
add rdx, rdi
adc r12, 0x0
xor r10, r10
adox r9, rdx
adox r12, rcx
mov rcx, r9
shrd rcx, r12, 52
mov rdx, [ rsi + 0x20 ]
mulx rbx, r13, rax
add rcx, rbp
adc r14, 0x0
mov rdx, rcx
shrd rdx, r14, 52
mov rax, r13
xor rdi, rdi
adox rax, [ rsp - 0x40 ]
adox rbx, [ rsp - 0x48 ]
adcx rdx, rax
adc rbx, 0x0
mov r10, rdx
shrd r10, rbx, 52
mov r8, 0x34 
bzhi rbp, r9, r8
mov r9, rbp
shr r9, 48
mov r12, [ rsi + 0x18 ]
lea r13, [r12 + r12]
mov r12, 0x30 
bzhi r14, rbp, r12
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx rbp, rbx, r13
adox r10, rbx
adox rbp, rdi
bzhi rdx, rcx, r8
shl rdx, 4
lea rdx, [ rdx + r9 ]
mov rcx, r10
shrd rcx, rbp, 52
bzhi r9, rax, r8
mov rax, 0x1000003d1 
mulx rbx, r13, rax
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, rdx
mov rdx, 0x1000003d10 
mulx r8, r12, r9
adox r13, rbp
adox rdi, rbx
mov r9, r13
shrd r9, rdi, 52
mov rdx, [ rsi + 0x8 ]
mulx rbp, rbx, r15
add r9, rbx
adc rbp, 0x0
xor rdx, rdx
adox r12, r9
adox rbp, r8
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, rbx, r15
adcx r8, rbx
adcx r9, rdi
mov rdx, 0xfffffffffffff 
and r13, rdx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], r13
mov rdi, r12
shrd rdi, rbp, 52
and r11, rdx
adox rdi, r8
mov rbp, 0x0 
adox r9, rbp
and r10, rdx
mov rbx, 0x1000003d10 
mov rdx, r10
mulx r8, r10, rbx
adox r10, rdi
adox r9, r8
mov r13, 0x34 
bzhi rdi, r10, r13
shrd r10, r9, 52
lea r11, [ r11 + r10 ]
mov rdx, rcx
mulx r8, rcx, rbx
add rcx, r11
adc r8, 0x0
mov rdx, rcx
shrd rdx, r8, 52
lea r14, [ r14 + rdx ]
mov [ r15 + 0x20 ], r14
bzhi r9, rcx, r13
mov [ r15 + 0x18 ], r9
mov [ r15 + 0x10 ], rdi
bzhi rdi, r12, r13
mov [ r15 + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1387
; seed 3566223694906793 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 936820 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=284, initial num_batches=31): 77550 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08278004312461305
; number reverted permutation / tried permutation: 74935 / 89702 =83.538%
; number reverted decision / tried decision: 64943 / 90297 =71.922%
; validated in 0.302s
