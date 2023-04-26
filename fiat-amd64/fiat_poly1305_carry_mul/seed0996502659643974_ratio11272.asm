SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
imul rdx, [ r10 + 0x10 ], 0xa
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x10 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + 4 * rdx]
mov rdx, rax
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x10 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
add rax, r8
adcx r9, rbp
mov rdx, rbx
mulx r8, rbx, [ rsi + 0x10 ]
add rax, r12
adcx r13, r9
mov rdx, [ rsi + 0x8 ]
mulx r12, rbp, [ r10 + 0x0 ]
xor rdx, rdx
adox rbx, rbp
adox r12, r8
mov rdx, [ r10 + 0x8 ]
mulx r8, r9, [ rsi + 0x0 ]
adcx rbx, r9
adcx r8, r12
imul rdx, [ r10 + 0x8 ], 0x2
mulx r12, rbp, [ rsi + 0x8 ]
mov r9, rax
shrd r9, r13, 44
add rbx, r9
adc r8, 0x0
mov r13, rbx
shrd r13, r8, 43
mov rdx, [ r10 + 0x10 ]
mulx r8, r9, [ rsi + 0x0 ]
add r11, rbp
adcx r12, rcx
add r11, r9
adcx r8, r12
add r11, r13
adc r8, 0x0
mov rdx, r11
shrd rdx, r8, 43
mov rcx, 0x2c 
bzhi rbp, rax, rcx
imul rax, rdx, 0x5
lea rbp, [ rbp + rax ]
bzhi r13, rbp, rcx
mov [ rdi + 0x0 ], r13
mov r9, 0x2b 
bzhi r12, rbx, r9
shr rbp, 44
lea rbp, [ rbp + r12 ]
bzhi rbx, r11, r9
bzhi r11, rbp, r9
shr rbp, 43
lea rbp, [ rbp + rbx ]
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1272
; seed 0996502659643974 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2304 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=621, initial num_batches=31): 357 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.15494791666666666
; number reverted permutation / tried permutation: 382 / 503 =75.944%
; number reverted decision / tried decision: 330 / 496 =66.532%
; validated in 0.154s
