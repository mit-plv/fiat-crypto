SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x5
imul r10, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, rax
test al, al
adox r11, r8
adox r9, rcx
mov rdx, [ rsi + 0x8 ]
lea rax, [rdx + rdx]
mov rdx, rax
mulx rcx, rax, [ rsi + 0x0 ]
adcx r10, rax
adcx rcx, rbx
mov r8, r11
shrd r8, r9, 44
xor rbx, rbx
adox r10, r8
adox rcx, rbx
mov r9, r10
shrd r9, rcx, 43
imul rax, [ rsi + 0x10 ], 0x2
mulx rcx, r8, [ rsi + 0x8 ]
mov rdx, rax
mulx rbx, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, rax
adox rbx, rcx
adcx r8, r9
adc rbx, 0x0
mov r9, r8
shrd r9, rbx, 43
lea rcx, [r9 + 4 * r9]
mov rax, 0x2c 
bzhi rbx, r11, rax
lea rbx, [ rbx + rcx ]
bzhi r11, rbx, rax
mov r9, 0x2b 
bzhi rcx, r10, r9
shr rbx, 44
lea rbx, [ rbx + rcx ]
bzhi r10, rbx, r9
bzhi rcx, r8, r9
shr rbx, 43
lea rbx, [ rbx + rcx ]
mov [ rdi + 0x10 ], rbx
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1186
; seed 3283121373150750 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 579913 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=526, initial num_batches=31): 101092 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1743227001291573
; number reverted permutation / tried permutation: 73056 / 89942 =81.226%
; number reverted decision / tried decision: 71041 / 90057 =78.884%
; validated in 0.157s
