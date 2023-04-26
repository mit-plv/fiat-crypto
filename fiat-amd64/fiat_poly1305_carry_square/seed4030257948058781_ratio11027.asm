SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
imul rdx, [ rsi + 0x10 ], 0x5
mulx rax, r9, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rcx
adox r8, r11
mov r11, [ rsi + 0x8 ]
lea rcx, [r11 + r11]
mov r11, r10
shrd r11, r8, 44
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
add r9, rbx
adcx rbp, rax
mov rax, [ rsi + 0x10 ]
lea rdx, [rax + rax]
mulx rbx, rax, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, rax
adox rbx, r8
adcx r9, r11
adc rbp, 0x0
mov r11, 0x2b 
bzhi r8, r9, r11
shrd r9, rbp, 43
add rcx, r9
adc rbx, 0x0
mov rax, rcx
shrd rax, rbx, 43
imul rbp, rax, 0x5
mov r9, 0x2c 
bzhi rbx, r10, r9
bzhi r10, rcx, r11
lea rbx, [ rbx + rbp ]
bzhi rcx, rbx, r9
mov [ rdi + 0x0 ], rcx
shr rbx, 44
lea rbx, [ rbx + r8 ]
bzhi r8, rbx, r11
shr rbx, 43
lea rbx, [ rbx + r10 ]
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1027
; seed 4030257948058781 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1838 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=801, initial num_batches=31): 365 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1985854189336235
; number reverted permutation / tried permutation: 436 / 515 =84.660%
; number reverted decision / tried decision: 383 / 484 =79.132%
; validated in 0.118s
