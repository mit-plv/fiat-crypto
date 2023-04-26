SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x8 ]
mov r10, rax
shl r10, 0x1
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
add r11, r8
adcx r9, rcx
imul rdx, [ rsi + 0x10 ], 0x5
mov rax, r11
shrd rax, r9, 44
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
xor rdx, rdx
adox rcx, r9
adox rbx, r8
adcx rcx, rax
adc rbx, 0x0
mov rax, [ rsi + 0x10 ]
lea r8, [rax + rax]
mov rax, rcx
shrd rax, rbx, 43
mov rdx, [ rsi + 0x0 ]
mulx rbx, r9, r8
mov rdx, r10
mulx r8, r10, [ rsi + 0x8 ]
add r10, r9
adcx rbx, r8
xor rdx, rdx
adox r10, rax
adox rbx, rdx
mov rax, r10
shrd rax, rbx, 43
mov r9, 0x2c 
bzhi r8, r11, r9
imul r11, rax, 0x5
lea r8, [ r8 + r11 ]
bzhi rbx, r8, r9
mov [ rdi + 0x0 ], rbx
mov rax, 0x2b 
bzhi r11, rcx, rax
shr r8, 44
lea r8, [ r8 + r11 ]
bzhi rcx, r8, rax
mov [ rdi + 0x8 ], rcx
bzhi rbx, r10, rax
shr r8, 43
lea r8, [ r8 + rbx ]
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1008
; seed 3056335673867837 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1839 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=771, initial num_batches=31): 357 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.19412724306688417
; number reverted permutation / tried permutation: 390 / 496 =78.629%
; number reverted decision / tried decision: 382 / 503 =75.944%
; validated in 0.117s
