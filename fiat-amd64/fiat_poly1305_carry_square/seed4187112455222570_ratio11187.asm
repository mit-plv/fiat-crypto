SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x5
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, rdx
imul rdx, [ rsi + 0x10 ], 0x14
mov rcx, [ rsi + 0x8 ]
lea r8, [rcx + rcx]
mulx r9, rcx, [ rsi + 0x8 ]
add rcx, r10
adcx r11, r9
mov r10, rcx
shrd r10, r11, 44
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
mov rdx, r8
mulx r11, r8, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox rax, r8
adox r11, r9
adcx rax, r10
adc r11, 0x0
mov r10, rax
shrd r10, r11, 43
mov r9, [ rsi + 0x10 ]
lea r8, [r9 + r9]
mulx r11, r9, [ rsi + 0x8 ]
mov rdx, r8
mulx rbx, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r8
adox rbx, r11
adcx r9, r10
adc rbx, 0x0
mov r10, r9
shrd r10, rbx, 43
imul r11, r10, 0x5
mov r8, 0x2c 
bzhi rbx, rcx, r8
lea rbx, [ rbx + r11 ]
bzhi rcx, rbx, r8
mov [ rdi + 0x0 ], rcx
shr rbx, 44
mov r10, 0x2b 
bzhi r11, rax, r10
lea rbx, [ rbx + r11 ]
bzhi rax, rbx, r10
shr rbx, 43
mov [ rdi + 0x8 ], rax
bzhi rcx, r9, r10
lea rbx, [ rbx + rcx ]
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1187
; seed 4187112455222570 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2054 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=803, initial num_batches=31): 382 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18597857838364168
; number reverted permutation / tried permutation: 407 / 497 =81.891%
; number reverted decision / tried decision: 394 / 502 =78.486%
; validated in 0.116s
