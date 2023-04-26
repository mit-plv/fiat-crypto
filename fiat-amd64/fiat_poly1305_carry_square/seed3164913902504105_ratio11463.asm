SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x8 ]
lea r9, [rdx + rdx]
add r10, rcx
adcx r8, r11
imul rdx, [ rsi + 0x10 ], 0x5
mov rax, r10
shrd rax, r8, 44
mov r11, [ rsi + 0x10 ]
lea rcx, [r11 + r11]
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
add r11, r9
adcx rbx, r8
mulx r9, r8, [ rsi + 0x8 ]
add r11, rax
adc rbx, 0x0
mov rdx, rcx
mulx rax, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, rcx
adox rax, r9
mov r9, 0x2b 
bzhi rcx, r11, r9
shrd r11, rbx, 43
mov rbx, 0xfffffffffff 
and r10, rbx
adox r8, r11
adox rax, rdx
bzhi r11, r8, r9
shrd r8, rax, 43
imul rax, r8, 0x5
lea r10, [ r10 + rax ]
mov r8, r10
shr r8, 44
lea r8, [ r8 + rcx ]
bzhi rcx, r8, r9
mov [ rdi + 0x8 ], rcx
shr r8, 43
lea r8, [ r8 + r11 ]
mov [ rdi + 0x10 ], r8
and r10, rbx
mov [ rdi + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1463
; seed 3164913902504105 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3285 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=564, initial num_batches=31): 608 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18508371385083713
; number reverted permutation / tried permutation: 408 / 498 =81.928%
; number reverted decision / tried decision: 433 / 501 =86.427%
; validated in 0.146s
