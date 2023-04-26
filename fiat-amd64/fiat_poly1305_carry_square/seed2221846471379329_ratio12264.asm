SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x10 ]
lea rdx, [r11 + 4 * r11]
imul r11, [ rsi + 0x10 ], 0x14
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, r11
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
xor rdx, rdx
adox r11, rax
adox r10, r9
mov rax, r11
shrd rax, r10, 44
mov rdx, rbx
mulx r9, rbx, [ rsi + 0x0 ]
xor r10, r10
adox rcx, rbx
adox r9, r8
adcx rcx, rax
adc r9, 0x0
mov r8, rcx
shrd r8, r9, 43
mulx rbx, rax, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x10 ], 0x2
mulx r10, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r9
adox r10, rbx
adcx rax, r8
adc r10, 0x0
mov r8, rax
shrd r8, r10, 43
mov rbx, 0x7ffffffffff 
and rax, rbx
mov r9, 0xfffffffffff 
and r11, r9
lea r10, [r8 + 4 * r8]
lea r11, [ r11 + r10 ]
mov r8, r11
shr r8, 44
and r11, r9
and rcx, rbx
lea r8, [ r8 + rcx ]
mov [ rdi + 0x0 ], r11
mov r10, r8
and r10, rbx
mov [ rdi + 0x8 ], r10
shr r8, 43
lea r8, [ r8 + rax ]
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2264
; seed 2221846471379329 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1494 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=988, initial num_batches=31): 374 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.250334672021419
; number reverted permutation / tried permutation: 382 / 479 =79.749%
; number reverted decision / tried decision: 449 / 520 =86.346%
; validated in 0.078s
