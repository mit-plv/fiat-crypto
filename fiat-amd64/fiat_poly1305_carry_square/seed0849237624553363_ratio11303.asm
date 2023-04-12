SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + 4 * rax]
mov rax, [ rsi + 0x8 ]
lea r11, [rax + rax]
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, rdx
imul rdx, [ rsi + 0x10 ], 0x14
mulx r9, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox r8, rax
adox rcx, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, rax, r10
mov rdx, r11
mulx r10, r11, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov rbx, r8
shrd rbx, rcx, 44
add rax, r11
adcx r10, r9
xor rcx, rcx
adox rax, rbx
adox r10, rcx
mov r9, [ rsi + 0x10 ]
lea r11, [r9 + r9]
xchg rdx, r11
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, r11
mulx rcx, r11, [ rsi + 0x8 ]
adcx r11, r9
adcx rbx, rcx
mov rdx, rax
shrd rdx, r10, 43
add r11, rdx
adc rbx, 0x0
mov r10, 0xfffffffffff 
and r8, r10
mov r9, r11
shrd r9, rbx, 43
lea rcx, [r9 + 4 * r9]
lea r8, [ r8 + rcx ]
mov rdx, r8
and rdx, r10
mov [ rdi + 0x0 ], rdx
shr r8, 44
mov rbx, 0x7ffffffffff 
and rax, rbx
lea r8, [ r8 + rax ]
mov r9, r8
and r9, rbx
shr r8, 43
and r11, rbx
mov [ rdi + 0x8 ], r9
lea r8, [ r8 + r11 ]
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1303
; seed 0849237624553363 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1864 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=684, initial num_batches=31): 380 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.20386266094420602
; number reverted permutation / tried permutation: 376 / 505 =74.455%
; number reverted decision / tried decision: 352 / 494 =71.255%
; validated in 0.104s
