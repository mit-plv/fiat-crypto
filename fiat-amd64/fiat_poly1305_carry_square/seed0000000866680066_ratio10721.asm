SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov r10, [ rsi + 0x10 ]
lea r11, [r10 + 4 * r10]
mov rdx, r11
mulx r11, r10, [ rsi + 0x10 ]
mov rcx, [ rsi + 0x8 ]
lea r8, [rcx + rcx]
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, r8
xor rdx, rdx
adox r10, rcx
adox r9, r11
mov rdx, rax
mulx r11, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, rdx
adcx rax, rcx
adcx rbx, r11
mov rdx, 0x2c 
bzhi r11, rax, rdx
shrd rax, rbx, 44
xor rcx, rcx
adox r10, rax
adox r9, rcx
mov rbx, r10
shrd rbx, r9, 43
mov rdx, r8
mulx rax, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
lea r9, [rdx + rdx]
mov rdx, r9
mulx rcx, r9, [ rsi + 0x0 ]
mov rdx, 0x7ffffffffff 
and r10, rdx
adox r8, r9
adox rcx, rax
adcx r8, rbx
adc rcx, 0x0
mov rbx, r8
shrd rbx, rcx, 43
and r8, rdx
lea rax, [rbx + 4 * rbx]
lea r11, [ r11 + rax ]
mov r9, r11
shr r9, 44
lea r9, [ r9 + r10 ]
mov r10, r9
shr r10, 43
and r9, rdx
mov rcx, 0xfffffffffff 
and r11, rcx
mov [ rdi + 0x8 ], r9
lea r10, [ r10 + r8 ]
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0721
; seed 4395469375335619 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 258810 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=634, initial num_batches=31): 53592 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.2070708241567173
; number reverted permutation / tried permutation: 73348 / 89993 =81.504%
; number reverted decision / tried decision: 69550 / 90006 =77.273%
; validated in 0.078s
