SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x10 ]
lea rcx, [rdx + 4 * rdx]
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x10 ]
mov r9, [ rsi + 0x8 ]
lea rax, [r9 + r9]
mov rdx, rax
mulx r9, rax, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox rcx, rax
adox r9, r8
mov r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbx, rax, rdx
adcx r10, rax
adcx rbx, r11
mov rdx, 0x1 
shlx r11, [ rsi + 0x10 ], rdx
mov rax, r10
shrd rax, rbx, 44
add rcx, rax
adc r9, 0x0
mov rdx, r8
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, r11
mulx rax, r11, [ rsi + 0x0 ]
mov rdx, rcx
shrd rdx, r9, 43
xor r9, r9
adox r8, r11
adox rax, rbx
adcx r8, rdx
adc rax, 0x0
mov rbx, 0xfffffffffff 
and r10, rbx
mov r11, 0x7ffffffffff 
mov rdx, r8
and rdx, r11
shrd r8, rax, 43
lea rax, [r8 + 4 * r8]
lea r10, [ r10 + rax ]
mov r8, r10
shr r8, 44
and r10, rbx
and rcx, r11
lea r8, [ r8 + rcx ]
mov rax, r8
and rax, r11
mov [ rdi + 0x8 ], rax
mov [ rdi + 0x0 ], r10
shr r8, 43
lea r8, [ r8 + rdx ]
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1050
; seed 3553248937761059 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1853 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=619, initial num_batches=31): 347 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18726389638424176
; number reverted permutation / tried permutation: 370 / 489 =75.665%
; number reverted decision / tried decision: 345 / 510 =67.647%
; validated in 0.103s
