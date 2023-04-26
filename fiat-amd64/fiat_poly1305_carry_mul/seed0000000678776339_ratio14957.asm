SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
imul rdx, [ rax + 0x8 ], 0xa
mulx r8, rcx, [ rsi + 0x10 ]
imul r9, [ rax + 0x10 ], 0xa
mov rdx, r9
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r9
adox rbx, r8
mov r8, [ rax + 0x10 ]
lea r9, [r8 + 4 * r8]
mov rdx, r9
mulx r9, r8, [ rsi + 0x10 ]
adcx rcx, r10
adcx r11, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, r10, [ rax + 0x0 ]
add r8, r10
adcx rbx, r9
mov rdx, [ rax + 0x8 ]
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, rcx
shrd rdx, r11, 44
xor r11, r11
adox r8, r9
adox r10, rbx
adcx r8, rdx
adc r10, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r9, rbx, [ rax + 0x0 ]
imul rdx, [ rax + 0x8 ], 0x2
mov [ rsp - 0x78 ], rbp
mulx rbp, r11, [ rsi + 0x8 ]
add rbx, r11
adcx rbp, r9
mov rdx, [ rax + 0x10 ]
mulx r11, r9, [ rsi + 0x0 ]
mov rdx, r8
shrd rdx, r10, 43
xor r10, r10
adox rbx, r9
adox r11, rbp
adcx rbx, rdx
adc r11, 0x0
mov rbp, rbx
shrd rbp, r11, 43
mov r9, 0xfffffffffff 
and rcx, r9
lea rdx, [rbp + 4 * rbp]
lea rcx, [ rcx + rdx ]
mov r11, rcx
shr r11, 44
and rcx, r9
mov [ rdi + 0x0 ], rcx
mov rbp, 0x7ffffffffff 
and r8, rbp
lea r11, [ r11 + r8 ]
mov rdx, r11
shr rdx, 43
and r11, rbp
and rbx, rbp
lea rdx, [ rdx + rbx ]
mov [ rdi + 0x8 ], r11
mov [ rdi + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.4957
; seed 2129214698933421 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 336082 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=660, initial num_batches=31): 67473 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.2007635041448218
; number reverted permutation / tried permutation: 74777 / 89973 =83.110%
; number reverted decision / tried decision: 68794 / 90026 =76.416%
; validated in 0.1s
