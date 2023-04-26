SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, rdx
imul rdx, [ rsi + 0x10 ], 0x14
mulx r8, rcx, [ rsi + 0x8 ]
xor r9, r9
adox rcx, r10
adox r11, r8
mov r10, rcx
shrd r10, r11, 44
imul rdx, [ rsi + 0x10 ], 0x5
mulx r11, r8, [ rsi + 0x10 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x0 ]
add r8, rax
adcx r9, r11
add r8, r10
adc r9, 0x0
mov r10, r8
shrd r10, r9, 43
mulx rax, r11, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x10 ], 0x2
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r9
adox rbx, rax
adcx r11, r10
adc rbx, 0x0
mov r10, r11
shrd r10, rbx, 43
imul rax, r10, 0x5
mov r9, 0x7ffffffffff 
and r11, r9
mov rbx, 0xfffffffffff 
and rcx, rbx
lea rcx, [ rcx + rax ]
mov r10, rcx
and r10, rbx
shr rcx, 44
mov [ rdi + 0x0 ], r10
and r8, r9
lea rcx, [ rcx + r8 ]
mov rax, rcx
and rax, r9
shr rcx, 43
lea rcx, [ rcx + r11 ]
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1568
; seed 0482229459697005 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2963 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1100, initial num_batches=31): 722 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.24367195410057374
; number reverted permutation / tried permutation: 392 / 508 =77.165%
; number reverted decision / tried decision: 385 / 491 =78.411%
; validated in 0.17s
