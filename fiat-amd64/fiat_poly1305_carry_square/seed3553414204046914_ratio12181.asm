SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, rdx
imul rdx, [ rsi + 0x10 ], 0x14
imul rcx, [ rsi + 0x8 ], 0x2
mulx r9, r8, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x10 ], 0x5
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, rax
adox r11, r9
mov rdx, rcx
mulx rax, rcx, [ rsi + 0x0 ]
adcx rbx, rcx
adcx rax, rbp
mov r9, r8
shrd r9, r11, 44
add rbx, r9
adc rax, 0x0
mov rbp, 0x7ffffffffff 
mov r11, rbx
and r11, rbp
shrd rbx, rax, 43
mulx r9, rcx, [ rsi + 0x8 ]
mov rdx, r10
mulx rax, r10, [ rsi + 0x0 ]
add rcx, r10
adcx rax, r9
add rcx, rbx
adc rax, 0x0
mov rdx, rcx
shrd rdx, rax, 43
lea rbx, [rdx + 4 * rdx]
and rcx, rbp
mov r9, 0xfffffffffff 
and r8, r9
lea r8, [ r8 + rbx ]
mov r10, r8
shr r10, 44
lea r10, [ r10 + r11 ]
mov r11, r10
and r11, rbp
mov [ rdi + 0x8 ], r11
shr r10, 43
and r8, r9
mov [ rdi + 0x0 ], r8
lea r10, [ r10 + rcx ]
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2181
; seed 3553414204046914 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1452 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1186, initial num_batches=31): 375 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.25826446280991733
; number reverted permutation / tried permutation: 344 / 459 =74.946%
; number reverted decision / tried decision: 450 / 540 =83.333%
; validated in 0.069s
