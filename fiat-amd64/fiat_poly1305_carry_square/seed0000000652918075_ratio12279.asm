SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x10 ], 0x14
mov rdx, r11
mulx rcx, r11, [ rsi + 0x8 ]
xor r8, r8
adox r11, rax
adox r10, rcx
mov r9, [ rsi + 0x8 ]
mov rax, r9
shl rax, 0x1
mov r9, r11
shrd r9, r10, 44
imul rdx, [ rsi + 0x10 ], 0x5
mulx r10, rcx, [ rsi + 0x10 ]
mov rdx, rax
mulx r8, rax, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox rcx, rax
adox r8, r10
adcx rcx, r9
adc r8, 0x0
imul r9, [ rsi + 0x10 ], 0x2
mulx rax, r10, [ rsi + 0x8 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x0 ]
add r10, r9
adcx rbx, rax
mov rdx, rcx
shrd rdx, r8, 43
add r10, rdx
adc rbx, 0x0
mov r8, r10
shrd r8, rbx, 43
lea rax, [r8 + 4 * r8]
mov r9, 0x7ffffffffff 
and r10, r9
mov rdx, 0xfffffffffff 
and r11, rdx
lea r11, [ r11 + rax ]
mov rbx, r11
and rbx, rdx
mov [ rdi + 0x0 ], rbx
and rcx, r9
shr r11, 44
lea r11, [ r11 + rcx ]
mov r8, r11
shr r8, 43
and r11, r9
lea r8, [ r8 + r10 ]
mov [ rdi + 0x10 ], r8
mov [ rdi + 0x8 ], r11
mov rbx, [ rsp - 0x80 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2279
; seed 1689906652498032 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 279451 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1006, initial num_batches=31): 65921 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.23589466489652927
; number reverted permutation / tried permutation: 71148 / 89757 =79.267%
; number reverted decision / tried decision: 78264 / 90242 =86.727%
; validated in 0.079s
