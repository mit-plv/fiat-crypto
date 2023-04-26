SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rax
imul rdx, [ r10 + 0x10 ], 0xa
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, [ r10 + 0x0 ]
xor rdx, rdx
adox r11, r8
adox r9, rcx
adcx r11, rax
adcx rbx, r9
mov rcx, r11
shrd rcx, rbx, 44
mov r8, [ r10 + 0x10 ]
lea rax, [r8 + 4 * r8]
mov rdx, [ r10 + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, rax
mulx rbx, rax, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, r8
adox r9, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r8, [ r10 + 0x8 ]
adcx rax, r8
adcx rbx, r9
imul rdx, [ r10 + 0x8 ], 0x2
add rax, rcx
adc rbx, 0x0
mov rcx, rax
shrd rcx, rbx, 43
mulx r8, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ r10 + 0x0 ]
xor rdx, rdx
adox rbx, r9
adox r8, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ r10 + 0x10 ]
adcx rbx, r9
adcx rbp, r8
add rbx, rcx
adc rbp, 0x0
mov rdx, rbx
shrd rdx, rbp, 43
lea rcx, [rdx + 4 * rdx]
mov r8, 0xfffffffffff 
and r11, r8
lea r11, [ r11 + rcx ]
mov r9, r11
shr r9, 44
and r11, r8
mov rbp, 0x7ffffffffff 
and rbx, rbp
and rax, rbp
lea r9, [ r9 + rax ]
mov [ rdi + 0x0 ], r11
mov rdx, r9
shr rdx, 43
lea rdx, [ rdx + rbx ]
mov [ rdi + 0x10 ], rdx
and r9, rbp
mov [ rdi + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2304
; seed 2895160250281468 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 312387 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=945, initial num_batches=31): 69196 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.22150729703860916
; number reverted permutation / tried permutation: 73094 / 89800 =81.396%
; number reverted decision / tried decision: 68927 / 90199 =76.417%
; validated in 0.086s
