SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
lea rcx, [rdx + 4 * rdx]
imul rdx, [ rax + 0x8 ], 0xa
mulx r9, r8, [ rsi + 0x10 ]
imul rdx, [ rax + 0x10 ], 0xa
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox r8, rbx
adox rbp, r9
adcx r8, r10
adcx r11, rbp
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, rcx
mov rdx, [ rax + 0x0 ]
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, r8
shrd rdx, r11, 44
xor rbp, rbp
adox r10, rcx
adox rbx, r9
mov r11, rdx
mov rdx, [ rax + 0x8 ]
mulx rcx, r9, [ rsi + 0x0 ]
adcx r10, r9
adcx rcx, rbx
add r10, r11
adc rcx, 0x0
imul rdx, [ rax + 0x8 ], 0x2
mulx rbx, r11, [ rsi + 0x8 ]
mov r9, r10
shrd r9, rcx, 43
mov rdx, [ rax + 0x0 ]
mulx rbp, rcx, [ rsi + 0x10 ]
add rcx, r11
adcx rbx, rbp
mov rdx, [ rax + 0x10 ]
mulx rbp, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, r11
adox rbp, rbx
adcx rcx, r9
adc rbp, 0x0
mov r9, 0xfffffffffff 
and r8, r9
mov rbx, rcx
shrd rbx, rbp, 43
lea r11, [rbx + 4 * rbx]
lea r8, [ r8 + r11 ]
mov rbp, r8
and rbp, r9
shr r8, 44
mov rbx, 0x7ffffffffff 
and rcx, rbx
and r10, rbx
lea r8, [ r8 + r10 ]
mov r11, r8
shr r11, 43
lea r11, [ r11 + rcx ]
mov [ rdi + 0x10 ], r11
and r8, rbx
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2396
; seed 1022764405827241 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 337035 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=813, initial num_batches=31): 68039 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.20187517616864717
; number reverted permutation / tried permutation: 74797 / 89970 =83.135%
; number reverted decision / tried decision: 70329 / 90029 =78.118%
; validated in 0.097s
