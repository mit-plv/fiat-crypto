SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 4 * rax]
imul rax, [ rdx + 0x8 ], 0xa
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ r11 + 0x0 ]
imul rdx, [ r11 + 0x10 ], 0xa
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, rax
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, r9
adox rbx, rbp
mov rdx, r10
mulx r9, r10, [ rsi + 0x10 ]
mov rdx, [ r11 + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
adcx rax, rcx
adcx r8, rbx
add r10, rbp
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, [ r11 + 0x8 ]
imul rdx, [ r11 + 0x8 ], 0x2
mulx rbp, r9, [ rsi + 0x8 ]
add r10, rcx
adcx rbx, r12
mov r12, rax
shrd r12, r8, 44
mov rdx, [ r11 + 0x0 ]
mulx rcx, r8, [ rsi + 0x10 ]
add r8, r9
adcx rbp, rcx
mov rdx, [ r11 + 0x10 ]
mulx rcx, r9, [ rsi + 0x0 ]
add r10, r12
adc rbx, 0x0
mov rdx, r10
shrd rdx, rbx, 43
mov r12, 0x7ffffffffff 
and r10, r12
adox r8, r9
adox rcx, rbp
adcx r8, rdx
adc rcx, 0x0
mov rbp, r8
shrd rbp, rcx, 43
mov r9, 0xfffffffffff 
and rax, r9
lea rbx, [rbp + 4 * rbp]
lea rax, [ rax + rbx ]
mov rdx, rax
and rdx, r9
mov [ rdi + 0x0 ], rdx
shr rax, 44
lea rax, [ rax + r10 ]
mov r10, rax
shr r10, 43
and rax, r12
and r8, r12
lea r10, [ r10 + r8 ]
mov [ rdi + 0x8 ], rax
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2326
; seed 2574977625098930 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1783 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=946, initial num_batches=31): 378 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.21200224340998317
; number reverted permutation / tried permutation: 411 / 525 =78.286%
; number reverted decision / tried decision: 357 / 474 =75.316%
; validated in 0.09s
