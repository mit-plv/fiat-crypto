SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, [ rdx + 0x10 ]
lea r11, [r10 + 4 * r10]
mov r10, [ rdx + 0x10 ]
lea rcx, [r10 + r10]
lea rcx, [rcx + 4 * rcx]
xchg rdx, rcx
mulx r8, r10, [ rsi + 0x8 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
mov rdx, [ rcx + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r10
adox r8, r9
adcx rax, rbx
adcx rbp, r8
mov rdx, [ rcx + 0x0 ]
mulx r9, r10, [ rsi + 0x8 ]
mov rdx, r11
mulx rbx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r10
adox r9, rbx
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rcx + 0x8 ]
adcx r11, r8
adcx r10, r9
mov rdx, rax
shrd rdx, rbp, 44
xor rbp, rbp
adox r11, rdx
adox r10, rbp
mov rbx, r11
shrd rbx, r10, 43
mov rdx, [ rcx + 0x0 ]
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rcx + 0x8 ]
mov r10, rdx
shl r10, 0x1
mov rdx, r10
mulx rbp, r10, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r10
adox rbp, r8
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rcx + 0x10 ]
adcx r9, r8
adcx r10, rbp
add r9, rbx
adc r10, 0x0
mov rdx, 0x7ffffffffff 
mov rbx, r9
and rbx, rdx
shrd r9, r10, 43
mov rbp, 0xfffffffffff 
and rax, rbp
lea r8, [r9 + 4 * r9]
lea rax, [ rax + r8 ]
mov r10, rax
and r10, rbp
shr rax, 44
and r11, rdx
lea rax, [ rax + r11 ]
mov r9, rax
shr r9, 43
lea r9, [ r9 + rbx ]
mov [ rdi + 0x10 ], r9
and rax, rdx
mov [ rdi + 0x0 ], r10
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1092
; seed 3455842106773661 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 422532 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=510, initial num_batches=31): 68146 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.16128009239536886
; number reverted permutation / tried permutation: 68874 / 90099 =76.443%
; number reverted decision / tried decision: 54436 / 89900 =60.552%
; validated in 0.126s
