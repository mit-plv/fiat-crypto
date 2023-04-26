SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
imul r10, [ rdx + 0x10 ], 0xa
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, r10
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rcx
adox r8, r9
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ r11 + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ r11 + 0x0 ]
adcx rax, r10
adcx rcx, r8
imul rdx, [ r11 + 0x10 ], 0x5
mulx r10, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r9
adox rbx, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r9, [ r11 + 0x8 ]
adcx r8, r9
adcx r10, rbx
mov rdx, rax
shrd rdx, rcx, 44
add r8, rdx
adc r10, 0x0
mov rcx, [ r11 + 0x8 ]
mov rbx, rcx
shl rbx, 0x1
mov rdx, rbx
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ r11 + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
mov rdx, r8
shrd rdx, r10, 43
xor r10, r10
adox r9, rcx
adox rbx, rbp
mov rcx, rdx
mov rdx, [ r11 + 0x10 ]
mulx r10, rbp, [ rsi + 0x0 ]
adcx r9, rbp
adcx r10, rbx
add r9, rcx
adc r10, 0x0
mov rdx, r9
shrd rdx, r10, 43
lea rcx, [rdx + 4 * rdx]
mov rbx, 0x7ffffffffff 
and r9, rbx
mov rbp, 0xfffffffffff 
and rax, rbp
lea rax, [ rax + rcx ]
mov r10, rax
and r10, rbp
and r8, rbx
shr rax, 44
lea rax, [ rax + r8 ]
mov rdx, rax
and rdx, rbx
mov [ rdi + 0x8 ], rdx
shr rax, 43
lea rax, [ rax + r9 ]
mov [ rdi + 0x10 ], rax
mov [ rdi + 0x0 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2472
; seed 1614856589419447 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 333700 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=751, initial num_batches=31): 67096 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.20106682649086005
; number reverted permutation / tried permutation: 72454 / 89973 =80.529%
; number reverted decision / tried decision: 69174 / 90026 =76.838%
; validated in 0.099s
