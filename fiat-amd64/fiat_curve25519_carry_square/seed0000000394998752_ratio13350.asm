SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x18 ], rax
mov r11, [ rsi + 0x18 ]
lea rdx, [r11 + 8 * r11]
lea rcx, [r11 + 2 * rdx]
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, rdx
imul rdx, [ rsi + 0x18 ], 0x26
mulx rax, r9, [ rsi + 0x10 ]
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
xor r12, r12
adox r9, rbx
adox rbp, rax
mulx rbx, rax, [ rsi + 0x10 ]
adcx r9, r11
adcx r8, rbp
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, rbp, rcx
add rbp, rax
adcx rbx, r12
mov rdx, [ rsi + 0x8 ]
lea rcx, [rdx + rdx]
mov rdx, rcx
mulx rax, rcx, [ rsi + 0x0 ]
mov r12, r9
shrd r12, r8, 51
mov rdx, r11
mulx r8, r11, [ rsi + 0x18 ]
add rbp, rcx
adcx rax, rbx
xor rdx, rdx
adox rbp, r12
adox rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, rdx
adcx r11, rbx
adcx rcx, r8
mov rdx, [ rsi + 0x10 ]
lea r12, [rdx + rdx]
mov rdx, r12
mulx r8, r12, [ rsi + 0x0 ]
add r11, r12
adcx r8, rcx
mulx rcx, rbx, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x20 ], 0x13
mov r12, rbp
shrd r12, rax, 51
add r11, r12
adc r8, 0x0
mulx r12, rax, [ rsi + 0x20 ]
mov rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, r10, [ rsi + 0x8 ]
add rax, rbx
adcx rcx, r12
mulx r12, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, rbx
adox r12, rcx
mov rcx, r11
shrd rcx, r8, 51
mov rdx, [ rsi + 0x10 ]
mulx rbx, r8, rdx
xor rdx, rdx
adox rax, rcx
adox r12, rdx
mov rcx, rax
shrd rcx, r12, 51
mov r12, [ rsi + 0x20 ]
lea rdx, [r12 + r12]
xor r12, r12
adox r8, r10
adox r13, rbx
mulx rbx, r10, [ rsi + 0x0 ]
adcx r8, r10
adcx rbx, r13
xor rdx, rdx
adox r8, rcx
adox rbx, rdx
mov r12, r8
shrd r12, rbx, 51
mov rcx, 0x7ffffffffffff 
and r8, rcx
and r9, rcx
imul r13, r12, 0x13
mov [ rdi + 0x20 ], r8
lea r9, [ r9 + r13 ]
mov r10, r9
and r10, rcx
shr r9, 51
and rbp, rcx
and r11, rcx
lea r9, [ r9 + rbp ]
mov rbx, r9
and rbx, rcx
mov [ rdi + 0x0 ], r10
shr r9, 51
and rax, rcx
mov [ rdi + 0x18 ], rax
lea r9, [ r9 + r11 ]
mov [ rdi + 0x8 ], rbx
mov [ rdi + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3350
; seed 1101302929159760 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 474511 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=538, initial num_batches=31): 70774 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.14915144222157126
; number reverted permutation / tried permutation: 70585 / 89492 =78.873%
; number reverted decision / tried decision: 69137 / 90507 =76.389%
; validated in 0.17s
