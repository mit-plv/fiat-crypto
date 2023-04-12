SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x26
imul r10, [ rsi + 0x20 ], 0x26
mov rdx, rax
mulx r11, rax, [ rsi + 0x10 ]
mov rcx, [ rsi + 0x18 ]
lea r8, [rcx + 8 * rcx]
lea r9, [rcx + 2 * r8]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, r10
xor rdx, rdx
adox rax, rcx
adox r8, r11
mov rdx, r9
mulx r11, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
lea rcx, [rdx + rdx]
mov rdx, rcx
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
adcx rax, rbp
adcx r12, r8
mov rdx, r10
mulx r8, r10, [ rsi + 0x10 ]
xor rbp, rbp
adox r9, r10
adox r8, r11
adcx r9, rcx
adcx rbx, r8
mov r11, rax
shrd r11, r12, 51
add r9, r11
adc rbx, 0x0
mulx r12, rcx, [ rsi + 0x18 ]
mov rdx, r9
shrd rdx, rbx, 51
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r8, rdx
add rcx, r8
adcx r11, r12
mov rdx, [ rsi + 0x10 ]
lea rbx, [rdx + rdx]
mov rdx, rbx
mulx r12, rbx, [ rsi + 0x0 ]
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
xor rdx, rdx
adox rcx, rbx
adox r12, r11
adcx rcx, r10
adc r12, 0x0
mov r13, rcx
shrd r13, r12, 51
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, r14
imul rdx, [ rsi + 0x18 ], 0x2
mulx r14, rbx, [ rsi + 0x0 ]
add r10, r8
adcx rbp, r11
mov r8, 0x7ffffffffffff 
and rcx, r8
adox r10, rbx
adox r14, rbp
adcx r10, r13
adc r14, 0x0
mov r12, r10
and r12, r8
shrd r10, r14, 51
mov r13, [ rsi + 0x20 ]
lea r11, [r13 + r13]
mulx rbx, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, rbp, rdx
add rbp, r13
adcx rbx, r14
mov rdx, r11
mulx r13, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, r11
adox r13, rbx
adcx rbp, r10
adc r13, 0x0
mov r10, rbp
shrd r10, r13, 51
and rbp, r8
mov [ rdi + 0x20 ], rbp
imul r14, r10, 0x13
and rax, r8
lea rax, [ rax + r14 ]
mov rbx, rax
and rbx, r8
shr rax, 51
and r9, r8
mov [ rdi + 0x0 ], rbx
lea rax, [ rax + r9 ]
mov r11, rax
shr r11, 51
lea r11, [ r11 + rcx ]
mov [ rdi + 0x18 ], r12
and rax, r8
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2192
; seed 1618277225930397 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 532448 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=507, initial num_batches=31): 74435 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.13979768916401225
; number reverted permutation / tried permutation: 70900 / 90007 =78.772%
; number reverted decision / tried decision: 68464 / 89992 =76.078%
; validated in 0.195s
