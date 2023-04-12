SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, [ rsi + 0x8 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x18 ]
mulx rcx, rax, r11
imul rdx, [ rsi + 0x20 ], 0x26
mulx r9, r8, [ rsi + 0x8 ]
imul r11, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
xor r12, r12
adox rax, rbx
adox rbp, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, rbx, r11
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
adcx rbx, r8
adcx r9, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r8, rdx
xor rdx, rdx
adox rbx, r8
adox r12, r9
adcx rax, r10
adcx r11, rbp
mov rdx, [ rsi + 0x18 ]
mulx r10, rbp, rcx
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, rdx
mov rdx, rbx
shrd rdx, r12, 51
xor r8, r8
adox rax, rdx
adox r11, r8
mov r12, [ rsi + 0x10 ]
lea rdx, [r12 + r12]
mulx r8, r12, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov r13, rax
shrd r13, r11, 51
xor r11, r11
adox rbp, rcx
adox r9, r10
adcx rbp, r12
adcx r8, r9
add rbp, r13
adc r8, 0x0
imul r10, [ rsi + 0x20 ], 0x13
mulx r12, rcx, [ rsi + 0x8 ]
mov rdx, r10
mulx r13, r10, [ rsi + 0x20 ]
mov r9, [ rsi + 0x18 ]
lea rdx, [r9 + r9]
xor r9, r9
adox r10, rcx
adox r12, r13
mulx rcx, r11, [ rsi + 0x0 ]
mulx r9, r13, [ rsi + 0x8 ]
adcx r10, r11
adcx rcx, r12
mov rdx, [ rsi + 0x10 ]
mulx r11, r12, rdx
add r12, r13
adcx r9, r11
mov rdx, rbp
shrd rdx, r8, 51
add r10, rdx
adc rcx, 0x0
mov r8, r10
shrd r8, rcx, 51
mov r13, 0x7ffffffffffff 
and r10, r13
mov r11, 0x1 
shlx rdx, [ rsi + 0x20 ], r11
mulx r11, rcx, [ rsi + 0x0 ]
adox r12, rcx
adox r11, r9
adcx r12, r8
adc r11, 0x0
mov r9, r12
shrd r9, r11, 51
and r12, r13
mov [ rdi + 0x20 ], r12
and rbx, r13
imul r8, r9, 0x13
lea rbx, [ rbx + r8 ]
mov rdx, rbx
and rdx, r13
mov [ rdi + 0x0 ], rdx
and rax, r13
and rbp, r13
shr rbx, 51
mov [ rdi + 0x18 ], r10
lea rbx, [ rbx + rax ]
mov r10, rbx
shr r10, 51
and rbx, r13
mov [ rdi + 0x8 ], rbx
lea r10, [ r10 + rbp ]
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3212
; seed 0833655896701052 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 473320 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=539, initial num_batches=31): 70916 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.14982675568325868
; number reverted permutation / tried permutation: 70288 / 89726 =78.336%
; number reverted decision / tried decision: 68481 / 90273 =75.860%
; validated in 0.171s
