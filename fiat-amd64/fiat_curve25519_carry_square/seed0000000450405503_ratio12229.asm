SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
imul rax, [ rsi + 0x18 ], 0x26
mov r11, [ rsi + 0x18 ]
lea rdx, [r11 + 8 * r11]
lea rcx, [r11 + 2 * rdx]
imul r11, [ rsi + 0x20 ], 0x26
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
xor rdx, rdx
adox rbx, r8
adox r9, rbp
mov rdx, [ rsi + 0x0 ]
mulx r8, rax, r10
mov rdx, [ rsi + 0x0 ]
mulx rbp, r10, rdx
adcx rbx, r10
adcx rbp, r9
mov rdx, rbx
shrd rdx, rbp, 51
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, rcx
mov rdx, r11
mulx rcx, r11, [ rsi + 0x10 ]
add r10, r11
adcx rcx, rbp
xor rbp, rbp
adox r10, rax
adox r8, rcx
adcx r10, r9
adc r8, 0x0
mov rax, r10
shrd rax, r8, 51
mov r9, 0x7ffffffffffff 
and rbx, r9
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
adox r11, r8
adox rbp, rcx
adcx r11, r12
adcx r13, rbp
add r11, rax
adc r13, 0x0
mulx rcx, rax, [ rsi + 0x8 ]
imul r8, [ rsi + 0x20 ], 0x13
mov rdx, r8
mulx r12, r8, [ rsi + 0x20 ]
xor rbp, rbp
adox r8, rax
adox rcx, r12
mov rax, 0x1 
shlx rdx, [ rsi + 0x18 ], rax
mulx rbp, r12, [ rsi + 0x0 ]
mov rax, r11
shrd rax, r13, 51
add r8, r12
adcx rbp, rcx
add r8, rax
adc rbp, 0x0
mov r13, r8
shrd r13, rbp, 51
and r8, r9
mulx r12, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, rax, rdx
adox rax, rcx
adox r12, rbp
mov rdx, [ rsi + 0x20 ]
mov rcx, rdx
shl rcx, 0x1
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x0 ]
add rax, rcx
adcx rbp, r12
add rax, r13
adc rbp, 0x0
mov r13, rax
shrd r13, rbp, 51
and rax, r9
imul r12, r13, 0x13
mov [ rdi + 0x20 ], rax
lea rbx, [ rbx + r12 ]
mov rdx, rbx
shr rdx, 51
and r10, r9
lea rdx, [ rdx + r10 ]
mov rcx, rdx
shr rcx, 51
and rdx, r9
mov [ rdi + 0x8 ], rdx
and r11, r9
and rbx, r9
lea rcx, [ rcx + r11 ]
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x0 ], rbx
mov [ rdi + 0x18 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2229
; seed 1877268122374057 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 525585 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=497, initial num_batches=31): 73787 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.14039023183690555
; number reverted permutation / tried permutation: 71454 / 90165 =79.248%
; number reverted decision / tried decision: 68938 / 89834 =76.739%
; validated in 0.197s
