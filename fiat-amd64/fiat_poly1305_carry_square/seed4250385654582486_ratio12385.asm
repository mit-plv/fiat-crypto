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
mov r9, r11
shrd r9, r10, 44
mov rax, [ rsi + 0x10 ]
lea rdx, [rax + 4 * rax]
mulx rcx, rax, [ rsi + 0x10 ]
mov r10, [ rsi + 0x8 ]
lea rdx, [r10 + r10]
mulx r8, r10, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox rax, r10
adox r8, rcx
adcx rax, r9
adc r8, 0x0
mov r9, rax
shrd r9, r8, 43
imul rcx, [ rsi + 0x10 ], 0x2
mulx r8, r10, [ rsi + 0x8 ]
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, rcx
adox rbx, r8
adcx r10, r9
adc rbx, 0x0
mov r9, r10
shrd r9, rbx, 43
lea r8, [r9 + 4 * r9]
mov rcx, 0xfffffffffff 
and r11, rcx
lea r11, [ r11 + r8 ]
mov rbx, r11
shr rbx, 44
mov r9, 0x7ffffffffff 
and rax, r9
lea rbx, [ rbx + rax ]
mov r8, rbx
and r8, r9
shr rbx, 43
and r10, r9
lea rbx, [ rbx + r10 ]
mov [ rdi + 0x10 ], rbx
and r11, rcx
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2385
; seed 4250385654582486 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2015 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1185, initial num_batches=31): 362 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.17965260545905706
; number reverted permutation / tried permutation: 351 / 481 =72.973%
; number reverted decision / tried decision: 425 / 518 =82.046%
; validated in 0.067s
