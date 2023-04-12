SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, rax
mulx r10, rax, [ rsi + 0x8 ]
mov r11, [ rsi + 0x10 ]
mov rcx, r11
shl rcx, 0x1
imul r11, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
imul rdx, [ rsi + 0x10 ], 0x5
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox rax, r8
adox r9, r10
mulx r8, r10, [ rsi + 0x10 ]
mov rdx, r11
mulx rbx, r11, [ rsi + 0x0 ]
adcx r10, r11
adcx rbx, r8
mov r8, rax
shrd r8, r9, 44
xor r9, r9
adox r10, r8
adox rbx, r9
mov r11, r10
shrd r11, rbx, 43
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, 0xfffffffffff 
and rax, rdx
adox r8, rcx
adox r9, rbx
adcx r8, r11
adc r9, 0x0
mov r11, r8
shrd r11, r9, 43
lea rbx, [r11 + 4 * r11]
lea rax, [ rax + rbx ]
mov rcx, rax
and rcx, rdx
shr rax, 44
mov r9, 0x7ffffffffff 
and r10, r9
lea rax, [ rax + r10 ]
mov r11, rax
shr r11, 43
and r8, r9
mov [ rdi + 0x0 ], rcx
lea r11, [ r11 + r8 ]
mov [ rdi + 0x10 ], r11
and rax, r9
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.2226
; seed 1137474026432199 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1516 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1008, initial num_batches=31): 361 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.23812664907651715
; number reverted permutation / tried permutation: 376 / 480 =78.333%
; number reverted decision / tried decision: 444 / 519 =85.549%
; validated in 0.077s
