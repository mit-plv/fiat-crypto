SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x8 ], 0x2
imul rdx, [ rsi + 0x10 ], 0x14
mulx r8, rcx, [ rsi + 0x8 ]
xor r9, r9
adox rcx, rax
adox r10, r8
imul rax, [ rsi + 0x10 ], 0x5
mov rdx, rax
mulx r8, rax, [ rsi + 0x10 ]
mov rdx, r11
mulx r9, r11, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov rbx, rcx
shrd rbx, r10, 44
xor r10, r10
adox rax, r11
adox r9, r8
adcx rax, rbx
adc r9, 0x0
mov r8, [ rsi + 0x10 ]
lea r11, [r8 + r8]
mov r8, rax
shrd r8, r9, 43
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, r11
mulx r10, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, r11
adox r10, r9
adcx rbx, r8
adc r10, 0x0
mov r8, rbx
shrd r8, r10, 43
lea r9, [r8 + 4 * r8]
mov r11, 0xfffffffffff 
and rcx, r11
lea rcx, [ rcx + r9 ]
mov r10, rcx
shr r10, 44
mov r8, 0x7ffffffffff 
and rax, r8
lea r10, [ r10 + rax ]
mov r9, r10
shr r9, 43
and r10, r8
and rbx, r8
and rcx, r11
lea r9, [ r9 + rbx ]
mov [ rdi + 0x0 ], rcx
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x10 ], r9
mov rbx, [ rsp - 0x80 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2345
; seed 0176785039699776 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 256924 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1185, initial num_batches=31): 66305 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.2580724260870919
; number reverted permutation / tried permutation: 72095 / 89773 =80.308%
; number reverted decision / tried decision: 77949 / 90226 =86.393%
; validated in 0.069s
