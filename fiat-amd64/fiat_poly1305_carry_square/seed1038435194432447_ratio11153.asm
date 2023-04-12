SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov r10, [ rsi + 0x10 ]
lea r11, [r10 + 4 * r10]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, r11
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rax
mov rdx, [ rsi + 0x0 ]
mulx r11, rax, rdx
xor rdx, rdx
adox r8, rax
adox r11, r9
imul r9, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, r9
mov rdx, r8
shrd rdx, r11, 44
xor r11, r11
adox r10, rax
adox rbx, rcx
adcx r10, rdx
adc rbx, 0x0
imul rcx, [ rsi + 0x10 ], 0x2
mov rax, r10
shrd rax, rbx, 43
mov rdx, [ rsi + 0x8 ]
mulx r11, rbx, r9
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, 0x7ffffffffff 
and r10, rdx
adox rbx, rcx
adox r9, r11
adcx rbx, rax
adc r9, 0x0
mov rax, rbx
shrd rax, r9, 43
and rbx, rdx
mov r11, 0x2c 
bzhi rcx, r8, r11
imul r8, rax, 0x5
lea rcx, [ rcx + r8 ]
bzhi r9, rcx, r11
shr rcx, 44
lea rcx, [ rcx + r10 ]
mov r10, rcx
and r10, rdx
mov [ rdi + 0x8 ], r10
shr rcx, 43
lea rcx, [ rcx + rbx ]
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1153
; seed 1038435194432447 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4161 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=1099, initial num_batches=31): 762 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18312905551550107
; number reverted permutation / tried permutation: 402 / 479 =83.925%
; number reverted decision / tried decision: 403 / 520 =77.500%
; validated in 0.169s
