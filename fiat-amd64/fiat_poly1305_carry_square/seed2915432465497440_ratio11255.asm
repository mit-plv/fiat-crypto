SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rax
mov rdx, [ rsi + 0x10 ]
lea rcx, [rdx + 4 * rdx]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rcx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rax, rdx
test al, al
adox r10, rax
adox rcx, r11
mov rdx, [ rsi + 0x8 ]
lea r11, [rdx + rdx]
mov rdx, r10
shrd rdx, rcx, 44
xchg rdx, r11
mulx rcx, rax, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
xor rbx, rbx
adox r8, rax
adox rcx, r9
adcx r8, r11
adc rcx, 0x0
mov r9, r8
shrd r9, rcx, 43
mulx rax, r11, [ rsi + 0x8 ]
mov rdx, 0x1 
shlx rcx, [ rsi + 0x10 ], rdx
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x0 ]
test al, al
adox r11, rcx
adox rbx, rax
adcx r11, r9
adc rbx, 0x0
mov r9, 0x7ffffffffff 
mov rax, r11
and rax, r9
shrd r11, rbx, 43
lea rdx, [r11 + 4 * r11]
mov rcx, 0xfffffffffff 
and r10, rcx
lea r10, [ r10 + rdx ]
mov rbx, r10
shr rbx, 44
and r10, rcx
and r8, r9
lea rbx, [ rbx + r8 ]
mov r11, rbx
and r11, r9
mov [ rdi + 0x8 ], r11
shr rbx, 43
mov [ rdi + 0x0 ], r10
lea rbx, [ rbx + rax ]
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1255
; seed 2915432465497440 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1844 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=684, initial num_batches=31): 372 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.2017353579175705
; number reverted permutation / tried permutation: 359 / 506 =70.949%
; number reverted decision / tried decision: 330 / 493 =66.937%
; validated in 0.103s
