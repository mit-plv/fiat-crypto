SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + rax]
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, rax
mulx r8, rax, [ rsi + 0x8 ]
mov r9, [ rsi + 0x10 ]
lea rdx, [r9 + 4 * r9]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
add rax, r11
adcx rcx, r8
mov r11, rax
shrd r11, rcx, 44
mov r8, 0x1 
shlx rdx, [ rsi + 0x8 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
add r9, rcx
adcx r8, rbx
add r9, r11
adc r8, 0x0
mov rbx, r9
shrd rbx, r8, 43
xchg rdx, r10
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, r10
mulx r8, r10, [ rsi + 0x8 ]
test al, al
adox r10, r11
adox rcx, r8
adcx r10, rbx
adc rcx, 0x0
mov rdx, 0x7ffffffffff 
mov rbx, r10
and rbx, rdx
and r9, rdx
shrd r10, rcx, 43
mov r11, 0x2c 
bzhi r8, rax, r11
lea rax, [r10 + 4 * r10]
lea r8, [ r8 + rax ]
mov rcx, r8
shr rcx, 44
lea rcx, [ rcx + r9 ]
bzhi r9, r8, r11
mov [ rdi + 0x0 ], r9
mov r10, rcx
and r10, rdx
shr rcx, 43
lea rcx, [ rcx + rbx ]
mov [ rdi + 0x10 ], rcx
mov [ rdi + 0x8 ], r10
mov rbx, [ rsp - 0x80 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0156
; seed 4013773482995318 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2786 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=407, initial num_batches=31): 426 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.15290739411342427
; number reverted permutation / tried permutation: 381 / 491 =77.597%
; number reverted decision / tried decision: 321 / 508 =63.189%
; validated in 0.131s
