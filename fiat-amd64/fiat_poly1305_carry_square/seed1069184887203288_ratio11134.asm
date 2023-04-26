SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
mov r11, [ rsi + 0x10 ]
lea rdx, [r11 + 4 * r11]
mulx rcx, r11, [ rsi + 0x10 ]
imul r8, [ rsi + 0x10 ], 0x14
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, rdx
mov rdx, r8
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rsi + 0x8 ]
add r8, r9
adcx rax, rbx
mov rdx, r10
mulx r9, r10, [ rsi + 0x0 ]
mov rbx, r8
shrd rbx, rax, 44
xor rax, rax
adox r11, r10
adox r9, rcx
adcx r11, rbx
adc r9, 0x0
mov rcx, r11
shrd rcx, r9, 43
imul r10, [ rsi + 0x10 ], 0x2
mulx r9, rbx, [ rsi + 0x8 ]
mov rdx, r10
mulx rax, r10, [ rsi + 0x0 ]
xor rdx, rdx
adox rbx, r10
adox rax, r9
adcx rbx, rcx
adc rax, 0x0
mov rcx, 0x2b 
bzhi r9, rbx, rcx
shrd rbx, rax, 43
lea r10, [rbx + 4 * rbx]
mov rax, 0x2c 
bzhi rbx, r8, rax
lea rbx, [ rbx + r10 ]
mov r8, rbx
shr r8, 44
bzhi r10, rbx, rax
mov [ rdi + 0x0 ], r10
bzhi rbx, r11, rcx
lea r8, [ r8 + rbx ]
mov r11, r8
shr r11, 43
lea r11, [ r11 + r9 ]
bzhi r9, r8, rcx
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], r9
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1134
; seed 1069184887203288 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3214 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=521, initial num_batches=31): 580 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1804604853764779
; number reverted permutation / tried permutation: 408 / 474 =86.076%
; number reverted decision / tried decision: 418 / 525 =79.619%
; validated in 0.153s
