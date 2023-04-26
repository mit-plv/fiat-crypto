SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
mov rdx, rax
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
xor rdx, rdx
adox rax, r11
adox rcx, r10
mov r8, [ rsi + 0x8 ]
lea r9, [r8 + r8]
mov r8, [ rsi + 0x10 ]
lea r10, [r8 + 4 * r8]
mov rdx, [ rsi + 0x10 ]
mulx r11, r8, r10
mov rdx, r9
mulx r10, r9, [ rsi + 0x0 ]
adcx r8, r9
adcx r10, r11
mov r11, 0x1 
shlx r9, [ rsi + 0x10 ], r11
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, [ rsi + 0x8 ]
mov rdx, rax
shrd rdx, rcx, 44
xchg rdx, r9
mov [ rsp - 0x78 ], rbp
mulx rbp, rcx, [ rsi + 0x0 ]
test al, al
adox r11, rcx
adox rbp, rbx
adcx r8, r9
adc r10, 0x0
mov rdx, r8
shrd rdx, r10, 43
xor rbx, rbx
adox r11, rdx
adox rbp, rbx
mov r9, r11
shrd r9, rbp, 43
lea rcx, [r9 + 4 * r9]
mov r10, 0x2b 
bzhi rdx, r11, r10
mov r11, 0x2c 
bzhi rbp, rax, r11
lea rbp, [ rbp + rcx ]
bzhi rax, rbp, r11
bzhi r9, r8, r10
shr rbp, 44
lea rbp, [ rbp + r9 ]
bzhi r8, rbp, r10
shr rbp, 43
lea rbp, [ rbp + rdx ]
mov [ rdi + 0x10 ], rbp
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0154
; seed 2273213058668123 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2900 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=406, initial num_batches=31): 409 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.14103448275862068
; number reverted permutation / tried permutation: 447 / 517 =86.460%
; number reverted decision / tried decision: 335 / 482 =69.502%
; validated in 0.133s
