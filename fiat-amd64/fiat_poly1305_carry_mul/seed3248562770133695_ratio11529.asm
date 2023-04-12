SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
imul rdx, [ rax + 0x8 ], 0xa
mulx r8, rcx, [ rsi + 0x10 ]
imul r9, [ rax + 0x10 ], 0xa
imul rdx, [ rax + 0x10 ], 0x5
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, r9
mov [ rsp - 0x70 ], r12
mulx r12, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r9
adox r12, r8
mov rdx, [ rax + 0x0 ]
mulx r9, r8, [ rsi + 0x0 ]
adcx rcx, r8
adcx r9, r12
mov rdx, rcx
shrd rdx, r9, 44
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x0 ]
add rbx, r8
adcx r9, rbp
test al, al
adox rbx, r10
adox r11, r9
adcx rbx, r12
adc r11, 0x0
imul rdx, [ rax + 0x8 ], 0x2
mulx rbp, r10, [ rsi + 0x8 ]
mov r12, rbx
shrd r12, r11, 43
mov rdx, [ rax + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
add r8, r10
adcx rbp, r9
mov rdx, [ rax + 0x10 ]
mulx r10, r11, [ rsi + 0x0 ]
test al, al
adox r8, r11
adox r10, rbp
adcx r8, r12
adc r10, 0x0
mov rdx, 0x2b 
bzhi r12, r8, rdx
shrd r8, r10, 43
mov r9, 0x2c 
bzhi rbp, rcx, r9
lea rcx, [r8 + 4 * r8]
lea rbp, [ rbp + rcx ]
bzhi r11, rbp, r9
shr rbp, 44
bzhi r10, rbx, rdx
lea rbp, [ rbp + r10 ]
bzhi rbx, rbp, rdx
shr rbp, 43
lea rbp, [ rbp + r12 ]
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x10 ], rbp
mov [ rdi + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1529
; seed 3248562770133695 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4075 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=421, initial num_batches=31): 622 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.15263803680981594
; number reverted permutation / tried permutation: 366 / 482 =75.934%
; number reverted decision / tried decision: 364 / 517 =70.406%
; validated in 0.187s
