SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
imul r10, [ rdx + 0x10 ], 0xa
mov r11, rdx
mov rdx, [ rdx + 0x0 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, rax
test al, al
adox r10, r9
adox rbx, rbp
mov rdx, [ r11 + 0x0 ]
mulx r9, rax, [ rsi + 0x0 ]
adcx r10, rax
adcx r9, rbx
imul rdx, [ r11 + 0x10 ], 0x5
mov rbp, r10
shrd rbp, r9, 44
mulx rax, rbx, [ rsi + 0x10 ]
add rbx, rcx
adcx r8, rax
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, [ r11 + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rax, [ r11 + 0x8 ]
imul rdx, [ r11 + 0x8 ], 0x2
add rbx, rax
adcx r12, r8
add rbx, rbp
adc r12, 0x0
mulx r8, rbp, [ rsi + 0x8 ]
add rcx, rbp
adcx r8, r9
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, [ r11 + 0x10 ]
mov rdx, rbx
shrd rdx, r12, 43
xor r12, r12
adox rcx, r9
adox rax, r8
adcx rcx, rdx
adc rax, 0x0
mov rbp, 0x2b 
bzhi r8, rbx, rbp
mov rbx, rcx
shrd rbx, rax, 43
imul r9, rbx, 0x5
mov rdx, 0x2c 
bzhi rax, r10, rdx
lea rax, [ rax + r9 ]
bzhi r10, rax, rdx
shr rax, 44
lea rax, [ rax + r8 ]
bzhi r8, rax, rbp
mov [ rdi + 0x8 ], r8
bzhi rbx, rcx, rbp
shr rax, 43
lea rax, [ rax + rbx ]
mov [ rdi + 0x0 ], r10
mov [ rdi + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1674
; seed 3066586779205530 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4091 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=410, initial num_batches=31): 575 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.14055243216817404
; number reverted permutation / tried permutation: 414 / 505 =81.980%
; number reverted decision / tried decision: 352 / 494 =71.255%
; validated in 0.188s
