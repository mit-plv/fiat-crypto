SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x0 ]
imul rdx, [ r10 + 0x10 ], 0xa
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
imul rdx, [ r10 + 0x10 ], 0x5
mov [ rsp - 0x70 ], r12
mulx r12, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ r10 + 0x0 ]
xor rdx, rdx
adox rax, r13
adox r14, r12
mov rdx, [ r10 + 0x8 ]
mulx r13, r12, [ rsi + 0x0 ]
adcx rax, r12
adcx r13, r14
imul rdx, [ r10 + 0x8 ], 0x2
add rbx, r8
adcx r9, rbp
xor r8, r8
adox rbx, r11
adox rcx, r9
mulx rbp, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, [ r10 + 0x0 ]
adcx r14, r11
adcx rbp, r12
mov rdx, [ rsi + 0x0 ]
mulx r11, r9, [ r10 + 0x10 ]
mov rdx, 0x2c 
bzhi r12, rbx, rdx
shrd rbx, rcx, 44
xor rcx, rcx
adox rax, rbx
adox r13, rcx
mov r8, 0x2b 
bzhi rbx, rax, r8
adox r14, r9
adox r11, rbp
shrd rax, r13, 43
xor rbp, rbp
adox r14, rax
adox r11, rbp
bzhi rcx, r14, r8
shrd r14, r11, 43
imul r9, r14, 0x5
lea r12, [ r12 + r9 ]
bzhi r13, r12, rdx
mov [ rdi + 0x0 ], r13
shr r12, 44
lea r12, [ r12 + rbx ]
bzhi rbx, r12, r8
mov [ rdi + 0x8 ], rbx
shr r12, 43
lea r12, [ r12 + rcx ]
mov [ rdi + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.5015
; seed 0384723549833557 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3680 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=616, initial num_batches=31): 675 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18342391304347827
; number reverted permutation / tried permutation: 454 / 514 =88.327%
; number reverted decision / tried decision: 358 / 485 =73.814%
; validated in 0.221s
