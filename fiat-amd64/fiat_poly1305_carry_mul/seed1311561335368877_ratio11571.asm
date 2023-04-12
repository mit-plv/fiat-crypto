SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0x2
imul r10, [ rdx + 0x10 ], 0x5
imul r11, [ rdx + 0x8 ], 0xa
mov rcx, rdx
mov rdx, [ rdx + 0x0 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
imul rdx, [ rcx + 0x10 ], 0xa
mov [ rsp - 0x70 ], r12
mulx r12, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r11
adox r12, rbp
mov rdx, rax
mulx rbp, rax, [ rsi + 0x8 ]
adcx rbx, r8
adcx r9, r12
mov rdx, [ rcx + 0x0 ]
mulx r11, r8, [ rsi + 0x10 ]
test al, al
adox r8, rax
adox rbp, r11
mov rdx, [ rcx + 0x10 ]
mulx rax, r12, [ rsi + 0x0 ]
adcx r8, r12
adcx rax, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r11, [ rcx + 0x0 ]
mov rdx, r10
mulx r12, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, r11
adox rbp, r12
mov r11, rbx
shrd r11, r9, 44
mov rdx, [ rsi + 0x0 ]
mulx r12, r9, [ rcx + 0x8 ]
xor rdx, rdx
adox r10, r9
adox r12, rbp
adcx r10, r11
adc r12, 0x0
mov rbp, r10
shrd rbp, r12, 43
mov r11, 0x2b 
bzhi r9, r10, r11
adox r8, rbp
adox rax, rdx
mov r10, r8
shrd r10, rax, 43
mov r12, 0x2c 
bzhi rbp, rbx, r12
lea rbx, [r10 + 4 * r10]
lea rbp, [ rbp + rbx ]
bzhi rax, rbp, r12
shr rbp, 44
lea rbp, [ rbp + r9 ]
mov [ rdi + 0x0 ], rax
bzhi r9, rbp, r11
bzhi r10, r8, r11
mov [ rdi + 0x8 ], r9
shr rbp, 43
lea rbp, [ rbp + r10 ]
mov [ rdi + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1571
; seed 1311561335368877 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3921 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=827, initial num_batches=31): 756 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1928079571537873
; number reverted permutation / tried permutation: 421 / 496 =84.879%
; number reverted decision / tried decision: 366 / 503 =72.763%
; validated in 0.222s
