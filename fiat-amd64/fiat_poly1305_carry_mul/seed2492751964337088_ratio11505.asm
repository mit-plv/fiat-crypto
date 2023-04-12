SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x10 ], 0xa
imul r10, [ rdx + 0x8 ], 0xa
imul r11, [ rdx + 0x10 ], 0x5
mov rcx, rdx
mov rdx, [ rdx + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
imul rdx, [ rcx + 0x8 ], 0x2
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
test al, al
adox r8, rbx
adox rbp, r9
mov rdx, r10
mulx r9, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, rax
adcx r10, rbx
adcx r12, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, rax, [ rcx + 0x0 ]
xor rdx, rdx
adox r10, rax
adox r9, r12
mov rdx, r11
mulx rbx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rax, r12, [ rcx + 0x0 ]
adcx r11, r12
adcx rax, rbx
mov rdx, [ rsi + 0x0 ]
mulx r12, rbx, [ rcx + 0x8 ]
mov rdx, r10
shrd rdx, r9, 44
xor r9, r9
adox r11, rbx
adox r12, rax
adcx r11, rdx
adc r12, 0x0
mov rax, r11
shrd rax, r12, 43
mov rdx, [ rcx + 0x10 ]
mulx r12, rbx, [ rsi + 0x0 ]
add r8, rbx
adcx r12, rbp
mov rdx, 0x2b 
bzhi rbp, r11, rdx
adox r8, rax
adox r12, r9
bzhi r11, r8, rdx
shrd r8, r12, 43
mov rax, 0x2c 
bzhi rbx, r10, rax
imul r10, r8, 0x5
lea rbx, [ rbx + r10 ]
bzhi r12, rbx, rax
shr rbx, 44
mov [ rdi + 0x0 ], r12
lea rbx, [ rbx + rbp ]
bzhi rbp, rbx, rdx
shr rbx, 43
lea rbx, [ rbx + r11 ]
mov [ rdi + 0x10 ], rbx
mov [ rdi + 0x8 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.1505
; seed 2492751964337088 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3779 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=826, initial num_batches=31): 763 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.20190526594337127
; number reverted permutation / tried permutation: 391 / 497 =78.672%
; number reverted decision / tried decision: 328 / 502 =65.339%
; validated in 0.219s
