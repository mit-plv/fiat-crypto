SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + 4 * rax]
mov rax, [ rsi + 0x10 ]
mov r11, rax
shl r11, 0x1
mov rax, [ rsi + 0x8 ]
lea rdx, [rax + rax]
imul rax, [ rsi + 0x10 ], 0x14
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
xor rdx, rdx
adox rbx, r8
adox r9, rbp
mov rdx, r10
mulx rax, r10, [ rsi + 0x10 ]
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x0 ]
adcx r10, rcx
adcx r8, rax
mov rbp, rbx
shrd rbp, r9, 44
xor r9, r9
adox r10, rbp
adox r8, r9
mov rax, 0x2b 
bzhi rcx, r10, rax
shrd r10, r8, 43
mulx r8, rbp, [ rsi + 0x8 ]
mov rdx, r11
mulx r9, r11, [ rsi + 0x0 ]
add rbp, r11
adcx r9, r8
xor rdx, rdx
adox rbp, r10
adox r9, rdx
mov r10, rbp
shrd r10, r9, 43
bzhi r8, rbp, rax
lea r11, [r10 + 4 * r10]
mov rbp, 0x2c 
bzhi r9, rbx, rbp
lea r9, [ r9 + r11 ]
bzhi rbx, r9, rbp
mov [ rdi + 0x0 ], rbx
shr r9, 44
lea r9, [ r9 + rcx ]
mov rcx, r9
shr rcx, 43
lea rcx, [ rcx + r8 ]
bzhi r10, r9, rax
mov [ rdi + 0x8 ], r10
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1346
; seed 1076519909723230 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1868 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=684, initial num_batches=31): 386 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.20663811563169165
; number reverted permutation / tried permutation: 371 / 515 =72.039%
; number reverted decision / tried decision: 358 / 484 =73.967%
; validated in 0.103s
