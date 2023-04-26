SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, [ rsi + 0x10 ]
lea r10, [rax + rax]
mov rax, 0x1 
shlx r11, [ rsi + 0x8 ], rax
imul rdx, [ rsi + 0x10 ], 0x14
mulx r8, rcx, [ rsi + 0x8 ]
mov r9, [ rsi + 0x10 ]
lea rdx, [r9 + 4 * r9]
mulx rax, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
xor rdx, rdx
adox rcx, rbx
adox rbp, r8
mov rdx, r11
mulx r8, r11, [ rsi + 0x0 ]
adcx r9, r11
adcx r8, rax
mulx rbx, rax, [ rsi + 0x8 ]
mov rdx, r10
mulx r11, r10, [ rsi + 0x0 ]
add rax, r10
adcx r11, rbx
mov rdx, rcx
shrd rdx, rbp, 44
xor rbp, rbp
adox r9, rdx
adox r8, rbp
mov rbx, r9
shrd rbx, r8, 43
mov r10, 0x7ffffffffff 
and r9, r10
adox rax, rbx
adox r11, rbp
mov rdx, rax
shrd rdx, r11, 43
lea r8, [rdx + 4 * rdx]
mov rbx, 0x2c 
bzhi r11, rcx, rbx
lea r11, [ r11 + r8 ]
mov rcx, r11
shr rcx, 44
lea rcx, [ rcx + r9 ]
bzhi r9, r11, rbx
mov rdx, rcx
and rdx, r10
shr rcx, 43
mov [ rdi + 0x8 ], rdx
and rax, r10
lea rcx, [ rcx + rax ]
mov [ rdi + 0x0 ], r9
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1149
; seed 4186664072736326 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1905 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=618, initial num_batches=31): 381 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.2
; number reverted permutation / tried permutation: 420 / 490 =85.714%
; number reverted decision / tried decision: 390 / 509 =76.621%
; validated in 0.101s
