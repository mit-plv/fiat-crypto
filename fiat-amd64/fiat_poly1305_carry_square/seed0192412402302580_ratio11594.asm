SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x10 ], 0x14
imul r10, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rax
test al, al
adox r8, r11
adox rcx, r9
imul rdx, [ rsi + 0x10 ], 0x5
mov rax, r8
shrd rax, rcx, 44
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, r10
imul rdx, [ rsi + 0x10 ], 0x2
add r11, rcx
adcx rbx, r9
mulx rcx, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, rax
adox rbx, rdx
mov rax, r11
shrd rax, rbx, 43
mov rdx, r10
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, 0x7ffffffffff 
and r11, rdx
adox r10, r9
adox rcx, rbx
adcx r10, rax
adc rcx, 0x0
mov r9, r10
shrd r9, rcx, 43
mov rax, 0x2c 
bzhi rbx, r8, rax
lea r8, [r9 + 4 * r9]
lea rbx, [ rbx + r8 ]
mov rcx, rbx
shr rcx, 44
lea rcx, [ rcx + r11 ]
bzhi r11, rbx, rax
mov r9, rcx
shr r9, 43
and rcx, rdx
and r10, rdx
mov [ rdi + 0x8 ], rcx
lea r9, [ r9 + r10 ]
mov [ rdi + 0x10 ], r9
mov [ rdi + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1594
; seed 0192412402302580 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2134 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=568, initial num_batches=31): 385 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18041237113402062
; number reverted permutation / tried permutation: 379 / 529 =71.645%
; number reverted decision / tried decision: 347 / 470 =73.830%
; validated in 0.131s
