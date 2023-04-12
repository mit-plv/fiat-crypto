SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
imul r11, [ rsi + 0x10 ], 0x5
imul rdx, [ rsi + 0x10 ], 0x14
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, r11
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rax, r10
add r11, rax
adcx rbx, r9
mov rdx, [ rsi + 0x0 ]
mulx rax, r9, rdx
add rcx, r9
adcx rax, r8
mov rdx, rcx
shrd rdx, rax, 44
mov r8, [ rsi + 0x10 ]
mov r9, r8
shl r9, 0x1
add r11, rdx
adc rbx, 0x0
mov rdx, r10
mulx r8, r10, [ rsi + 0x8 ]
mov rdx, r9
mulx rax, r9, [ rsi + 0x0 ]
mov rdx, r11
shrd rdx, rbx, 43
xor rbx, rbx
adox r10, r9
adox rax, r8
adcx r10, rdx
adc rax, 0x0
mov r8, r10
shrd r8, rax, 43
imul r9, r8, 0x5
mov rdx, 0x2c 
bzhi rax, rcx, rdx
lea rax, [ rax + r9 ]
bzhi rcx, rax, rdx
shr rax, 44
mov r8, 0x2b 
bzhi r9, r11, r8
lea rax, [ rax + r9 ]
bzhi r11, rax, r8
shr rax, 43
bzhi r9, r10, r8
mov [ rdi + 0x8 ], r11
lea rax, [ rax + r9 ]
mov [ rdi + 0x10 ], rax
mov [ rdi + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1301
; seed 3195483375317184 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2149 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=583, initial num_batches=31): 355 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.16519311307584922
; number reverted permutation / tried permutation: 410 / 496 =82.661%
; number reverted decision / tried decision: 429 / 503 =85.288%
; validated in 0.13s
