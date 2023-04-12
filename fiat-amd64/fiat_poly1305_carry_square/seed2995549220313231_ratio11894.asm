SECTION .text
	GLOBAL fiat_poly1305_carry_square
fiat_poly1305_carry_square:
imul rax, [ rsi + 0x8 ], 0x2
imul r10, [ rsi + 0x10 ], 0x14
mov rdx, r10
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
add r10, r9
adcx rbx, r11
imul rdx, [ rsi + 0x10 ], 0x5
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, r10
shrd rdx, rbx, 44
xor rbx, rbx
adox r11, rcx
adox r8, r9
adcx r11, rdx
adc r8, 0x0
mov rcx, r11
shrd rcx, r8, 43
mov rdx, rax
mulx r9, rax, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x10 ], 0x2
mulx rbx, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r8
adox rbx, r9
adcx rax, rcx
adc rbx, 0x0
mov rcx, 0x2c 
bzhi r9, r10, rcx
mov r10, 0x2b 
bzhi r8, rax, r10
shrd rax, rbx, 43
lea rbx, [rax + 4 * rax]
lea r9, [ r9 + rbx ]
bzhi rax, r11, r10
mov r11, r9
shr r11, 44
lea r11, [ r11 + rax ]
bzhi rbx, r11, r10
shr r11, 43
bzhi rax, r9, rcx
lea r11, [ r11 + r8 ]
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], rbx
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1894
; seed 2995549220313231 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2859 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=581, initial num_batches=31): 371 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1297656523259881
; number reverted permutation / tried permutation: 431 / 505 =85.347%
; number reverted decision / tried decision: 397 / 494 =80.364%
; validated in 0.129s
