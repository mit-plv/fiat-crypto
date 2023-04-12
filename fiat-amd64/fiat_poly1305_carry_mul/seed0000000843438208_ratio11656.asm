SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
imul r10, [ rdx + 0x10 ], 0xa
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, r10
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
add rax, rcx
adcx r8, r9
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ r11 + 0x0 ]
imul rdx, [ r11 + 0x10 ], 0x5
add rax, r10
adcx rcx, r8
mov r9, rax
shrd r9, rcx, 44
mulx r10, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ r11 + 0x0 ]
xor rdx, rdx
adox r8, rcx
adox rbx, r10
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, [ r11 + 0x8 ]
adcx r8, r10
adcx rcx, rbx
imul rdx, [ r11 + 0x8 ], 0x2
add r8, r9
adc rcx, 0x0
mulx rbx, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ r11 + 0x0 ]
add r10, r9
adcx rbx, rbp
mov rdx, [ r11 + 0x10 ]
mulx rbp, r9, [ rsi + 0x0 ]
add r10, r9
adcx rbp, rbx
mov rdx, r8
shrd rdx, rcx, 43
add r10, rdx
adc rbp, 0x0
mov rcx, r10
shrd rcx, rbp, 43
lea rbx, [rcx + 4 * rcx]
mov r9, 0x2c 
bzhi rdx, rax, r9
lea rdx, [ rdx + rbx ]
mov rax, 0x2b 
bzhi rbp, r8, rax
mov r8, rdx
shr r8, 44
bzhi rcx, rdx, r9
mov [ rdi + 0x0 ], rcx
lea r8, [ r8 + rbp ]
bzhi rbx, r8, rax
bzhi rdx, r10, rax
shr r8, 43
lea r8, [ r8 + rdx ]
mov [ rdi + 0x10 ], r8
mov [ rdi + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1656
; seed 3541510137092742 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 483633 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=456, initial num_batches=31): 71163 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.147142564713326
; number reverted permutation / tried permutation: 72466 / 89964 =80.550%
; number reverted decision / tried decision: 65462 / 90035 =72.707%
; validated in 0.17s
