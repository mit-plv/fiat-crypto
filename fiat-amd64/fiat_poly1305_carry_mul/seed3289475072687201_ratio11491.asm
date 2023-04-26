SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
imul r10, [ rdx + 0x10 ], 0xa
imul r11, [ rdx + 0x8 ], 0x2
imul rcx, [ rdx + 0x10 ], 0x5
mov r8, rdx
mov rdx, [ rdx + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r11
add r9, rbp
adcx r12, rbx
mov rdx, [ rsi + 0x0 ]
mulx rbx, r11, [ r8 + 0x10 ]
add r9, r11
adcx rbx, r12
mov rdx, rax
mulx rbp, rax, [ rsi + 0x10 ]
mov rdx, r10
mulx r12, r10, [ rsi + 0x8 ]
add rax, r10
adcx r12, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r11, [ r8 + 0x0 ]
xor rdx, rdx
adox rax, r11
adox rbp, r12
mov r10, rax
shrd r10, rbp, 44
mov rdx, [ rsi + 0x8 ]
mulx r11, r12, [ r8 + 0x0 ]
mov rdx, rcx
mulx rbp, rcx, [ rsi + 0x10 ]
add rcx, r12
adcx r11, rbp
mov rdx, [ r8 + 0x8 ]
mulx rbp, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, r12
adox rbp, r11
adcx rcx, r10
adc rbp, 0x0
mov r10, rcx
shrd r10, rbp, 43
mov r11, 0x2b 
bzhi r12, rcx, r11
adox r9, r10
adox rbx, rdx
mov rcx, r9
shrd rcx, rbx, 43
bzhi rbp, r9, r11
mov r10, 0x2c 
bzhi r9, rax, r10
lea rax, [rcx + 4 * rcx]
lea r9, [ r9 + rax ]
bzhi rbx, r9, r10
shr r9, 44
lea r9, [ r9 + r12 ]
mov r12, r9
shr r12, 43
lea r12, [ r12 + rbp ]
bzhi rcx, r9, r11
mov [ rdi + 0x0 ], rbx
mov [ rdi + 0x10 ], r12
mov [ rdi + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1491
; seed 3289475072687201 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2751 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=446, initial num_batches=31): 398 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.14467466375863322
; number reverted permutation / tried permutation: 404 / 495 =81.616%
; number reverted decision / tried decision: 368 / 504 =73.016%
; validated in 0.17s
