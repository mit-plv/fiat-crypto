SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, [ rdx + 0x10 ]
lea r11, [r10 + 4 * r10]
mov r10, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rax
imul rdx, [ r10 + 0x10 ], 0xa
mulx rax, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, r9
adox rax, r8
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ r10 + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ r10 + 0x0 ]
adcx rcx, r8
adcx r9, rax
mov rdx, [ rsi + 0x10 ]
mulx r8, rax, r11
xor rdx, rdx
adox rax, rbx
adox rbp, r8
mov rdx, [ r10 + 0x8 ]
mulx rbx, r11, [ rsi + 0x0 ]
adcx rax, r11
adcx rbx, rbp
imul rdx, [ r10 + 0x8 ], 0x2
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, r11, [ rsi + 0x10 ]
add r11, r8
adcx rbp, r12
mov rdx, rcx
shrd rdx, r9, 44
add rax, rdx
adc rbx, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ r10 + 0x10 ]
add r11, r9
adcx r8, rbp
mov rdx, 0x7ffffffffff 
mov r12, rax
and r12, rdx
shrd rax, rbx, 43
xor rbp, rbp
adox r11, rax
adox r8, rbp
mov rbx, r11
shrd rbx, r8, 43
lea r9, [rbx + 4 * rbx]
mov rax, 0x2c 
bzhi r8, rcx, rax
lea r8, [ r8 + r9 ]
bzhi rcx, r8, rax
mov [ rdi + 0x0 ], rcx
shr r8, 44
lea r8, [ r8 + r12 ]
mov r12, r8
and r12, rdx
mov [ rdi + 0x8 ], r12
and r11, rdx
shr r8, 43
lea r8, [ r8 + r11 ]
mov [ rdi + 0x10 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.1483
; seed 3507969415373503 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4071 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=395, initial num_batches=31): 578 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1419798575288627
; number reverted permutation / tried permutation: 431 / 527 =81.784%
; number reverted decision / tried decision: 368 / 472 =77.966%
; validated in 0.196s
