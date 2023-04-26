SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0x2
imul r10, [ rdx + 0x8 ], 0xa
imul r11, [ rdx + 0x10 ], 0xa
imul rcx, [ rdx + 0x10 ], 0x5
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, r11
mov rdx, [ r8 + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r11, [ rsi + 0x10 ]
mov rdx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rax, [ rsi + 0x8 ]
add r11, rax
adcx r12, rbp
mov rdx, r10
mulx rbp, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mulx r13, rax, [ r8 + 0x0 ]
add r10, r9
adcx rbx, rbp
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rax
adox r13, rbx
mov rdx, [ r8 + 0x0 ]
mulx rax, rbp, [ rsi + 0x8 ]
adcx rcx, rbp
adcx rax, r9
mov rdx, 0xfffffffffff 
mov rbx, r10
and rbx, rdx
mov rdx, [ r8 + 0x8 ]
mulx rbp, r9, [ rsi + 0x0 ]
adox rcx, r9
adox rbp, rax
shrd r10, r13, 44
mov rdx, [ r8 + 0x10 ]
mulx rax, r13, [ rsi + 0x0 ]
add rcx, r10
adc rbp, 0x0
mov rdx, 0x2b 
bzhi r9, rcx, rdx
shrd rcx, rbp, 43
xor r10, r10
adox r11, r13
adox rax, r12
adcx r11, rcx
adc rax, 0x0
mov r12, r11
shrd r12, rax, 43
lea r13, [r12 + 4 * r12]
lea rbx, [ rbx + r13 ]
mov rbp, 0x2c 
bzhi rcx, rbx, rbp
mov [ rdi + 0x0 ], rcx
shr rbx, 44
lea rbx, [ rbx + r9 ]
bzhi r9, rbx, rdx
bzhi r12, r11, rdx
shr rbx, 43
lea rbx, [ rbx + r12 ]
mov [ rdi + 0x8 ], r9
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.1500
; seed 1103088518642748 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2618 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=446, initial num_batches=31): 398 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1520244461420932
; number reverted permutation / tried permutation: 424 / 492 =86.179%
; number reverted decision / tried decision: 395 / 507 =77.909%
; validated in 0.175s
