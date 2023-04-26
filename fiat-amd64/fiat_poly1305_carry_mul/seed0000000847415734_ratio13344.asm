SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x10 ], 0xa
imul r10, [ rdx + 0x10 ], 0x5
mov r11, rdx
mov rdx, [ rdx + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x8 ]
imul rdx, [ r11 + 0x8 ], 0xa
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, rax
adox r9, rbp
adcx rbx, rcx
adcx r8, r9
mov rcx, rbx
shrd rcx, r8, 44
mov rdx, [ rsi + 0x10 ]
mulx rbp, rax, r10
mov rdx, [ r11 + 0x0 ]
mulx r9, r10, [ rsi + 0x8 ]
test al, al
adox rax, r10
adox r9, rbp
mov rdx, [ r11 + 0x8 ]
mulx rbp, r8, [ rsi + 0x0 ]
adcx rax, r8
adcx rbp, r9
mov rdx, [ r11 + 0x8 ]
lea r10, [rdx + rdx]
xor rdx, rdx
adox rax, rcx
adox rbp, rdx
mov rcx, rax
shrd rcx, rbp, 43
mov rdx, [ rsi + 0x8 ]
mulx r8, r9, r10
mov rdx, [ rsi + 0x10 ]
mulx rbp, r10, [ r11 + 0x0 ]
xor rdx, rdx
adox r10, r9
adox r8, rbp
mov rdx, [ r11 + 0x10 ]
mulx rbp, r9, [ rsi + 0x0 ]
adcx r10, r9
adcx rbp, r8
add r10, rcx
adc rbp, 0x0
mov rdx, 0x2b 
bzhi rcx, r10, rdx
shrd r10, rbp, 43
imul r8, r10, 0x5
mov r9, 0xfffffffffff 
and rbx, r9
lea rbx, [ rbx + r8 ]
mov rbp, rbx
shr rbp, 44
bzhi r10, rax, rdx
lea rbp, [ rbp + r10 ]
and rbx, r9
mov [ rdi + 0x0 ], rbx
bzhi rax, rbp, rdx
mov [ rdi + 0x8 ], rax
shr rbp, 43
lea rbp, [ rbp + rcx ]
mov [ rdi + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.3344
; seed 3660083443917512 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 403256 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=523, initial num_batches=31): 62359 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.15463874065110003
; number reverted permutation / tried permutation: 72832 / 90061 =80.870%
; number reverted decision / tried decision: 65020 / 89938 =72.294%
; validated in 0.153s
