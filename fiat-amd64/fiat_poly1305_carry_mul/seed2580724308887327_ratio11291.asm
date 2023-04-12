SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x10 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x0 ]
imul rdx, [ r10 + 0x8 ], 0xa
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
xor rdx, rdx
adox r8, rbx
adox rbp, r9
mov rax, [ r10 + 0x10 ]
lea r9, [rax + 4 * rax]
adcx r8, r11
adcx rcx, rbp
mov rdx, [ rsi + 0x8 ]
mulx r11, rax, [ r10 + 0x0 ]
mov rdx, r9
mulx rbx, r9, [ rsi + 0x10 ]
mov rbp, r8
shrd rbp, rcx, 44
add r9, rax
adcx r11, rbx
mov rdx, [ r10 + 0x8 ]
mulx rax, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ r10 + 0x0 ]
imul rdx, [ r10 + 0x8 ], 0x2
add r9, rcx
adcx rax, r11
xor r11, r11
adox r9, rbp
adox rax, r11
mulx rcx, rbp, [ rsi + 0x8 ]
adcx rbx, rbp
adcx rcx, r12
mov rdx, [ r10 + 0x10 ]
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, r9
shrd rdx, rax, 43
xor rax, rax
adox rbx, r12
adox rbp, rcx
adcx rbx, rdx
adc rbp, 0x0
mov r11, 0x2b 
bzhi rcx, r9, r11
bzhi r9, rbx, r11
mov r12, 0x2c 
bzhi rdx, r8, r12
shrd rbx, rbp, 43
lea r8, [rbx + 4 * rbx]
lea rdx, [ rdx + r8 ]
bzhi rbp, rdx, r12
mov [ rdi + 0x0 ], rbp
shr rdx, 44
lea rdx, [ rdx + rcx ]
bzhi rcx, rdx, r11
mov [ rdi + 0x8 ], rcx
shr rdx, 43
lea rdx, [ rdx + r9 ]
mov [ rdi + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.1291
; seed 2580724308887327 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2339 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=621, initial num_batches=31): 387 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.16545532278751604
; number reverted permutation / tried permutation: 404 / 491 =82.281%
; number reverted decision / tried decision: 366 / 508 =72.047%
; validated in 0.153s
