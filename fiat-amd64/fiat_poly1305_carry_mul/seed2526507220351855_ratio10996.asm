SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x10 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x8 ]
lea r8, [rdx + rdx]
mov rdx, rax
mulx r9, rax, [ rsi + 0x8 ]
imul rdx, [ r10 + 0x8 ], 0xa
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
imul rdx, [ r10 + 0x10 ], 0x5
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r12, r11
adox rcx, r13
mov rdx, [ r10 + 0x8 ]
mulx r13, r11, [ rsi + 0x0 ]
adcx r12, r11
adcx r13, rcx
mov rdx, [ r10 + 0x0 ]
mulx r11, rcx, [ rsi + 0x0 ]
test al, al
adox rbx, rax
adox r9, rbp
mov rdx, [ r10 + 0x0 ]
mulx rbp, rax, [ rsi + 0x10 ]
adcx rbx, rcx
adcx r11, r9
mov rdx, rbx
shrd rdx, r11, 44
mov rcx, 0xfffffffffff 
and rbx, rcx
xchg rdx, r8
mulx r11, r9, [ rsi + 0x8 ]
adox rax, r9
adox r11, rbp
adcx r12, r8
adc r13, 0x0
mov rdx, r12
shrd rdx, r13, 43
mov rbp, rdx
mov rdx, [ r10 + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r8
adox r9, r11
adcx rax, rbp
adc r9, 0x0
mov r11, rax
shrd r11, r9, 43
lea r13, [r11 + 4 * r11]
lea rbx, [ rbx + r13 ]
mov rbp, rbx
and rbp, rcx
mov r8, 0x2b 
bzhi r9, r12, r8
shr rbx, 44
lea rbx, [ rbx + r9 ]
bzhi r12, rax, r8
mov rax, rbx
shr rax, 43
bzhi r11, rbx, r8
mov [ rdi + 0x8 ], r11
lea rax, [ rax + r12 ]
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.0996
; seed 2526507220351855 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2367 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=541, initial num_batches=31): 440 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.18588931136459655
; number reverted permutation / tried permutation: 367 / 503 =72.962%
; number reverted decision / tried decision: 291 / 496 =58.669%
; validated in 0.133s
