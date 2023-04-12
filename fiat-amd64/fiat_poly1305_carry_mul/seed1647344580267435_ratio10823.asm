SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 4 * rax]
xchg rdx, r10
mulx r11, rax, [ rsi + 0x10 ]
mov rcx, [ r10 + 0x8 ]
lea r8, [rcx + rcx]
mov rdx, [ r10 + 0x10 ]
mulx r9, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ r10 + 0x0 ]
mov rdx, r8
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x8 ]
test al, al
adox rbx, r8
adox r12, rbp
adcx rbx, rcx
adcx r9, r12
mov rdx, [ rsi + 0x8 ]
mulx rbp, rcx, [ r10 + 0x0 ]
xor rdx, rdx
adox rax, rcx
adox rbp, r11
imul r11, [ r10 + 0x8 ], 0xa
mov r8, [ r10 + 0x10 ]
lea r12, [r8 + r8]
lea r12, [r12 + 4 * r12]
mov rdx, r12
mulx r12, r8, [ rsi + 0x8 ]
mov rdx, r11
mulx rcx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r8
adox r12, rcx
mov rdx, [ r10 + 0x0 ]
mulx rcx, r8, [ rsi + 0x0 ]
adcx r11, r8
adcx rcx, r12
mov rdx, r11
shrd rdx, rcx, 44
mov r12, rdx
mov rdx, [ r10 + 0x8 ]
mulx rcx, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, r8
adox rcx, rbp
adcx rax, r12
adc rcx, 0x0
mov rbp, 0x7ffffffffff 
mov r12, rax
and r12, rbp
shrd rax, rcx, 43
xor r8, r8
adox rbx, rax
adox r9, r8
mov rdx, rbx
shrd rdx, r9, 43
and rbx, rbp
mov rcx, 0x2c 
bzhi rax, r11, rcx
lea r11, [rdx + 4 * rdx]
lea rax, [ rax + r11 ]
bzhi r9, rax, rcx
shr rax, 44
lea rax, [ rax + r12 ]
mov [ rdi + 0x0 ], r9
mov r12, rax
shr r12, 43
lea r12, [ r12 + rbx ]
mov [ rdi + 0x10 ], r12
and rax, rbp
mov [ rdi + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.0823
; seed 1647344580267435 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2620 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=496, initial num_batches=31): 366 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.13969465648854962
; number reverted permutation / tried permutation: 380 / 495 =76.768%
; number reverted decision / tried decision: 307 / 504 =60.913%
; validated in 0.131s
