SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x10 ], 0xa
mov r10, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
imul rdx, [ r10 + 0x10 ], 0x5
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rax
imul rdx, [ r10 + 0x8 ], 0xa
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x10 ]
test al, al
adox rax, r9
adox rbx, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ r10 + 0x0 ]
adcx rax, r9
adcx rbp, rbx
mov rdx, rax
shrd rdx, rbp, 44
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rbp, r9, r8
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, r8, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r8
adox r12, rbp
mov rdx, [ rsi + 0x0 ]
mulx r8, rbp, [ r10 + 0x8 ]
adcx r9, rbp
adcx r8, r12
test al, al
adox r9, rbx
mov rdx, 0x0 
adox r8, rdx
mov rbx, r9
shrd rbx, r8, 43
mov r12, 0x1 
shlx rbp, [ r10 + 0x8 ], r12
mov rdx, [ rsi + 0x8 ]
mulx r12, r8, rbp
add r11, r8
adcx r12, rcx
mov rdx, [ r10 + 0x10 ]
mulx rbp, rcx, [ rsi + 0x0 ]
test al, al
adox r11, rcx
adox rbp, r12
adcx r11, rbx
adc rbp, 0x0
mov rdx, r11
shrd rdx, rbp, 43
mov rbx, 0x2b 
bzhi r8, r11, rbx
lea r12, [rdx + 4 * rdx]
mov rcx, 0xfffffffffff 
and rax, rcx
lea rax, [ rax + r12 ]
mov r11, rax
and r11, rcx
mov [ rdi + 0x0 ], r11
shr rax, 44
bzhi rbp, r9, rbx
lea rax, [ rax + rbp ]
bzhi r9, rax, rbx
shr rax, 43
mov [ rdi + 0x8 ], r9
lea rax, [ rax + r8 ]
mov [ rdi + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1045
; seed 3665445000946055 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 426526 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=539, initial num_batches=31): 74548 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.17477949761562014
; number reverted permutation / tried permutation: 68162 / 89763 =75.936%
; number reverted decision / tried decision: 54728 / 90236 =60.650%
; validated in 0.132s
