SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 4 * rax]
imul rax, [ rdx + 0x8 ], 0xa
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ r11 + 0x0 ]
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
mov rdx, [ r11 + 0x10 ]
mov [ rsp - 0x80 ], rbx
lea rbx, [rdx + rdx]
lea rbx, [rbx + 4 * rbx]
mov rdx, rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, r10
mov [ rsp - 0x70 ], r12
mulx r12, r10, [ rsi + 0x10 ]
xor rdx, rdx
adox rax, rbx
adox rbp, r9
adcx r10, rcx
adcx r8, r12
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ r11 + 0x0 ]
test al, al
adox rax, rcx
adox r9, rbp
imul rdx, [ r11 + 0x8 ], 0x2
mov rbx, rax
shrd rbx, r9, 44
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ r11 + 0x8 ]
mulx r9, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, rcx
adox r9, r8
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, [ r11 + 0x0 ]
adcx r8, r12
adcx rbp, rcx
xor rdx, rdx
adox r10, rbx
adox r9, rdx
mov rbx, r10
shrd rbx, r9, 43
mov rdx, [ r11 + 0x10 ]
mulx rcx, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r12
adox rcx, rbp
mov rbp, 0x2b 
bzhi r12, r10, rbp
adox r8, rbx
adox rcx, rdx
bzhi r10, r8, rbp
shrd r8, rcx, 43
mov r9, 0xfffffffffff 
and rax, r9
imul rbx, r8, 0x5
lea rax, [ rax + rbx ]
mov rcx, rax
shr rcx, 44
lea rcx, [ rcx + r12 ]
mov r12, rcx
shr r12, 43
bzhi r8, rcx, rbp
lea r12, [ r12 + r10 ]
mov [ rdi + 0x10 ], r12
and rax, r9
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x0 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0469
; seed 4051189958004543 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 314113 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=484, initial num_batches=31): 56032 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1783816651969196
; number reverted permutation / tried permutation: 73698 / 90219 =81.688%
; number reverted decision / tried decision: 63935 / 89780 =71.213%
; validated in 0.103s
