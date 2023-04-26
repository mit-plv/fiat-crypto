SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
lea rcx, [rdx + 4 * rdx]
mov rdx, [ rax + 0x10 ]
lea r8, [rdx + rdx]
lea r8, [r8 + 4 * r8]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov rdx, [ rax + 0x8 ]
lea rcx, [rdx + rdx]
lea rcx, [rcx + 4 * rcx]
mov rdx, r8
mov [ rsp - 0x78 ], rbp
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rcx
test al, al
adox r12, r8
adox rbp, r13
mov rdx, [ rax + 0x8 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mulx r13, r8, rcx
adcx r12, r10
adcx r11, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, r10, [ rax + 0x0 ]
add r10, r8
adcx r13, rbp
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x8 ]
test al, al
adox r9, rcx
adox r8, rbx
mov rdx, [ rax + 0x8 ]
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, r11, 44
add r9, rbx
adcx rbp, r8
mov r11, rdx
mov rdx, [ rax + 0x10 ]
mulx r8, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r11
adox rbp, rdx
mov rbx, 0x2c 
bzhi r11, r12, rbx
mov r12, r9
shrd r12, rbp, 43
test al, al
adox r10, rcx
adox r8, r13
adcx r10, r12
adc r8, 0x0
mov r13, r10
shrd r13, r8, 43
imul rcx, r13, 0x5
lea r11, [ r11 + rcx ]
mov rbp, r11
shr rbp, 44
bzhi r12, r11, rbx
mov r8, 0x2b 
bzhi r13, r9, r8
lea rbp, [ rbp + r13 ]
bzhi r9, rbp, r8
shr rbp, 43
mov [ rdi + 0x8 ], r9
bzhi rcx, r10, r8
lea rbp, [ rbp + rcx ]
mov [ rdi + 0x10 ], rbp
mov [ rdi + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.0954
; seed 1448383790120967 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3679 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=298, initial num_batches=31): 462 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.12557760260940473
; number reverted permutation / tried permutation: 419 / 492 =85.163%
; number reverted decision / tried decision: 309 / 507 =60.947%
; validated in 0.174s
