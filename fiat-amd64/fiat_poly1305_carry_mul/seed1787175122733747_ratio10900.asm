SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
imul rax, [ rdx + 0x8 ], 0xa
mov r10, [ rdx + 0x8 ]
mov r11, r10
shl r11, 0x1
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, r11
mov rdx, [ r10 + 0x10 ]
lea r9, [rdx + 4 * rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r11, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rax, [ r10 + 0x0 ]
xor rdx, rdx
adox r11, rax
adox r12, rbx
mov rbx, [ r10 + 0x10 ]
lea rax, [rbx + rbx]
lea rax, [rax + 4 * rax]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbx, rax
mov rdx, [ r10 + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rax, [ rsi + 0x0 ]
adcx r11, rax
adcx r14, r12
xor rdx, rdx
adox r9, rbx
adox r13, rbp
mov rdx, [ r10 + 0x0 ]
mulx r12, rbp, [ rsi + 0x0 ]
adcx r9, rbp
adcx r12, r13
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, [ r10 + 0x0 ]
mov rdx, r9
shrd rdx, r12, 44
xor r13, r13
adox r11, rdx
adox r14, r13
mov rdx, [ rsi + 0x0 ]
mulx r12, rbp, [ r10 + 0x10 ]
adcx rbx, rcx
adcx r8, rax
test al, al
adox rbx, rbp
adox r12, r8
mov rdx, 0x2c 
bzhi rcx, r9, rdx
mov r9, r11
shrd r9, r14, 43
add rbx, r9
adc r12, 0x0
mov rax, 0x2b 
bzhi rbp, r11, rax
mov r11, rbx
shrd r11, r12, 43
lea r14, [r11 + 4 * r11]
bzhi r8, rbx, rax
lea rcx, [ rcx + r14 ]
bzhi r9, rcx, rdx
shr rcx, 44
mov [ rdi + 0x0 ], r9
lea rcx, [ rcx + rbp ]
mov rbx, rcx
shr rbx, 43
lea rbx, [ rbx + r8 ]
mov [ rdi + 0x10 ], rbx
bzhi r12, rcx, rax
mov [ rdi + 0x8 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0900
; seed 1787175122733747 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1852 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=483, initial num_batches=31): 324 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.17494600431965443
; number reverted permutation / tried permutation: 406 / 485 =83.711%
; number reverted decision / tried decision: 370 / 514 =71.984%
; validated in 0.107s
