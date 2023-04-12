SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
lea rcx, [rdx + 4 * rdx]
mov rdx, [ rax + 0x8 ]
lea r8, [rdx + rdx]
imul rdx, [ rax + 0x10 ], 0xa
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
imul rdx, [ rax + 0x8 ], 0xa
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, r9
adox rbx, r12
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
adcx rcx, r10
adcx r11, r9
add rcx, r12
adcx r13, r11
mov rdx, [ rax + 0x0 ]
mulx r9, r10, [ rsi + 0x0 ]
test al, al
adox rbp, r10
adox r9, rbx
mov rdx, r8
mulx rbx, r8, [ rsi + 0x8 ]
mov rdx, rbp
shrd rdx, r9, 44
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mulx r10, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, r12
adox r13, rdx
mov r9, 0x7ffffffffff 
mov r12, rcx
and r12, r9
shrd rcx, r13, 43
add r11, r8
adcx rbx, r10
mov rdx, [ rax + 0x10 ]
mulx r10, r8, [ rsi + 0x0 ]
add r11, r8
adcx r10, rbx
add r11, rcx
adc r10, 0x0
mov rdx, r11
and rdx, r9
shrd r11, r10, 43
imul r13, r11, 0x5
mov rcx, 0x2c 
bzhi rbx, rbp, rcx
lea rbx, [ rbx + r13 ]
bzhi rbp, rbx, rcx
shr rbx, 44
lea rbx, [ rbx + r12 ]
mov r12, rbx
and r12, r9
mov [ rdi + 0x8 ], r12
shr rbx, 43
lea rbx, [ rbx + rdx ]
mov [ rdi + 0x0 ], rbp
mov [ rdi + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1710
; seed 4444783196056723 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1880 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=476, initial num_batches=31): 308 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.16382978723404254
; number reverted permutation / tried permutation: 427 / 508 =84.055%
; number reverted decision / tried decision: 355 / 491 =72.301%
; validated in 0.104s
