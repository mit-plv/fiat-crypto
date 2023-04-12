SECTION .text
	GLOBAL fiat_poly1305_carry_mul
fiat_poly1305_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + rax]
lea r10, [r10 + 4 * r10]
mov rax, [ rdx + 0x8 ]
lea r11, [rax + rax]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
lea r9, [rdx + rdx]
lea r9, [r9 + 4 * r9]
mov rdx, r10
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r9
test al, al
adox rbp, r10
adox rbx, r12
mov rdx, [ rax + 0x10 ]
lea r9, [rdx + 4 * rdx]
mov rdx, r9
mulx r10, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x0 ]
adcx rbp, rcx
adcx r8, rbx
xor rdx, rdx
adox r9, r12
adox r13, r10
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, [ rax + 0x8 ]
mov rdx, rbp
shrd rdx, r8, 44
add r9, rcx
adcx rbx, r13
xchg rdx, r11
mulx r12, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r13, r8, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r9, r11
adox rbx, rdx
mov r11, r9
shrd r11, rbx, 43
mov rbx, 0x7ffffffffff 
and r9, rbx
adox r8, r10
adox r12, r13
adcx r8, rcx
adcx r14, r12
add r8, r11
adc r14, 0x0
mov r10, r8
shrd r10, r14, 43
lea r13, [r10 + 4 * r10]
mov rcx, 0xfffffffffff 
and rbp, rcx
lea rbp, [ rbp + r13 ]
mov r11, rbp
and r11, rcx
and r8, rbx
shr rbp, 44
lea rbp, [ rbp + r9 ]
mov r9, rbp
shr r9, 43
and rbp, rbx
lea r9, [ r9 + r8 ]
mov [ rdi + 0x10 ], r9
mov [ rdi + 0x8 ], rbp
mov [ rdi + 0x0 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1330
; seed 1050076044628575 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3660 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=298, initial num_batches=31): 484 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.13224043715846995
; number reverted permutation / tried permutation: 409 / 510 =80.196%
; number reverted decision / tried decision: 274 / 489 =56.033%
; validated in 0.177s
