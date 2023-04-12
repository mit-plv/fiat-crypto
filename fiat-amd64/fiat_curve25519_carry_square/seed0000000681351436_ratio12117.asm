SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x18 ], 0x13
imul rdx, [ rsi + 0x20 ], 0x26
mov rcx, [ rsi + 0x8 ]
lea r8, [rcx + rcx]
imul rcx, [ rsi + 0x18 ], 0x26
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, r8, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
test al, al
adox r13, r8
adox r12, r14
adcx r13, rax
adcx r10, r12
mov rdx, [ rsi + 0x18 ]
lea rax, [rdx + rdx]
mov rdx, r13
shrd rdx, r10, 51
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, rax
imul rdx, [ rsi + 0x10 ], 0x2
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, r11
mov rdx, r12
mulx r11, r12, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rsi + 0x8 ]
mov rdx, r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x10 ]
add r10, r9
adcx r8, r15
add r10, rbx
adcx rbp, r8
xor rbx, rbx
adox r10, rcx
adox rbp, rbx
mov rcx, r10
shrd rcx, rbp, 51
mulx r9, r15, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, rdx
test al, al
adox r15, r8
adox rbp, r9
mov rdx, 0x33 
bzhi r9, r10, rdx
imul r10, [ rsi + 0x20 ], 0x13
xor r8, r8
adox r15, r12
adox r11, rbp
mov rdx, r10
mulx rbx, r10, [ rsi + 0x20 ]
adcx r15, rcx
adc r11, 0x0
mov r12, r15
shrd r12, r11, 51
add r10, rdi
adcx r14, rbx
xor rdi, rdi
adox r10, [ rsp - 0x40 ]
adox r14, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r8, rdx
adcx r10, r12
adc r14, 0x0
mov rdx, rax
mulx rbp, rax, [ rsi + 0x8 ]
add r8, rax
adcx rbp, rcx
mov rdx, [ rsi + 0x20 ]
lea rbx, [rdx + rdx]
mov rdx, rbx
mulx r11, rbx, [ rsi + 0x0 ]
mov r12, 0x33 
bzhi rcx, r10, r12
shrd r10, r14, 51
xor r14, r14
adox r8, rbx
adox r11, rbp
adcx r8, r10
adc r11, 0x0
bzhi rdi, r8, r12
shrd r8, r11, 51
imul rax, r8, 0x13
bzhi rbp, r13, r12
lea rbp, [ rbp + rax ]
mov r13, rbp
shr r13, 51
bzhi rdx, rbp, r12
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], rdx
lea r13, [ r13 + r9 ]
bzhi r9, r15, r12
bzhi r15, r13, r12
shr r13, 51
lea r13, [ r13 + r9 ]
mov [ rbx + 0x8 ], r15
mov [ rbx + 0x20 ], rdi
mov [ rbx + 0x10 ], r13
mov [ rbx + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2117
; seed 2354350031586728 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1235101 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=242, initial num_batches=31): 116455 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09428783556972264
; number reverted permutation / tried permutation: 72350 / 90146 =80.259%
; number reverted decision / tried decision: 64708 / 89853 =72.015%
; validated in 0.352s
