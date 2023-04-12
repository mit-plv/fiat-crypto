SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
mov r10, [ rsi + 0x20 ]
lea r11, [r10 + 8 * r10]
lea rdx, [r10 + 2 * r11]
mov r10, [ rsi + 0x18 ]
lea r11, [r10 + 8 * r10]
lea rcx, [r10 + 2 * r11]
mov r10, 0x1 
shlx r11, [ rsi + 0x8 ], r10
imul r8, [ rsi + 0x18 ], 0x26
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, rcx
mov rdx, rax
mulx rcx, rax, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
xchg rdx, r8
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
test al, al
adox r13, rbp
adox r12, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, rbp, rdx
adcx r13, rbp
adcx r14, r12
mov rdx, [ rsi + 0x8 ]
mulx rbp, r12, rdx
test al, al
adox r10, rax
adox rcx, rbx
mov rdx, r11
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, r8
mulx rax, r8, [ rsi + 0x18 ]
adcx r10, r11
adcx rbx, rcx
xor rdx, rdx
adox r8, r12
adox rbp, rax
mov r12, [ rsi + 0x10 ]
mov rcx, r12
shl rcx, 0x1
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, rcx
test al, al
adox r8, r12
adox r11, rbp
mov rdx, 0x1 
shlx rax, [ rsi + 0x18 ], rdx
mov rbp, r13
shrd rbp, r14, 51
test al, al
adox r10, rbp
mov r14, 0x0 
adox rbx, r14
mov rdx, r9
mulx r12, r9, [ rsi + 0x20 ]
mov rdx, r10
shrd rdx, rbx, 51
mov rbp, 0x7ffffffffffff 
and r10, rbp
adox r8, rdx
adox r11, r14
mov rbx, r8
shrd rbx, r11, 51
mov rdx, rcx
mulx r11, rcx, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, rcx
adox r11, r12
mov rdx, rax
mulx r14, rax, [ rsi + 0x0 ]
adcx r9, rax
adcx r14, r11
imul r12, [ rsi + 0x20 ], 0x2
and r8, rbp
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, rdx
adox r9, rbx
mov rdx, 0x0 
adox r14, rdx
mov rbx, r9
and rbx, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mulx rbp, r15, r12
shrd r9, r14, 51
mov [ rdi + 0x18 ], rbx
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, rcx
xor rdx, rdx
adox r11, r12
adox r14, rax
adcx r11, r15
adcx rbp, r14
test al, al
adox r11, r9
adox rbp, rdx
mov rcx, 0x33 
bzhi rax, r11, rcx
bzhi rbx, r13, rcx
shrd r11, rbp, 51
lea r13, [r11 + 8 * r11]
lea r15, [r11 + 2 * r13]
lea rbx, [ rbx + r15 ]
mov [ rdi + 0x20 ], rax
bzhi r13, rbx, rcx
shr rbx, 51
lea rbx, [ rbx + r10 ]
mov r10, rbx
shr r10, 51
lea r10, [ r10 + r8 ]
mov [ rdi + 0x0 ], r13
bzhi r8, rbx, rcx
mov [ rdi + 0x8 ], r8
mov [ rdi + 0x10 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.2941
; seed 2210124772508141 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 680968 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=251, initial num_batches=31): 70192 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10307679656019078
; number reverted permutation / tried permutation: 73338 / 89807 =81.662%
; number reverted decision / tried decision: 58781 / 90192 =65.173%
; validated in 0.253s
