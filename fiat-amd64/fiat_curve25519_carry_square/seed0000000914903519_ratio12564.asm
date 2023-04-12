SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
imul r10, [ rsi + 0x8 ], 0x2
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rax
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rax
mov rdx, 0x1 
mov [ rsp - 0x58 ], r15
shlx r15, [ rsi + 0x18 ], rdx
xor rdx, rdx
adox rbp, r13
adox r14, r12
mov rdx, rax
mulx r12, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, rdx
mov rdx, r10
mov [ rsp - 0x48 ], r15
mulx r15, r10, [ rsi + 0x0 ]
adcx rbp, r13
adcx rdi, r14
imul rdx, [ rsi + 0x18 ], 0x13
mov r14, 0x33 
bzhi r13, rbp, r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x18 ]
adox r14, rax
adox r12, r13
add r14, r10
adcx r15, r12
shrd rbp, rdi, 51
xor rax, rax
adox r14, rbp
adox r15, rax
adcx r9, r11
adcx rcx, rbx
mov rdx, r8
mulx r11, r8, [ rsi + 0x0 ]
mov rbx, r14
shrd rbx, r15, 51
xor r10, r10
adox r9, r8
adox r11, rcx
adcx r9, rbx
adc r11, 0x0
imul rax, [ rsi + 0x20 ], 0x13
mov rdi, rdx
mov rdx, [ rsi + 0x20 ]
mulx r12, r13, rax
mov rdx, rdi
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, 0x7ffffffffffff 
mov r15, r9
and r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx rax, rbx, [ rsp - 0x48 ]
adox rcx, rbx
adox rax, r8
adcx r13, rdi
adcx rbp, r12
mov rdx, [ rsp - 0x48 ]
mulx rdi, r12, [ rsi + 0x0 ]
shrd r9, r11, 51
xor rdx, rdx
adox r13, r12
adox rdi, rbp
adcx r13, r9
adc rdi, 0x0
mov r10, 0x7ffffffffffff 
mov r11, r13
and r11, r10
imul r8, [ rsi + 0x20 ], 0x2
mov rdx, r8
mulx rbx, r8, [ rsi + 0x0 ]
add rcx, r8
adcx rbx, rax
shrd r13, rdi, 51
add rcx, r13
adc rbx, 0x0
mov rax, rcx
shrd rax, rbx, 51
imul rbp, rax, 0x13
add rbp, [ rsp - 0x40 ]
mov r12, rbp
and r12, r10
shr rbp, 51
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x0 ], r12
and rcx, r10
and r14, r10
lea rbp, [ rbp + r14 ]
mov rdi, rbp
shr rdi, 51
and rbp, r10
mov [ r9 + 0x8 ], rbp
lea rdi, [ rdi + r15 ]
mov [ r9 + 0x18 ], r11
mov [ r9 + 0x20 ], rcx
mov [ r9 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2564
; seed 1599418290981913 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1114125 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=461, initial num_batches=31): 140026 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1256824862560305
; number reverted permutation / tried permutation: 74555 / 89882 =82.948%
; number reverted decision / tried decision: 66816 / 90117 =74.144%
; validated in 0.436s
