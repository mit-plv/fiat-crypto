SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x8 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, rdx
imul rdx, [ rsi + 0x18 ], 0x13
imul rcx, [ rsi + 0x20 ], 0x26
mov r8, [ rsi + 0x18 ]
lea r9, [r8 + r8]
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rcx
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rsi + 0x10 ]
add rdi, rbx
adcx rbp, r10
xor rbx, rbx
adox rax, r12
adox r13, r11
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, rdx
adcx rdi, r11
adcx r12, rbp
mov rdx, r8
mulx r10, r8, [ rsi + 0x18 ]
add r8, r14
adcx r15, r10
mov rdx, [ rsp - 0x48 ]
mulx rbp, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r14
adox rbp, r15
mov rbx, [ rsi + 0x10 ]
mov r11, rbx
shl r11, 0x1
mov rbx, rdi
shrd rbx, r12, 51
xor r12, r12
adox r8, rbx
adox rbp, r12
mov rdx, r8
shrd rdx, rbp, 51
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, r15, rcx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rcx, rdx
xor rdx, rdx
adox r15, rcx
adox rbx, r14
mov rdx, r11
mulx r12, r11, [ rsi + 0x8 ]
mulx r14, rbp, [ rsi + 0x0 ]
adcx r15, rbp
adcx r14, rbx
xor rdx, rdx
adox r15, r10
adox r14, rdx
imul r10, [ rsi + 0x20 ], 0x13
mov rcx, r15
shrd rcx, r14, 51
mov rdx, [ rsi + 0x0 ]
mulx rbp, rbx, r9
mov rdx, r10
mulx r9, r10, [ rsi + 0x20 ]
add r10, r11
adcx r12, r9
mov r11, [ rsi + 0x20 ]
mov r14, r11
shl r14, 0x1
mov rdx, r14
mulx r14, r11, [ rsi + 0x0 ]
xor r9, r9
adox r10, rbx
adox rbp, r12
adcx r10, rcx
adc rbp, 0x0
mov rcx, r10
shrd rcx, rbp, 51
mov rbx, 0x33 
bzhi r12, r15, rbx
bzhi r15, r10, rbx
adox rax, r11
adox r14, r13
xor r13, r13
adox rax, rcx
adox r14, r13
mov r9, rax
shrd r9, r14, 51
bzhi rdx, rax, rbx
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x20 ], rdx
imul r10, r9, 0x13
bzhi rbp, rdi, rbx
lea rbp, [ rbp + r10 ]
bzhi rdi, rbp, rbx
shr rbp, 51
mov [ r11 + 0x0 ], rdi
bzhi rcx, r8, rbx
lea rbp, [ rbp + rcx ]
mov r8, rbp
shr r8, 51
bzhi rax, rbp, rbx
mov [ r11 + 0x8 ], rax
lea r8, [ r8 + r12 ]
mov [ r11 + 0x10 ], r8
mov [ r11 + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.2093
; seed 0403803291326190 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 811864 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=257, initial num_batches=31): 76237 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09390365874087285
; number reverted permutation / tried permutation: 71884 / 90043 =79.833%
; number reverted decision / tried decision: 64258 / 89956 =71.433%
; validated in 0.32s
