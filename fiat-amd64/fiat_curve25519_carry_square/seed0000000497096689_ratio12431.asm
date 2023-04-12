SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
mov r10, [ rsi + 0x20 ]
lea r11, [r10 + r10]
mov rdx, rax
mulx r10, rax, [ rsi + 0x18 ]
imul rcx, [ rsi + 0x18 ], 0x26
mov r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
xor rdx, rdx
adox r13, rbp
adox r12, r14
adcx rax, r9
adcx rbx, r10
mov rdx, [ rsi + 0x0 ]
mulx rcx, r10, rdx
xor rdx, rdx
adox r13, r10
adox rcx, r12
mov r9, r13
shrd r9, rcx, 51
imul rbp, [ rsi + 0x18 ], 0x13
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, r8
mov rdx, rbp
mulx r8, rbp, [ rsi + 0x18 ]
add rbp, r14
adcx r12, r8
imul r10, [ rsi + 0x8 ], 0x2
mov rdx, r10
mulx rcx, r10, [ rsi + 0x0 ]
add rbp, r10
adcx rcx, r12
imul r14, [ rsi + 0x10 ], 0x2
mov r8, 0x1 
shlx r12, [ rsi + 0x18 ], r8
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, r12
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
xor rdi, rdi
adox rbp, r9
adox rcx, rdi
mulx rdi, r9, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], rdi
mulx rdi, r11, rdx
adcx r11, r10
adcx r8, rdi
imul rdx, [ rsi + 0x20 ], 0x13
mulx rdi, r10, [ rsi + 0x20 ]
mov rdx, rbp
shrd rdx, rcx, 51
xor rcx, rcx
adox rax, r14
adox r15, rbx
adcx rax, rdx
adc r15, 0x0
mov rbx, 0x33 
bzhi r14, rbp, rbx
adox r10, r9
adox rdi, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, rbp, r12
mov rdx, rax
shrd rdx, r15, 51
xor r12, r12
adox r10, rbp
adox r9, rdi
adcx r10, rdx
adc r9, 0x0
bzhi rcx, r10, rbx
mov rdx, [ rsp - 0x48 ]
mulx rdi, r15, [ rsi + 0x0 ]
shrd r10, r9, 51
add r11, r15
adcx rdi, r8
xor rdx, rdx
adox r11, r10
adox rdi, rdx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x18 ], rcx
bzhi r8, r11, rbx
shrd r11, rdi, 51
mov [ r12 + 0x20 ], r8
bzhi rbp, r13, rbx
imul r13, r11, 0x13
lea rbp, [ rbp + r13 ]
mov r9, rbp
shr r9, 51
lea r9, [ r9 + r14 ]
bzhi r14, rax, rbx
bzhi rax, r9, rbx
shr r9, 51
mov [ r12 + 0x8 ], rax
lea r9, [ r9 + r14 ]
mov [ r12 + 0x10 ], r9
bzhi rcx, rbp, rbx
mov [ r12 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.2431
; seed 3486063572194730 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 684685 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=342, initial num_batches=31): 70731 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10330443926769245
; number reverted permutation / tried permutation: 73577 / 90106 =81.656%
; number reverted decision / tried decision: 66848 / 89893 =74.364%
; validated in 0.292s
