SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
imul r11, [ rsi + 0x20 ], 0x26
imul rdx, [ rsi + 0x18 ], 0x26
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
shl r12, 0x1
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rcx
mov rdx, [ rsi + 0x18 ]
lea rcx, [rdx + rdx]
mov rdx, rcx
mov [ rsp - 0x58 ], r15
mulx r15, rcx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x0 ]
imul rdx, [ rsi + 0x18 ], 0x13
mov [ rsp - 0x40 ], r12
xor r12, r12
adox r13, r8
adox r9, r14
mulx r14, r8, [ rsi + 0x18 ]
adcx r13, rbx
adcx rbp, r9
xor rbx, rbx
adox rax, rcx
adox r15, r10
mov r12, r13
shrd r12, rbp, 51
imul r10, [ rsi + 0x20 ], 0x13
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, r11
mov rdx, [ rsi + 0x8 ]
mov rbp, rdx
shl rbp, 0x1
mov rdx, rbp
mulx rbx, rbp, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, rcx
adox r9, r14
adcx r8, rbp
adcx rbx, r9
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, rdx
xor rdx, rdx
adox r8, r12
adox rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r12, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mulx r15, r9, r11
adcx r9, r14
adcx rcx, r15
xor rdx, rdx
adox r9, r12
adox rbp, rcx
mov rdx, [ rsi + 0x20 ]
mulx r14, r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r12, r10, [ rsp - 0x48 ]
adcx r11, r10
adcx r12, r14
imul rdx, [ rsi + 0x20 ], 0x2
mov r15, 0x33 
bzhi rcx, r13, r15
bzhi r13, r8, r15
shrd r8, rbx, 51
xor rbx, rbx
adox r9, r8
adox rbp, rbx
bzhi r14, r9, r15
adox r11, rdi
adox r12, [ rsp - 0x40 ]
shrd r9, rbp, 51
xor rdi, rdi
adox r11, r9
adox r12, rdi
mulx r10, rbx, [ rsi + 0x0 ]
bzhi rdx, r11, r15
adox rax, rbx
adox r10, [ rsp - 0x38 ]
shrd r11, r12, 51
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x18 ], rdx
xor rbp, rbp
adox rax, r11
adox r10, rbp
bzhi rdi, rax, r15
mov [ r8 + 0x20 ], rdi
shrd rax, r10, 51
imul r9, rax, 0x13
lea rcx, [ rcx + r9 ]
bzhi r12, rcx, r15
mov [ r8 + 0x0 ], r12
shr rcx, 51
lea rcx, [ rcx + r13 ]
bzhi r13, rcx, r15
shr rcx, 51
lea rcx, [ rcx + r14 ]
mov [ r8 + 0x8 ], r13
mov [ r8 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.2196
; seed 1795189027736273 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4040 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=343, initial num_batches=31): 406 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1004950495049505
; number reverted permutation / tried permutation: 412 / 515 =80.000%
; number reverted decision / tried decision: 340 / 484 =70.248%
; validated in 0.298s
