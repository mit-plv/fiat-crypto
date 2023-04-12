SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
imul rdx, [ rax + 0x8 ], 0x13
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
imul rdx, [ rax + 0x20 ], 0x13
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
test al, al
adox r12, r14
adox r15, r13
mov rdx, [ rax + 0x10 ]
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, rbp
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, [ rsi + 0x8 ]
adcx r12, r13
adcx r14, r15
mulx r13, r15, [ rsi + 0x20 ]
test al, al
adox r15, r9
adox rbx, r13
imul r9, [ rax + 0x18 ], 0x13
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r12
mulx r12, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox r15, r14
adox r12, rbx
adcx r15, r11
adcx r10, r12
mov rdx, r9
mulx rbx, r9, [ rsi + 0x20 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], rbp
lea rdi, [rdx + 8 * rdx]
lea rbp, [rdx + 2 * rdi]
add r15, r11
adcx r12, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, rdi, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r12
mulx r12, r11, rbp
xor rdx, rdx
adox rcx, r11
adox r12, r8
adcx rcx, rdi
adcx r10, r12
mov rdx, [ rsi + 0x18 ]
mulx rdi, r8, r13
test al, al
adox r9, r8
adox rdi, rbx
mov rdx, [ rax + 0x0 ]
mulx r11, rbx, [ rsi + 0x10 ]
adcx r9, rbx
adcx r11, rdi
mov rdx, r13
mulx r12, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx rdi, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, [ rsp - 0x20 ]
adox r10, [ rsp - 0x28 ]
adcx r9, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
test al, al
adox rcx, r8
adox rdi, r10
mov rdx, [ rsi + 0x20 ]
mulx r8, rbx, rbp
mov rdx, 0x7ffffffffffff 
mov rbp, rcx
and rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], rbp
mulx rbp, r10, r14
adox rbx, r10
adox rbp, r8
mov rdx, [ rsi + 0x0 ]
mulx r8, r14, [ rax + 0x10 ]
adcx r9, r14
adcx r8, r11
test al, al
adox rbx, r13
adox r12, rbp
mov rdx, [ rsi + 0x0 ]
mulx r11, r13, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, [ rax + 0x0 ]
adcx rbx, r10
adcx rbp, r12
xor rdx, rdx
adox rbx, r13
adox r11, rbp
shrd rcx, rdi, 51
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x18 ]
mov rdx, rdi
xor r12, r12
adox rdx, [ rsp - 0x40 ]
adox r14, [ rsp - 0x48 ]
adcx rbx, rcx
adc r11, 0x0
mov r13, 0x33 
bzhi r10, rbx, r13
shrd rbx, r11, 51
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, [ rax + 0x20 ]
test al, al
adox r9, rbx
adox r8, r12
mov rdx, r9
shrd rdx, r8, 51
xor r11, r11
adox rbp, rcx
adox rdi, r14
adcx r15, rdx
mov r12, [ rsp - 0x18 ]
adc r12, 0x0
bzhi r14, r15, r13
shrd r15, r12, 51
xor rbx, rbx
adox rbp, r15
adox rdi, rbx
mov r11, rbp
shrd r11, rdi, 51
imul rcx, r11, 0x13
add rcx, [ rsp - 0x10 ]
bzhi r8, rbp, r13
bzhi rdx, rcx, r13
shr rcx, 51
lea rcx, [ rcx + r10 ]
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x0 ], rdx
bzhi r12, rcx, r13
mov [ r10 + 0x8 ], r12
shr rcx, 51
bzhi r15, r9, r13
lea rcx, [ rcx + r15 ]
mov [ r10 + 0x20 ], r8
mov [ r10 + 0x18 ], r14
mov [ r10 + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.2655
; seed 3791983356307370 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7002 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=226, initial num_batches=31): 432 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.061696658097686374
; number reverted permutation / tried permutation: 354 / 498 =71.084%
; number reverted decision / tried decision: 323 / 501 =64.471%
; validated in 0.479s
