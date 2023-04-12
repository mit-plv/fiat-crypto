SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
imul rax, [ rdx + 0x18 ], 0x13
mov r10, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ r10 + 0x8 ]
imul rdx, [ r10 + 0x20 ], 0x13
imul r8, [ r10 + 0x8 ], 0x13
imul r9, [ r10 + 0x10 ], 0x13
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rax
mov rdx, r9
mov [ rsp - 0x68 ], r13
mulx r13, r9, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ r10 + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r15
mulx r15, rdi, r8
xor rdx, rdx
adox rdi, r9
adox r13, r15
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rax
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rcx
mulx rcx, r15, r14
adcx r15, r8
adcx r9, rcx
mov rdx, [ rsi + 0x10 ]
mulx r8, r14, rbx
xor rdx, rdx
adox r15, r14
adox r8, r9
mov rdx, rbx
mulx rcx, rbx, [ rsi + 0x8 ]
adcx rdi, rbp
adcx r12, r13
test al, al
adox rdi, rbx
adox rcx, r12
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, [ r10 + 0x0 ]
adcx rdi, r13
adcx r9, rcx
mov rdx, rdi
shrd rdx, r9, 51
mov r14, rdx
mov rdx, [ r10 + 0x0 ]
mulx r12, rbx, [ rsi + 0x8 ]
mov rdx, [ r10 + 0x8 ]
mulx r13, rcx, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, rbx
adox r12, r8
adcx r15, rcx
adcx r13, r12
test al, al
adox r15, r14
adox r13, rdx
mov rdx, rax
mulx r8, rax, [ rsi + 0x20 ]
mov rdx, rbp
mulx r9, rbp, [ rsi + 0x18 ]
adcx rax, rbp
adcx r9, r8
mulx rbx, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rcx, [ r10 + 0x0 ]
mov rdx, r15
shrd rdx, r13, 51
mov r13, rdx
mov rdx, [ r10 + 0x0 ]
mulx rbp, r8, [ rsi + 0x18 ]
mov rdx, 0x7ffffffffffff 
and r15, rdx
adox r14, r8
adox rbp, rbx
mov rdx, [ r10 + 0x8 ]
mulx r8, rbx, [ rsi + 0x10 ]
adcx r14, rbx
adcx r8, rbp
add rax, rcx
adcx r12, r9
add rax, r11
adcx r12, [ rsp - 0x38 ]
add rax, [ rsp - 0x40 ]
adcx r12, [ rsp - 0x48 ]
xor rdx, rdx
adox rax, r13
adox r12, rdx
mov rdx, [ r10 + 0x10 ]
mulx r9, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r13, rcx, [ r10 + 0x18 ]
mov rdx, rax
shrd rdx, r12, 51
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r12, rbx, [ r10 + 0x18 ]
xor rdx, rdx
adox r14, r11
adox r9, r8
adcx r14, rcx
adcx r13, r9
mov rdx, [ r10 + 0x8 ]
mulx r11, r8, [ rsi + 0x18 ]
mov rdx, [ r10 + 0x0 ]
mulx r9, rcx, [ rsi + 0x20 ]
add rcx, r8
adcx r11, r9
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ r10 + 0x10 ]
add rcx, r8
adcx r9, r11
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ r10 + 0x20 ]
xor rdx, rdx
adox r14, rbp
adox r13, rdx
mov rbp, r14
shrd rbp, r13, 51
add rcx, rbx
adcx r12, r9
xor rbx, rbx
adox rcx, r11
adox r8, r12
adcx rcx, rbp
adc r8, 0x0
mov rdx, rcx
shrd rdx, r8, 51
imul r9, rdx, 0x13
mov r11, 0x33 
bzhi r13, rcx, r11
bzhi rbp, r14, r11
mov r14, [ rsp - 0x50 ]
mov [ r14 + 0x20 ], r13
mov [ r14 + 0x18 ], rbp
bzhi r12, rdi, r11
lea r12, [ r12 + r9 ]
bzhi rdi, r12, r11
shr r12, 51
lea r12, [ r12 + r15 ]
mov [ r14 + 0x0 ], rdi
bzhi r15, rax, r11
mov rax, r12
shr rax, 51
lea rax, [ rax + r15 ]
bzhi rcx, r12, r11
mov [ r14 + 0x10 ], rax
mov [ r14 + 0x8 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.3381
; seed 3817666679117635 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1010308 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=227, initial num_batches=31): 76804 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07602038190334037
; number reverted permutation / tried permutation: 70455 / 90017 =78.269%
; number reverted decision / tried decision: 57721 / 89982 =64.147%
; validated in 0.47s
