SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x0 ]
imul rdx, [ rax + 0x20 ], 0x13
mov rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rax + 0x8 ]
imul rdx, [ rax + 0x10 ], 0x13
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
imul rdx, [ rax + 0x18 ], 0x13
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
xchg rdx, rcx
mov [ rsp - 0x48 ], r12
mov [ rsp - 0x40 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r9
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], r11
mulx r11, r8, rcx
xor rdx, rdx
adox r13, r15
adox rdi, r14
adcx r13, r12
adcx rbp, rdi
mov r14, [ rax + 0x8 ]
lea r15, [r14 + 8 * r14]
lea r12, [r14 + 2 * r15]
mov rdx, [ rsi + 0x18 ]
mulx r15, r14, rbx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x20 ]
test al, al
adox r12, r14
adox r15, rbx
adcx r13, r10
adcx rbp, [ rsp - 0x28 ]
xor r10, r10
adox r12, r8
adox r11, r15
mov rdx, [ rsi + 0x8 ]
mulx rdi, r8, r9
adcx r12, r8
adcx rdi, r11
mov rdx, [ rsi + 0x0 ]
mulx rbx, r14, [ rax + 0x0 ]
xor rdx, rdx
adox r12, r14
adox rbx, rdi
mov r10, r12
shrd r10, rbx, 51
mov rdx, rcx
mulx r15, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r11, r9
xor rdx, rdx
adox rcx, r11
adox r8, r15
mov rdx, [ rax + 0x0 ]
mulx r14, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, rbx, [ rax + 0x8 ]
adcx rcx, rdi
adcx r14, r8
xor rdx, rdx
adox rcx, rbx
adox r15, r14
mov rdx, [ rsi + 0x0 ]
mulx r8, r11, [ rax + 0x10 ]
adcx rcx, r11
adcx r8, r15
mov rdx, [ rax + 0x8 ]
mulx rbx, rdi, [ rsi + 0x0 ]
test al, al
adox r13, rdi
adox rbx, rbp
mov rdx, [ rsi + 0x20 ]
mulx r14, rbp, r9
adcx r13, r10
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r10, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r15, [ rax + 0x0 ]
add rbp, r15
adcx r11, r14
xor rdx, rdx
adox rbp, [ rsp - 0x30 ]
adox r11, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, [ rax + 0x10 ]
mov rdx, r13
shrd rdx, rbx, 51
xor rbx, rbx
adox rcx, rdx
adox r8, rbx
mov rdx, [ rsi + 0x20 ]
mulx rbx, r15, [ rax + 0x0 ]
adcx r15, r9
adcx r10, rbx
mov rdx, [ rax + 0x18 ]
mulx rbx, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox rbp, rdi
adox r14, r11
adcx rbp, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
mov r11, rcx
shrd r11, r8, 51
xor rdi, rdi
adox rbp, r11
adox r14, rdi
mov rdx, rbp
shrd rdx, r14, 51
mov r8, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, r11, [ rsi + 0x10 ]
add r15, r11
adcx r14, r10
test al, al
adox r15, r9
adox rbx, r14
mov rdx, [ rax + 0x20 ]
mulx r9, r10, [ rsi + 0x0 ]
adcx r15, r10
adcx r9, rbx
mov rdx, 0x33 
bzhi r11, r12, rdx
adox r15, r8
adox r9, rdi
mov r12, r15
shrd r12, r9, 51
imul r8, r12, 0x13
bzhi r14, r15, rdx
lea r11, [ r11 + r8 ]
bzhi rbx, r11, rdx
bzhi r10, r13, rdx
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rbx
shr r11, 51
lea r11, [ r11 + r10 ]
bzhi r15, rcx, rdx
bzhi rcx, r11, rdx
shr r11, 51
lea r11, [ r11 + r15 ]
bzhi r9, rbp, rdx
mov [ r13 + 0x10 ], r11
mov [ r13 + 0x8 ], rcx
mov [ r13 + 0x18 ], r9
mov [ r13 + 0x20 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.2605
; seed 4262903500932446 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1636023 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=334, initial num_batches=31): 148556 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09080312440595273
; number reverted permutation / tried permutation: 72084 / 89960 =80.129%
; number reverted decision / tried decision: 57931 / 90039 =64.340%
; validated in 0.686s
