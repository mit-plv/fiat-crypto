SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
imul rax, [ rdx + 0x10 ], 0x13
xchg rdx, r11
mulx rcx, r10, [ rsi + 0x8 ]
mov r8, rdx
mov rdx, [ r11 + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ r11 + 0x0 ]
mov rdx, [ r11 + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
add rbp, r9
adcx rbx, r12
mov rdx, [ r11 + 0x8 ]
mulx r9, r13, [ rsi + 0x10 ]
mov rdx, rax
mulx r12, rax, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, r14
imul rdx, [ r11 + 0x18 ], 0x13
xchg rdx, r15
mov [ rsp - 0x40 ], rbp
mulx rbp, r14, [ rsi + 0x18 ]
mov rdx, r15
mov [ rsp - 0x38 ], r9
mulx r9, r15, [ rsi + 0x10 ]
test al, al
adox rdi, r14
adox rbp, rbx
adcx rdi, r15
adcx r9, rbp
test al, al
adox rdi, r10
adox rcx, r9
xchg rdx, r8
mulx rbx, r10, [ rsi + 0x18 ]
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r15, [ r11 + 0x0 ]
mov rdx, r8
mulx r9, r8, [ rsi + 0x18 ]
adcx rdi, r15
adcx rbp, rcx
mulx r15, rcx, [ rsi + 0x20 ]
mov rdx, rdi
shrd rdx, rbp, 51
xor rbp, rbp
adox rcx, r10
adox rbx, r15
adcx rax, r8
adcx r9, r12
mov r12, rdx
mov rdx, [ r11 + 0x0 ]
mulx r8, r10, [ rsi + 0x10 ]
add rcx, r10
adcx r8, rbx
mov rdx, r14
mulx r15, r14, [ rsi + 0x10 ]
add rax, r14
adcx r15, r9
mov rbx, rdx
mov rdx, [ r11 + 0x10 ]
mulx r10, r9, [ rsi + 0x0 ]
mov rdx, [ r11 + 0x0 ]
mulx rbp, r14, [ rsi + 0x8 ]
mov rdx, 0x33 
mov [ rsp - 0x30 ], r13
bzhi r13, rdi, rdx
adox rax, r14
adox rbp, r15
mov rdx, [ r11 + 0x8 ]
mulx r15, rdi, [ rsi + 0x8 ]
xor rdx, rdx
adox rcx, rdi
adox r15, r8
mov rdx, [ r11 + 0x8 ]
mulx r14, r8, [ rsi + 0x0 ]
adcx rax, r8
adcx r14, rbp
mov rdx, [ r11 + 0x0 ]
mulx rdi, rbp, [ rsi + 0x18 ]
test al, al
adox rcx, r9
adox r10, r15
mov rdx, [ rsi + 0x20 ]
mulx r15, r9, rbx
adcx rax, r12
adc r14, 0x0
mov rdx, rax
shrd rdx, r14, 51
test al, al
adox r9, rbp
adox rdi, r15
adcx rcx, rdx
adc r10, 0x0
mov rdx, [ r11 + 0x18 ]
mulx r12, rbx, [ rsi + 0x8 ]
add r9, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
mov rdx, [ r11 + 0x10 ]
mulx rbp, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, [ r11 + 0x10 ]
test al, al
adox r9, r8
adox rbp, rdi
mov rdx, r15
adcx rdx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
add rdx, rbx
adcx r12, r14
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rdi, [ r11 + 0x18 ]
xor rdx, rdx
adox r9, rdi
adox r8, rbp
mov r15, rcx
shrd r15, r10, 51
add r9, r15
adc r8, 0x0
mov rdx, [ r11 + 0x20 ]
mulx rbp, r10, [ rsi + 0x0 ]
mov rdx, r9
shrd rdx, r8, 51
xor r14, r14
adox rbx, r10
adox rbp, r12
mov r12, 0x33 
bzhi rdi, r9, r12
adox rbx, rdx
adox rbp, r14
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x18 ], rdi
mov r9, rbx
shrd r9, rbp, 51
imul r8, r9, 0x13
lea r13, [ r13 + r8 ]
bzhi r10, rax, r12
bzhi rax, r13, r12
shr r13, 51
mov [ r15 + 0x0 ], rax
lea r13, [ r13 + r10 ]
mov rdx, r13
shr rdx, 51
bzhi rdi, r13, r12
bzhi rbp, rcx, r12
bzhi rcx, rbx, r12
mov [ r15 + 0x8 ], rdi
lea rdx, [ rdx + rbp ]
mov [ r15 + 0x20 ], rcx
mov [ r15 + 0x10 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1786
; seed 1771460510736352 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1638739 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 112135 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0684276141594238
; number reverted permutation / tried permutation: 76346 / 90173 =84.666%
; number reverted decision / tried decision: 42985 / 89826 =47.854%
; validated in 0.499s
