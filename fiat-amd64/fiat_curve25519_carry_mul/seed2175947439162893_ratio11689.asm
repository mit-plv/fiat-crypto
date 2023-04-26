SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
xor rdx, rdx
adox r10, rcx
adox r8, r11
mov rdx, [ rax + 0x10 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
lea rbp, [rdx + 8 * rdx]
lea r12, [rdx + 2 * rbp]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, r12
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
lea r14, [rdx + 8 * rdx]
lea r15, [rdx + 2 * r14]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], rbp
mulx rbp, r13, r15
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], r13
lea rbp, [rdx + 8 * rdx]
lea r13, [rdx + 2 * rbp]
mov rdx, r13
mulx r13, rbp, [ rsi + 0x20 ]
adcx rbp, r14
adcx rdi, r13
test al, al
adox rbp, r9
adox rbx, rdi
adcx r10, r11
adcx rcx, r8
mov r9, rdx
mov rdx, [ rax + 0x20 ]
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
lea r14, [rdx + 8 * rdx]
lea r13, [rdx + 2 * r14]
mov rdx, [ rax + 0x18 ]
mulx rdi, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r11
mulx r11, r13, [ rax + 0x8 ]
xor rdx, rdx
adox r10, r14
adox rdi, rcx
adcx rbp, r13
adcx r11, rbx
mov rdx, r9
mulx rbx, r9, [ rsi + 0x18 ]
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r13, r14, r12
test al, al
adox r10, r8
adox rdi, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rax + 0x0 ]
mov rdx, [ rsp - 0x28 ]
mov [ rsp - 0x18 ], rdi
mov [ rsp - 0x10 ], r10
mulx r10, rdi, [ rsi + 0x20 ]
mov rdx, r15
mov [ rsp - 0x8 ], r11
mulx r11, r15, [ rsi + 0x10 ]
adcx r14, r9
adcx rbx, r13
add r14, r15
adcx r11, rbx
add r14, r12
adcx r8, r11
mov r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r12, r13, rcx
test al, al
adox rdi, [ rsp - 0x40 ]
adox r10, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx r15, rcx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, rbx, [ rax + 0x10 ]
adcx rdi, r13
adcx r12, r10
xor rdx, rdx
adox rdi, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
adcx rdi, rcx
adcx r15, r12
mov r13, rdi
shrd r13, r15, 51
xor r10, r10
adox rbp, rbx
adox r11, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rbx, rcx, [ rax + 0x8 ]
adcx r14, rcx
adcx rbx, r8
add r14, r13
adc rbx, 0x0
mov rdx, [ rax + 0x8 ]
mulx r12, r8, [ rsi + 0x10 ]
mov rdx, r14
shrd rdx, rbx, 51
xor r15, r15
adox rbp, rdx
adox r11, r15
mov r10, rbp
shrd r10, r11, 51
mov rdx, r9
mulx r13, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx rbx, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x0 ]
test al, al
adox r9, r11
adox r15, r13
adcx r9, r8
adcx r12, r15
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rax + 0x18 ]
test al, al
adox r9, rcx
adox rbx, r12
adcx r9, r8
adcx r13, rbx
add r9, r10
adc r13, 0x0
mov rdx, r9
shrd rdx, r13, 51
mov r10, 0x7ffffffffffff 
and rbp, r10
mov rcx, rdx
adox rcx, [ rsp - 0x10 ]
mov r11, [ rsp - 0x18 ]
mov r15, 0x0 
adox r11, r15
and rdi, r10
mov r12, rcx
and r12, r10
shrd rcx, r11, 51
lea r8, [rcx + 8 * rcx]
lea rbx, [rcx + 2 * r8]
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x20 ], r12
and r14, r10
lea rdi, [ rdi + rbx ]
mov r13, rdi
and r13, r10
mov [ r8 + 0x0 ], r13
shr rdi, 51
lea rdi, [ rdi + r14 ]
mov rdx, rdi
and rdx, r10
shr rdi, 51
lea rdi, [ rdi + rbp ]
and r9, r10
mov [ r8 + 0x18 ], r9
mov [ r8 + 0x8 ], rdx
mov [ r8 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.1689
; seed 2175947439162893 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 11537 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=123, initial num_batches=31): 648 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05616711450117015
; number reverted permutation / tried permutation: 387 / 515 =75.146%
; number reverted decision / tried decision: 244 / 484 =50.413%
; validated in 0.505s
