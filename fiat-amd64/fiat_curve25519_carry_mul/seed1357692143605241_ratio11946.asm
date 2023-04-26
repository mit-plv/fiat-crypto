SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
sub rsp, 168
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, [ rdx + 0x8 ]
lea r10, [rax + 8 * rax]
lea rcx, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r8, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r11
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r11
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
lea r14, [rdx + 8 * rdx]
lea r13, [rdx + 2 * r14]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rdi
mulx rdi, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r14
mulx r14, rdi, r11
mov rdx, r13
mov [ rsp - 0x20 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r13
mulx r13, r15, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r12
xor r12, r12
adox r15, rdi
adox r14, r13
mov rdi, rdx
mov rdx, [ rax + 0x0 ]
mulx r12, r13, [ rsi + 0x10 ]
adcx r15, r13
adcx r12, r14
mov rdx, [ rsi + 0x20 ]
mulx r13, r14, [ rax + 0x0 ]
add r14, r10
adcx r8, r13
add r14, r9
adcx rbx, r8
imul rdx, [ rax + 0x10 ], 0x13
xchg rdx, rcx
mulx r9, r10, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r8, r13, [ rax + 0x0 ]
xor rdx, rdx
adox r15, rbp
adox r12, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r8
mulx r8, rbp, rcx
adcx r10, rbp
adcx r8, r9
test al, al
adox r10, [ rsp - 0x10 ]
adox r8, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x8 ], r13
mulx r13, r11, [ rax + 0x18 ]
mov rdx, rdi
mov [ rsp + 0x10 ], r12
mulx r12, rdi, [ rsi + 0x18 ]
adcx r14, r11
adcx r13, rbx
mov rdx, rcx
mulx rbx, rcx, [ rsi + 0x20 ]
add rcx, rdi
adcx r12, rbx
test al, al
adox rcx, [ rsp - 0x20 ]
adox r12, [ rsp - 0x38 ]
mov rdx, [ rax + 0x0 ]
mulx rdi, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r13
mulx r13, rbx, [ rax + 0x0 ]
adcx r10, r9
adcx rbp, r8
test al, al
adox rcx, rbx
adox r13, r12
adcx r10, r11
adcx rdi, rbp
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, r10
shrd rdx, rdi, 51
xor r12, r12
adox rcx, r8
adox r9, r13
mov r11, 0x7ffffffffffff 
and r10, r11
adox rcx, rdx
adox r9, r12
mov rbx, rcx
shrd rbx, r9, 51
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mulx r12, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r9
adox r12, [ rsp + 0x10 ]
mov r9, [ rsp + 0x8 ]
mov r11, r9
adcx r11, [ rsp - 0x40 ]
mov [ rsp + 0x20 ], r10
mov r10, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x48 ]
xor r9, r9
adox r15, rbx
adox r12, r9
adcx r11, rbp
adcx r13, r10
xor rdx, rdx
adox r11, [ rsp - 0x28 ]
adox r13, [ rsp - 0x30 ]
mov r9, r15
shrd r9, r12, 51
add r11, rdi
adcx r8, r13
test al, al
adox r11, r9
adox r8, rdx
mov rbx, r11
shrd rbx, r8, 51
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rax + 0x20 ]
test al, al
adox r14, rbp
adox rdi, [ rsp + 0x18 ]
adcx r14, rbx
adc rdi, 0x0
mov rdx, 0x33 
bzhi r10, r14, rdx
shrd r14, rdi, 51
imul r12, r14, 0x13
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x20 ], r10
add r12, [ rsp + 0x20 ]
mov r9, r12
shr r9, 51
bzhi r8, r12, rdx
bzhi rbx, rcx, rdx
bzhi rcx, r15, rdx
lea r9, [ r9 + rbx ]
mov r15, r9
shr r15, 51
lea r15, [ r15 + rcx ]
mov [ r13 + 0x10 ], r15
bzhi rbp, r11, rdx
bzhi r11, r9, rdx
mov [ r13 + 0x8 ], r11
mov [ r13 + 0x18 ], rbp
mov [ r13 + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 168
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1946
; seed 1357692143605241 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 6918 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=197, initial num_batches=31): 439 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.06345764671870482
; number reverted permutation / tried permutation: 321 / 489 =65.644%
; number reverted decision / tried decision: 252 / 510 =49.412%
; validated in 0.416s
