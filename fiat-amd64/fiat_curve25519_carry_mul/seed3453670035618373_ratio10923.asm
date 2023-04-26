SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
sub rsp, 184
mov rax, [ rdx + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r10, [ rsi + 0x20 ]
imul rdx, [ rax + 0x10 ], 0x13
mov r8, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r13, r11
mov rdx, r14
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], r9
mulx r9, rbx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r13
mulx r13, r15, r11
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r13
mulx r13, r11, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], rdi
lea r15, [rdx + 8 * rdx]
lea rdi, [rdx + 2 * r15]
xor rdx, rdx
adox r10, r11
adox r13, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x0 ]
mov rdx, rdi
mulx r11, rdi, [ rsi + 0x18 ]
adcx rbp, rdi
adcx r11, r12
mov r12, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], r13
mulx r13, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox rbp, rdi
adox r13, r11
mov rdx, [ rsi + 0x8 ]
mulx rdi, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], r10
mov [ rsp + 0x0 ], r14
mulx r14, r10, r12
adcx r10, r15
adcx rcx, r14
xor rdx, rdx
adox r10, rbx
adox r9, rcx
mov rdx, [ rsi + 0x20 ]
mulx r15, rbx, r8
adcx rbp, r11
adcx rdi, r13
mov rdx, [ rax + 0x10 ]
mulx r11, r13, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx rcx, r14, [ rsi + 0x0 ]
test al, al
adox r10, r13
adox r11, r9
mov rdx, r8
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, r8
adcx rdx, [ rsp + 0x0 ]
adcx r9, [ rsp - 0x18 ]
add rdx, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
xchg rdx, r12
mulx r8, r13, [ rsi + 0x10 ]
add rbx, [ rsp - 0x20 ]
adcx r15, [ rsp - 0x28 ]
mov [ rsp + 0x8 ], r11
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], rcx
mulx rcx, r10, [ rax + 0x0 ]
xor rdx, rdx
adox rbx, r13
adox r8, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, r13, r11
adcx rbx, r10
adcx rcx, r8
mov rdx, [ rsi + 0x10 ]
mulx r10, r11, [ rax + 0x10 ]
test al, al
adox r12, r13
adox r15, r9
mov rdx, [ rsi + 0x0 ]
mulx r8, r9, [ rax + 0x10 ]
adcx r12, [ rsp - 0x40 ]
adcx r15, [ rsp - 0x48 ]
mov rdx, r12
shrd rdx, r15, 51
mov r13, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], r14
mulx r14, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x28 ], rdi
mov [ rsp + 0x30 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
mov rdx, r11
test al, al
adox rdx, [ rsp - 0x8 ]
adox r10, [ rsp - 0x10 ]
adcx rbx, r15
adcx r14, rcx
xor rcx, rcx
adox rbx, r13
adox r14, rcx
mov r11, rbx
shrd r11, r14, 51
mov r13, r9
xor r15, r15
adox r13, [ rsp + 0x30 ]
adox r8, [ rsp + 0x28 ]
adcx rdx, rdi
adcx rbp, r10
test al, al
adox r13, r11
adox r8, r15
mov rcx, r13
shrd rcx, r8, 51
mov r9, [ rsp + 0x20 ]
mov rdi, r9
add rdi, [ rsp + 0x10 ]
mov r10, [ rsp + 0x18 ]
adcx r10, [ rsp + 0x8 ]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r14, [ rax + 0x20 ]
mov rdx, 0x7ffffffffffff 
and r13, rdx
adox rdi, rcx
adox r10, r15
adcx r9, r14
adcx r11, rbp
mov rbp, rdi
shrd rbp, r10, 51
xor r8, r8
adox r9, rbp
adox r11, r8
and r12, rdx
mov r15, r9
shrd r15, r11, 51
imul rcx, r15, 0x13
lea r12, [ r12 + rcx ]
and r9, rdx
and rbx, rdx
mov r14, r12
and r14, rdx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x20 ], r9
mov [ r10 + 0x0 ], r14
shr r12, 51
lea r12, [ r12 + rbx ]
mov rbp, r12
and rbp, rdx
shr r12, 51
mov [ r10 + 0x8 ], rbp
and rdi, rdx
lea r12, [ r12 + r13 ]
mov [ r10 + 0x10 ], r12
mov [ r10 + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 184
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0923
; seed 3453670035618373 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5649 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=197, initial num_batches=31): 331 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05859444149406975
; number reverted permutation / tried permutation: 394 / 490 =80.408%
; number reverted decision / tried decision: 280 / 509 =55.010%
; validated in 0.345s
