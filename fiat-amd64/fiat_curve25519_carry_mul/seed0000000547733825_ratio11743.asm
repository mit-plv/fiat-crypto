SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
sub rsp, 152
imul rax, [ rdx + 0x18 ], 0x13
mov r10, [ rdx + 0x20 ]
lea r11, [r10 + 8 * r10]
lea rcx, [r10 + 2 * r11]
mov r10, rdx
mov rdx, [ rdx + 0x10 ]
mulx r8, r11, [ rsi + 0x10 ]
mov rdx, [ r10 + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x0 ]
mov rdx, rax
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
imul r14, [ r10 + 0x10 ], 0x13
mov [ rsp - 0x58 ], r15
mov r15, [ r10 + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
lea rdi, [r15 + 8 * r15]
lea rbx, [r15 + 2 * rdi]
xchg rdx, r14
mulx r15, rdi, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r9
mov r9, rdx
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x38 ], r8
mov [ rsp - 0x30 ], r11
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, [ r10 + 0x0 ]
mov [ rsp - 0x28 ], r11
mov [ rsp - 0x20 ], r8
mulx r8, r11, [ rsi + 0x20 ]
mov rdx, [ r10 + 0x8 ]
mov [ rsp - 0x18 ], rbp
mov [ rsp - 0x10 ], rax
mulx rax, rbp, [ rsi + 0x18 ]
test al, al
adox r11, rbp
adox rax, r8
mov rdx, r9
mulx r8, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x8 ], rax
mulx rax, rbp, rcx
adcx r9, r12
adcx r13, r8
mov rdx, [ rsi + 0x20 ]
mulx r8, r12, rbx
xor rdx, rdx
adox r12, rdi
adox r15, r8
adcx r12, [ rsp - 0x10 ]
adcx r15, [ rsp - 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx rdi, rbx, r14
mov rdx, rcx
mulx r14, rcx, [ rsi + 0x18 ]
xor r8, r8
adox rbx, rcx
adox r14, rdi
mov rdi, rdx
mov rdx, [ r10 + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r11
mov [ rsp + 0x8 ], r13
mulx r13, r11, [ r10 + 0x8 ]
adcx rbp, rcx
adcx r8, rax
mov rdx, [ r10 + 0x0 ]
mulx rcx, rax, [ rsi + 0x10 ]
xor rdx, rdx
adox rbx, rax
adox rcx, r14
mov rdx, rdi
mulx r14, rdi, [ rsi + 0x8 ]
adcx r12, rdi
adcx r14, r15
test al, al
adox r12, [ rsp - 0x20 ]
adox r14, [ rsp - 0x28 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, rax, [ r10 + 0x10 ]
adcx rbx, r11
adcx r13, rcx
test al, al
adox rbx, rax
adox rdi, r13
mov rdx, [ r10 + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, rax, r15
mov rdx, [ r10 + 0x8 ]
mov [ rsp + 0x10 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
adcx r9, rax
adcx r13, [ rsp + 0x8 ]
test al, al
adox r9, r11
adox rcx, r13
adcx r9, r15
adcx rdi, rcx
mov rdx, r12
shrd rdx, r14, 51
xor r14, r14
adox r9, rdx
adox rdi, r14
mov r11, 0x7ffffffffffff 
mov rax, r9
and rax, r11
shrd r9, rdi, 51
and r12, r11
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, [ r10 + 0x8 ]
mov rdx, [ r10 + 0x10 ]
mulx rdi, rcx, [ rsi + 0x8 ]
adox rbp, r15
adox r13, r8
adcx rbp, rcx
adcx rdi, r13
test al, al
adox rbx, r9
mov rdx, [ rsp + 0x10 ]
adox rdx, r14
mov r8, rbx
shrd r8, rdx, 51
mov rdx, [ r10 + 0x18 ]
mulx r15, r9, [ rsi + 0x0 ]
test al, al
adox rbp, r9
adox r15, rdi
mov rdx, [ rsi + 0x8 ]
mulx r13, rcx, [ r10 + 0x18 ]
adcx rbp, r8
adc r15, 0x0
mov rdx, [ rsp + 0x0 ]
xor rdi, rdi
adox rdx, [ rsp - 0x30 ]
mov r14, [ rsp - 0x8 ]
adox r14, [ rsp - 0x38 ]
adcx rdx, rcx
adcx r13, r14
mov r8, rbp
shrd r8, r15, 51
xor r9, r9
adox rdx, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
adcx rdx, r8
adc r13, 0x0
and rbp, r11
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], rbp
mov rcx, rdx
and rcx, r11
shrd rdx, r13, 51
imul r15, rdx, 0x13
lea r12, [ r12 + r15 ]
mov r14, r12
shr r14, 51
lea r14, [ r14 + rax ]
mov rax, r14
shr rax, 51
and r14, r11
and rbx, r11
and r12, r11
mov [ rdi + 0x0 ], r12
mov [ rdi + 0x20 ], rcx
lea rax, [ rax + rbx ]
mov [ rdi + 0x10 ], rax
mov [ rdi + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1743
; seed 3725409830005307 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1074313 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=198, initial num_batches=31): 80179 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07463281185278406
; number reverted permutation / tried permutation: 69213 / 89722 =77.142%
; number reverted decision / tried decision: 47167 / 90277 =52.247%
; validated in 0.418s
