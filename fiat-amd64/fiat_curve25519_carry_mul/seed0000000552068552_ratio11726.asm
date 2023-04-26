SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
imul rax, [ rdx + 0x10 ], 0x13
mov r10, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ r10 + 0x18 ]
mov rdx, [ r10 + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
lea rbp, [rdx + 8 * rdx]
lea r12, [rdx + 2 * rbp]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, [ r10 + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ r10 + 0x0 ]
mov rdx, [ r10 + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], r15
mulx r15, r9, [ r10 + 0x0 ]
imul rdx, [ r10 + 0x18 ], 0x13
mov [ rsp - 0x20 ], r14
xor r14, r14
adox rcx, r9
adox r15, r8
mov r8, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r9, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r15
mulx r15, r12, rax
adcx r9, r12
adcx r15, r14
mov rdx, r8
mulx r14, r8, [ rsi + 0x10 ]
test al, al
adox r9, r8
adox r14, r15
adcx r9, rbx
adcx rdi, r14
mulx r12, rbx, [ rsi + 0x18 ]
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, [ r10 + 0x0 ]
xor rdx, rdx
adox r9, r8
adox r14, rdi
mov rdx, rax
mulx rdi, rax, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r14
mulx r14, r8, r11
adcx rax, rbx
adcx r12, rdi
add rax, r8
adcx r14, r12
test al, al
adox rax, rbp
adox r13, r14
mov rdx, [ rsi + 0x0 ]
mulx rbx, rbp, [ r10 + 0x8 ]
mov rdx, r11
mulx rdi, r11, [ rsi + 0x18 ]
adcx rax, rbp
adcx rbx, r13
mov rdx, [ r10 + 0x8 ]
mulx r12, r8, [ rsi + 0x10 ]
mov rdx, r15
mulx r14, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rbp, r13, [ r10 + 0x10 ]
add r15, r11
adcx rdi, r14
test al, al
adox r15, [ rsp - 0x20 ]
adox rdi, [ rsp - 0x28 ]
mov rdx, [ r10 + 0x8 ]
mulx r14, r11, [ rsi + 0x8 ]
adcx rcx, r8
adcx r12, [ rsp - 0x18 ]
mov rdx, [ rsp - 0x10 ]
mov r8, r9
shrd r8, rdx, 51
test al, al
adox rax, r8
mov rdx, 0x0 
adox rbx, rdx
adcx r15, r11
adcx r14, rdi
mov rdx, [ r10 + 0x10 ]
mulx r11, rdi, [ rsi + 0x0 ]
mov rdx, rax
shrd rdx, rbx, 51
add r15, rdi
adcx r11, r14
test al, al
adox r15, rdx
mov r8, 0x0 
adox r11, r8
mov rbx, r15
shrd rbx, r11, 51
test al, al
adox rcx, r13
adox rbp, r12
adcx rcx, [ rsp - 0x30 ]
adcx rbp, [ rsp - 0x48 ]
mov rdx, [ r10 + 0x0 ]
mulx r12, r13, [ rsi + 0x20 ]
mov rdx, [ r10 + 0x18 ]
mulx rdi, r14, [ rsi + 0x8 ]
xor rdx, rdx
adox r13, [ rsp - 0x38 ]
adox r12, [ rsp - 0x40 ]
adcx rcx, rbx
adc rbp, 0x0
mov rdx, [ r10 + 0x10 ]
mulx r11, r8, [ rsi + 0x10 ]
add r13, r8
adcx r11, r12
mov rdx, [ r10 + 0x20 ]
mulx r12, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r13, r14
adox rdi, r11
adcx r13, rbx
adcx r12, rdi
mov r14, rcx
shrd r14, rbp, 51
test al, al
adox r13, r14
adox r12, rdx
mov rbp, r13
shrd rbp, r12, 51
imul r8, rbp, 0x13
mov r11, 0x7ffffffffffff 
and r9, r11
lea r9, [ r9 + r8 ]
mov rbx, r9
and rbx, r11
and rax, r11
and r13, r11
shr r9, 51
lea r9, [ r9 + rax ]
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], rbx
mov r14, r9
shr r14, 51
and rcx, r11
and r9, r11
mov [ rdi + 0x8 ], r9
and r15, r11
lea r14, [ r14 + r15 ]
mov [ rdi + 0x18 ], rcx
mov [ rdi + 0x20 ], r13
mov [ rdi + 0x10 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.1726
; seed 2613449178064061 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1079414 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=200, initial num_batches=31): 79771 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07390213578849264
; number reverted permutation / tried permutation: 68192 / 89391 =76.285%
; number reverted decision / tried decision: 46402 / 90608 =51.212%
; validated in 0.387s
