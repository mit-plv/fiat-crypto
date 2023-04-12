SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
sub rsp, 144
mov rax, [ rdx + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
lea rbx, [rdx + 8 * rdx]
lea rbp, [rdx + 2 * rbx]
mov rdx, r11
mulx rbx, r11, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
imul rdx, [ rax + 0x8 ], 0x13
mov [ rsp - 0x48 ], r14
xor r14, r14
adox r10, r8
adox r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r14, r8, [ rax + 0x20 ]
adcx r10, r15
adcx rdi, r9
mov rdx, r12
mulx r15, r12, [ rsi + 0x20 ]
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r8
mulx r8, r14, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x30 ], rdi
mov [ rsp - 0x28 ], r10
lea rdi, [rdx + 8 * rdx]
lea r10, [rdx + 2 * rdi]
mov rdx, r10
mulx rdi, r10, [ rsi + 0x20 ]
mov [ rsp - 0x20 ], r13
mov [ rsp - 0x18 ], rbx
mulx rbx, r13, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r11
xor r11, r11
adox r10, r14
adox r8, rdi
xchg rdx, rbp
mulx rdi, r14, [ rsi + 0x18 ]
adcx r12, r13
adcx rbx, r15
xchg rdx, r9
mulx r13, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r8
mulx r8, r11, [ rax + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp + 0x0 ], r8
mov [ rsp + 0x8 ], r11
mulx r11, r8, rcx
test al, al
adox r8, r14
adox rdi, r11
mov rdx, [ rsi + 0x8 ]
mulx r14, rcx, rbp
adcx r8, r15
adcx r13, rdi
mov rdx, r9
mulx r15, r9, [ rsi + 0x20 ]
test al, al
adox r9, [ rsp - 0x10 ]
adox r15, [ rsp - 0x18 ]
adcx r8, rcx
adcx r14, r13
mov rdx, [ rsi + 0x10 ]
mulx rdi, r11, rbp
mov rdx, [ rax + 0x0 ]
mulx rcx, rbp, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r11
adox rdi, r15
adcx r9, rbp
adcx rcx, rdi
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rax + 0x0 ]
test al, al
adox r8, r13
adox r15, r14
mov rdx, [ rax + 0x0 ]
mulx r11, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rax + 0x8 ]
adcx r12, r14
adcx r11, rbx
mov rdx, r8
shrd rdx, r15, 51
xor rbx, rbx
adox r9, rbp
adox rdi, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, [ rax + 0x10 ]
adcx r9, rcx
adc rdi, 0x0
xor rdx, rdx
adox r12, [ rsp - 0x20 ]
adox r11, [ rsp - 0x48 ]
mov rbx, 0x7ffffffffffff 
and r8, rbx
adox r12, r13
adox r15, r11
mov rdx, [ rsi + 0x10 ]
mulx rbp, r14, [ rax + 0x8 ]
mov rdx, r9
shrd rdx, rdi, 51
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mulx rdi, r13, [ rax + 0x10 ]
xor rdx, rdx
adox r12, rcx
adox r15, rdx
adcx r10, r14
adcx rbp, [ rsp - 0x8 ]
mov r11, [ rsp + 0x8 ]
mov r14, r11
add r14, [ rsp - 0x28 ]
mov rcx, [ rsp + 0x0 ]
adcx rcx, [ rsp - 0x30 ]
mov rdx, [ rax + 0x18 ]
mulx rbx, r11, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, r15, 51
xor r15, r15
adox r10, r13
adox rdi, rbp
adcx r10, r11
adcx rbx, rdi
add r10, rdx
adc rbx, 0x0
mov r13, 0x7ffffffffffff 
mov rbp, r10
and rbp, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x18 ], rbp
shrd r10, rbx, 51
xor rdx, rdx
adox r14, [ rsp - 0x38 ]
adox rcx, [ rsp - 0x40 ]
adcx r14, r10
adc rcx, 0x0
and r12, r13
mov r15, r14
and r15, r13
shrd r14, rcx, 51
imul rdi, r14, 0x13
lea r8, [ r8 + rdi ]
mov rbx, r8
shr rbx, 51
and r9, r13
and r8, r13
lea rbx, [ rbx + r9 ]
mov rbp, rbx
shr rbp, 51
mov [ r11 + 0x0 ], r8
and rbx, r13
lea rbp, [ rbp + r12 ]
mov [ r11 + 0x20 ], r15
mov [ r11 + 0x8 ], rbx
mov [ r11 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.2265
; seed 1204625481953541 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5190 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=198, initial num_batches=31): 369 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.07109826589595376
; number reverted permutation / tried permutation: 374 / 503 =74.354%
; number reverted decision / tried decision: 267 / 496 =53.831%
; validated in 0.328s
