SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
lea rcx, [rdx + 8 * rdx]
lea r8, [rdx + 2 * rcx]
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, r8
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rax + 0x8 ]
test al, al
adox r10, rbx
adox rbp, r11
mov rdx, [ rax + 0x8 ]
lea r11, [rdx + 8 * rdx]
lea rbx, [rdx + 2 * r11]
mov r11, [ rax + 0x18 ]
mov [ rsp - 0x70 ], r12
lea rdx, [r11 + 8 * r11]
lea r12, [r11 + 2 * rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mulx r13, r11, rbx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov r14, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
lea r15, [r14 + 8 * r14]
lea rdi, [r14 + 2 * r15]
xchg rdx, rdi
mulx r15, r14, [ rsi + 0x18 ]
adcx r11, r14
adcx r15, r13
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], rbp
mulx rbp, r14, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r10
mov [ rsp - 0x38 ], r9
mulx r9, r10, r8
xor rdx, rdx
adox r11, r14
adox rbp, r15
adcx r12, r10
adcx r9, rbx
xor rbx, rbx
adox r11, rcx
adox rbp, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, rcx, r13
mov rdx, [ rsi + 0x0 ]
mulx r14, r13, [ rax + 0x0 ]
mov rdx, rdi
mulx r10, rdi, [ rsi + 0x18 ]
adcx rcx, rdi
adcx r10, r15
test al, al
adox r11, r13
adox r14, rbp
mov rdx, 0x7ffffffffffff 
mov rbp, r11
and rbp, rdx
shrd r11, r14, 51
mov rdx, [ rsi + 0x10 ]
mulx r13, r15, r8
test al, al
adox rcx, r15
adox r13, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rdi, [ rax + 0x0 ]
adcx rcx, rdi
adcx r10, r13
mov rdx, [ rax + 0x8 ]
mulx r15, r14, [ rsi + 0x0 ]
test al, al
adox rcx, r14
adox r15, r10
mov rdx, [ rax + 0x0 ]
mulx rdi, r13, [ rsi + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r14, r10, [ rsi + 0x0 ]
adcx rcx, r11
adc r15, 0x0
mov rdx, [ rsi + 0x8 ]
mulx rbx, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x30 ], rbp
mov [ rsp - 0x28 ], r14
mulx r14, rbp, r8
add r12, r13
adcx rdi, r9
xor rdx, rdx
adox r12, r11
adox rbx, rdi
mov r8, rcx
shrd r8, r15, 51
test al, al
adox r12, r10
adox rbx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, [ rax + 0x0 ]
adcx r12, r8
adc rbx, 0x0
mov rdx, [ rsi + 0x10 ]
mulx r15, r10, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, r9
adox r13, r14
adcx rbp, r10
adcx r15, r13
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r10, r9, [ rsi + 0x0 ]
test al, al
adox rbp, rdi
adox r8, r15
mov rdx, r12
shrd rdx, rbx, 51
mov rbx, rdx
mov rdx, [ rax + 0x18 ]
mulx r15, r13, [ rsi + 0x8 ]
test al, al
adox rbp, r9
adox r10, r8
adcx rbp, rbx
adc r10, 0x0
mov rdx, [ rsi + 0x0 ]
mulx r9, rdi, [ rax + 0x20 ]
mov rdx, r11
add rdx, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
xor r11, r11
adox rdx, r13
adox r15, r14
mov r8, rbp
shrd r8, r10, 51
mov rbx, 0x7ffffffffffff 
and rbp, rbx
adox rdx, rdi
adox r9, r15
adcx rdx, r8
adc r9, 0x0
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x18 ], rbp
mov r10, rdx
shrd r10, r9, 51
imul rdi, r10, 0x13
add rdi, [ rsp - 0x30 ]
and rcx, rbx
mov r14, rdi
shr r14, 51
lea r14, [ r14 + rcx ]
mov r15, r14
shr r15, 51
and r12, rbx
lea r15, [ r15 + r12 ]
mov [ r13 + 0x10 ], r15
and rdi, rbx
mov [ r13 + 0x0 ], rdi
and r14, rbx
mov [ r13 + 0x8 ], r14
and rdx, rbx
mov [ r13 + 0x20 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2090
; seed 2985359769239054 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1088794 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=232, initial num_batches=31): 86420 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07937222284472545
; number reverted permutation / tried permutation: 69907 / 89829 =77.822%
; number reverted decision / tried decision: 46650 / 90170 =51.736%
; validated in 0.377s
