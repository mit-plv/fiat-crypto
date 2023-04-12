SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x26
imul r10, [ rsi + 0x20 ], 0x26
mov r11, [ rsi + 0x20 ]
lea rdx, [r11 + r11]
mov r11, [ rsi + 0x8 ]
mov rcx, r11
shl rcx, 0x1
xchg rdx, rax
mulx r8, r11, [ rsi + 0x10 ]
mov r9, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
lea rdx, [r9 + 8 * r9]
lea rbx, [r9 + 2 * rdx]
mov rdx, rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, r10
mov [ rsp - 0x68 ], r13
mulx r13, r10, [ rsi + 0x8 ]
add r11, r10
adcx r13, r8
mov r8, 0x1 
shlx r10, [ rsi + 0x10 ], r8
xchg rdx, r10
mov [ rsp - 0x60 ], r14
mulx r14, r8, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov r15, [ rsi + 0x20 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rax
lea rdi, [r15 + 8 * r15]
lea rax, [r15 + 2 * rdi]
xchg rdx, rax
mulx r15, rdi, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], r15
mov [ rsp - 0x38 ], rdi
mulx rdi, r15, r10
xor rdx, rdx
adox r9, r15
adox rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx r15, rbx, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r14
mulx r14, rcx, rax
mov rdx, [ rsi + 0x18 ]
lea rax, [rdx + rdx]
adcx r9, rbx
adcx r15, rdi
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, rax
xor rdx, rdx
adox r11, rbp
adox r12, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, rbp, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rbx
mulx rbx, r10, rdx
adcx rbp, r10
adcx rbx, r13
test al, al
adox rbp, r8
adox rbx, [ rsp - 0x30 ]
mov rdx, 0x7ffffffffffff 
mov r8, r11
and r8, rdx
shrd r11, r12, 51
add r9, r11
adc r15, 0x0
mov r12, r9
shrd r12, r15, 51
mov rdx, [ rsi + 0x10 ]
mulx r10, r13, rdx
xor rdx, rdx
adox rbp, r12
adox rbx, rdx
mov r11, rcx
adcx r11, [ rsp - 0x38 ]
adcx r14, [ rsp - 0x40 ]
test al, al
adox r13, rdi
adox r10, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, rcx, rax
mov rdx, [ rsp - 0x48 ]
mulx r15, rax, [ rsi + 0x0 ]
adcx r13, rax
adcx r15, r10
mov rdx, rbp
shrd rdx, rbx, 51
xor r12, r12
adox r11, rcx
adox rdi, r14
adcx r11, rdx
adc rdi, 0x0
mov rbx, 0x7ffffffffffff 
mov r14, r11
and r14, rbx
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], r14
shrd r11, rdi, 51
test al, al
adox r13, r11
adox r15, r12
mov rcx, r13
shrd rcx, r15, 51
lea rax, [rcx + 8 * rcx]
lea rdx, [rcx + 2 * rax]
lea r8, [ r8 + rdx ]
and r13, rbx
mov rax, r8
shr rax, 51
mov [ r10 + 0x20 ], r13
and r8, rbx
and r9, rbx
lea rax, [ rax + r9 ]
mov rdi, rax
shr rdi, 51
and rax, rbx
mov [ r10 + 0x8 ], rax
and rbp, rbx
lea rdi, [ rdi + rbp ]
mov [ r10 + 0x10 ], rdi
mov [ r10 + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1789
; seed 0751660659242383 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3204 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=264, initial num_batches=31): 348 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.10861423220973783
; number reverted permutation / tried permutation: 407 / 518 =78.571%
; number reverted decision / tried decision: 317 / 481 =65.904%
; validated in 0.205s
