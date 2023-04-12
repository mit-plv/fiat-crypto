SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
imul rax, [ rsi + 0x20 ], 0x26
mov rdx, r11
mulx r11, r10, [ rsi + 0x18 ]
imul rcx, [ rsi + 0x20 ], 0x2
mov r8, 0x1 
shlx r9, [ rsi + 0x8 ], r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rax
imul rdx, [ rsi + 0x18 ], 0x26
xchg rdx, rax
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
xchg rdx, rax
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
test al, al
adox r15, r13
adox r14, rdi
mov rdx, [ rsi + 0x0 ]
mulx rdi, r13, rdx
adcx r15, r13
adcx rdi, r14
xor rdx, rdx
adox rbp, r8
adox rbx, r12
mov rdx, [ rsi + 0x0 ]
mulx r12, r8, r9
mov rdx, rax
mulx r9, rax, [ rsi + 0x10 ]
adcx r10, rax
adcx r9, r11
mov rdx, r15
shrd rdx, rdi, 51
xor r11, r11
adox r10, r8
adox r12, r9
adcx r10, rdx
adc r12, 0x0
mov r14, r10
shrd r14, r12, 51
mov r13, 0x1 
shlx rdi, [ rsi + 0x10 ], r13
mov rdx, rdi
mulx r8, rdi, [ rsi + 0x0 ]
xor rax, rax
adox rbp, rdi
adox r8, rbx
adcx rbp, r14
adc r8, 0x0
mov r11, [ rsi + 0x18 ]
lea rbx, [r11 + r11]
mov r11, [ rsi + 0x20 ]
lea r9, [r11 + 8 * r11]
lea r12, [r11 + 2 * r9]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r9, rbx
mov rdx, rbp
shrd rdx, r8, 51
xchg rdx, r11
mulx r8, rdi, [ rsi + 0x8 ]
mov rdx, r12
mulx rax, r12, [ rsi + 0x20 ]
xor rdx, rdx
adox r12, rdi
adox r8, rax
mov rdx, [ rsi + 0x10 ]
mulx rax, rdi, rdx
adcx rdi, r9
adcx r14, rax
mov rdx, rbx
mulx r9, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, rbx
adox r9, r8
adcx r12, r11
adc r9, 0x0
mov r11, r12
shrd r11, r9, 51
mov rdx, rcx
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0x7ffffffffffff 
and r12, rdx
and r15, rdx
adox rdi, rcx
adox r8, r14
adcx rdi, r11
adc r8, 0x0
mov rax, rdi
shrd rax, r8, 51
lea r14, [rax + 8 * rax]
lea rbx, [rax + 2 * r14]
lea r15, [ r15 + rbx ]
mov r14, r15
and r14, rdx
and r10, rdx
shr r15, 51
lea r15, [ r15 + r10 ]
mov r9, r15
shr r9, 51
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x0 ], r14
and rbp, rdx
lea r9, [ r9 + rbp ]
and rdi, rdx
mov [ r11 + 0x10 ], r9
mov [ r11 + 0x20 ], rdi
mov [ r11 + 0x18 ], r12
and r15, rdx
mov [ r11 + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1992
; seed 0690481031246809 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 674323 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=302, initial num_batches=31): 78096 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11581393486504242
; number reverted permutation / tried permutation: 73331 / 89963 =81.512%
; number reverted decision / tried decision: 58453 / 90036 =64.922%
; validated in 0.257s
