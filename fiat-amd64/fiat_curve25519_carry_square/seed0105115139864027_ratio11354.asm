SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
mov r10, [ rsi + 0x8 ]
lea r11, [r10 + r10]
mov r10, [ rsi + 0x20 ]
lea rdx, [r10 + 8 * r10]
lea rcx, [r10 + 2 * rdx]
imul r10, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x10 ]
lea r8, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, rax
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov r12, 0x1 
mov [ rsp - 0x68 ], r13
shlx r13, [ rsi + 0x18 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, r11
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r11
lea rdi, [rdx + 8 * rdx]
lea r11, [rdx + 2 * rdi]
mov rdi, [ rsi + 0x20 ]
lea rdx, [rdi + rdi]
xchg rdx, rcx
mov [ rsp - 0x38 ], rcx
mulx rcx, rdi, [ rsi + 0x20 ]
mov rdx, r11
mov [ rsp - 0x30 ], r10
mulx r10, r11, [ rsi + 0x18 ]
mov rdx, r8
mov [ rsp - 0x28 ], r10
mulx r10, r8, [ rsi + 0x8 ]
test al, al
adox rdi, r8
adox r10, rcx
adcx rdi, r14
adcx r15, r10
mov r14, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, rdx
test al, al
adox rax, r9
adox rbx, rbp
mov rdx, [ rsi + 0x8 ]
mulx rbp, r9, r12
mov rdx, [ rsp - 0x30 ]
mov [ rsp - 0x20 ], r15
mulx r15, r10, [ rsi + 0x10 ]
adcx r10, r9
adcx rbp, r15
xor rdx, rdx
adox r10, rcx
adox r8, rbp
mov rcx, r10
shrd rcx, r8, 51
mov rdx, r12
mulx r9, r12, [ rsi + 0x10 ]
mov rdx, r13
mulx r15, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rbp, rdx
add r11, r12
adcx r9, [ rsp - 0x28 ]
test al, al
adox r11, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
adcx rbp, r13
adcx r15, r8
mov rdx, [ rsi + 0x0 ]
mulx r13, r12, r14
test al, al
adox r11, rcx
mov rdx, 0x0 
adox r9, rdx
mov r14, 0x7ffffffffffff 
mov rcx, r11
and rcx, r14
shrd r11, r9, 51
xor r8, r8
adox rax, r12
adox r13, rbx
adcx rax, r11
adc r13, 0x0
mov rdx, rax
shrd rdx, r13, 51
add rdi, rdx
mov rbx, [ rsp - 0x20 ]
adc rbx, 0x0
mov r12, rdi
shrd r12, rbx, 51
mov rdx, [ rsp - 0x38 ]
mulx r11, r9, [ rsi + 0x0 ]
and rax, r14
adox rbp, r9
adox r11, r15
adcx rbp, r12
adc r11, 0x0
mov rdx, rbp
shrd rdx, r11, 51
lea r15, [rdx + 8 * rdx]
lea r13, [rdx + 2 * r15]
and r10, r14
lea r10, [ r10 + r13 ]
mov r15, r10
shr r15, 51
lea r15, [ r15 + rcx ]
mov rcx, r15
and rcx, r14
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x8 ], rcx
shr r15, 51
and r10, r14
lea r15, [ r15 + rax ]
mov [ rbx + 0x0 ], r10
and rdi, r14
and rbp, r14
mov [ rbx + 0x20 ], rbp
mov [ rbx + 0x10 ], r15
mov [ rbx + 0x18 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.1354
; seed 0105115139864027 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3324 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=266, initial num_batches=31): 340 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1022864019253911
; number reverted permutation / tried permutation: 413 / 519 =79.576%
; number reverted decision / tried decision: 330 / 480 =68.750%
; validated in 0.21s
