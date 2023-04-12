SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x20 ], 0x26
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, rax
mov rdx, 0x1 
shlx rcx, [ rsi + 0x8 ], rdx
mov rdx, rax
mulx r8, rax, [ rsi + 0x10 ]
imul r9, [ rsi + 0x20 ], 0x13
mov [ rsp - 0x80 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
lea r15, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, r13
imul rdx, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x40 ], r15
mov r15, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
lea r12, [r15 + 8 * r15]
lea rbp, [r15 + 2 * r12]
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rcx
mulx rcx, r15, rbx
mov rdx, rbp
mulx rbx, rbp, [ rsi + 0x18 ]
xor rdx, rdx
adox rbp, rax
adox r8, rbx
mov rdx, [ rsi + 0x8 ]
mulx rbx, rax, rdx
mov rdx, r9
mov [ rsp - 0x20 ], rcx
mulx rcx, r9, [ rsi + 0x20 ]
adcx r9, rdi
adcx r14, rcx
mov rdx, r12
mulx rdi, r12, [ rsi + 0x10 ]
xor rdx, rdx
adox r12, r10
adox r11, rdi
mov rdx, [ rsp - 0x28 ]
mulx rcx, r10, [ rsi + 0x0 ]
adcx r12, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x38 ]
mov rdx, r12
shrd rdx, r11, 51
xchg rdx, r13
mulx r11, rdi, [ rsi + 0x0 ]
test al, al
adox rbp, r10
adox rcx, r8
adcx r15, rax
adcx rbx, [ rsp - 0x20 ]
xor rdx, rdx
adox rbp, r13
adox rcx, rdx
mov rdx, [ rsi + 0x0 ]
mulx rax, r8, [ rsp - 0x40 ]
adcx r15, rdi
adcx r11, rbx
mov rdx, rbp
shrd rdx, rcx, 51
xor r10, r10
adox r9, r8
adox rax, r14
adcx r15, rdx
adc r11, 0x0
mov r14, r15
shrd r14, r11, 51
mov r13, 0x7ffffffffffff 
and r12, r13
adox r9, r14
adox rax, r10
mov rdi, r9
and rdi, r13
shrd r9, rax, 51
mov rdx, [ rsi + 0x8 ]
mulx rcx, rbx, [ rsp - 0x40 ]
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], rdi
mov r8, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r11, rdx
xor rdx, rdx
adox r11, rbx
adox rcx, r14
mov rdx, [ rsp - 0x48 ]
mulx rax, r10, [ rsi + 0x0 ]
adcx r11, r10
adcx rax, rcx
test al, al
adox r11, r9
mov rdx, 0x0 
adox rax, rdx
mov rdi, r11
and rdi, r13
shrd r11, rax, 51
mov [ r8 + 0x20 ], rdi
imul r9, r11, 0x13
lea r12, [ r12 + r9 ]
mov rbx, r12
shr rbx, 51
and rbp, r13
lea rbx, [ rbx + rbp ]
and r15, r13
mov r14, rbx
shr r14, 51
lea r14, [ r14 + r15 ]
mov [ r8 + 0x10 ], r14
and r12, r13
mov [ r8 + 0x0 ], r12
and rbx, r13
mov [ r8 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1720
; seed 3013443975160299 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4543 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=309, initial num_batches=31): 425 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09355051727933084
; number reverted permutation / tried permutation: 398 / 500 =79.600%
; number reverted decision / tried decision: 329 / 499 =65.932%
; validated in 0.257s
