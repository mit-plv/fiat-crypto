SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
imul rax, [ rsi + 0x18 ], 0x26
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, rdx
mov rdx, [ rsi + 0x20 ]
lea rcx, [rdx + 8 * rdx]
lea r8, [rdx + 2 * rcx]
mov rdx, [ rsi + 0x18 ]
lea rcx, [rdx + rdx]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rax
imul rdx, [ rsi + 0x18 ], 0x13
mov [ rsp - 0x78 ], rbp
mulx rbp, rax, [ rsi + 0x18 ]
imul rdx, [ rsi + 0x20 ], 0x26
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
test al, al
adox r9, r12
adox r13, rbx
mulx r12, rbx, [ rsi + 0x10 ]
adcx rax, rbx
adcx r12, rbp
mulx rbx, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov r14, rdx
shl r14, 0x1
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov rdi, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rcx
lea rcx, [rdi + rdi]
xor rdi, rdi
adox r9, r10
adox r11, r13
mov r10, r9
shrd r10, r11, 51
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx rdi, r11, rcx
test al, al
adox rax, r11
adox rdi, r12
adcx rax, r10
adc rdi, 0x0
mov rdx, [ rsi + 0x20 ]
lea r12, [rdx + rdx]
mov rdx, [ rsi + 0x8 ]
mulx r10, rcx, rdx
xor rdx, rdx
adox rbp, rcx
adox r10, rbx
mov rbx, rax
shrd rbx, rdi, 51
mov rdx, [ rsi + 0x0 ]
mulx rdi, r11, r13
test al, al
adox rbp, r11
adox rdi, r10
adcx rbp, rbx
adc rdi, 0x0
mov rdx, [ rsi + 0x20 ]
mulx rcx, r13, r8
test al, al
adox r13, r14
adox r15, rcx
mov rdx, [ rsp - 0x48 ]
mulx r14, r8, [ rsi + 0x0 ]
adcx r13, r8
adcx r14, r15
mulx rbx, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, r12
mulx r15, r12, [ rsi + 0x0 ]
mov rdx, rbp
shrd rdx, rdi, 51
xor rdi, rdi
adox r11, r10
adox rbx, rcx
adcx r11, r12
adcx r15, rbx
xor r8, r8
adox r13, rdx
adox r14, r8
mov rdi, 0x7ffffffffffff 
and r9, rdi
mov r10, r13
shrd r10, r14, 51
test al, al
adox r11, r10
adox r15, r8
mov rcx, r11
shrd rcx, r15, 51
imul r12, rcx, 0x13
lea r9, [ r9 + r12 ]
and r13, rdi
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r13
mov rbx, r9
shr rbx, 51
and rax, rdi
lea rbx, [ rbx + rax ]
mov r14, rbx
and r14, rdi
mov [ rdx + 0x8 ], r14
shr rbx, 51
and rbp, rdi
lea rbx, [ rbx + rbp ]
mov [ rdx + 0x10 ], rbx
and r9, rdi
mov [ rdx + 0x0 ], r9
and r11, rdi
mov [ rdx + 0x20 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.1673
; seed 2354047693504646 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 688300 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=305, initial num_batches=31): 78841 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11454453000145286
; number reverted permutation / tried permutation: 73070 / 90236 =80.977%
; number reverted decision / tried decision: 58335 / 89763 =64.988%
; validated in 0.253s
