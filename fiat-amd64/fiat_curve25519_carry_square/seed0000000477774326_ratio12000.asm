SECTION .text
	GLOBAL fiat_curve25519_carry_square
fiat_curve25519_carry_square:
mov rax, [ rsi + 0x18 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, r11
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, rdx
imul rdx, [ rsi + 0x20 ], 0x26
mov r9, [ rsi + 0x8 ]
lea r11, [r9 + r9]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov rbp, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov r12, rbp
shl r12, 0x1
imul rbp, [ rsi + 0x18 ], 0x26
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
xchg rdx, rbp
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
mov rdx, [ rsi + 0x0 ]
mulx r13, r14, r11
mov rdx, 0x33 
bzhi r11, r15, rdx
mov rdx, rbp
mov [ rsp - 0x48 ], r11
mulx r11, rbp, [ rsi + 0x10 ]
adox rax, rbp
adox r11, r10
mov r10, [ rsi + 0x18 ]
mov rdx, r10
shl rdx, 0x1
xor r10, r10
adox r9, rcx
adox r8, rbx
mulx rbx, rcx, [ rsi + 0x0 ]
shrd r15, rdi, 51
add rax, r14
adcx r13, r11
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r14, r12
add rax, r15
adc r13, 0x0
mov rdx, rax
shrd rdx, r13, 51
add r9, r14
adcx rbp, r8
test al, al
adox r9, rdx
adox rbp, r10
mov r11, 0x7ffffffffffff 
mov r8, r9
and r8, r11
mov rdx, r12
mulx r15, r12, [ rsi + 0x8 ]
imul rdx, [ rsi + 0x20 ], 0x13
mulx r13, r14, [ rsi + 0x20 ]
xor rdx, rdx
adox r14, r12
adox r15, r13
mov rdx, [ rsi + 0x10 ]
mulx r12, r10, rdx
shrd r9, rbp, 51
test al, al
adox r14, rcx
adox rbx, r15
adcx r14, r9
adc rbx, 0x0
mov rdx, r14
shrd rdx, rbx, 51
and r14, r11
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], r14
mov rbp, [ rsi + 0x20 ]
mov r13, rbp
shl r13, 0x1
mov rbp, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r15, rdi
add r10, r15
adcx r9, r12
mov rdx, r13
mulx rdi, r13, [ rsi + 0x0 ]
xor r12, r12
adox r10, r13
adox rdi, r9
adcx r10, rbp
adc rdi, 0x0
mov rbx, r10
shrd rbx, rdi, 51
imul rbp, rbx, 0x13
add rbp, [ rsp - 0x48 ]
mov r14, rbp
shr r14, 51
and r10, r11
mov [ rcx + 0x20 ], r10
and rax, r11
lea r14, [ r14 + rax ]
mov rdx, r14
and rdx, r11
mov [ rcx + 0x8 ], rdx
shr r14, 51
lea r14, [ r14 + r8 ]
mov [ rcx + 0x10 ], r14
and rbp, r11
mov [ rcx + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.2000
; seed 3659203732823612 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 717123 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=284, initial num_batches=31): 73678 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10274109183501297
; number reverted permutation / tried permutation: 74631 / 89485 =83.401%
; number reverted decision / tried decision: 60287 / 90514 =66.605%
; validated in 0.244s
