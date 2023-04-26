SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x18 ]
lea r8, [rdx + 8 * rdx]
lea r9, [rdx + 2 * r8]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, [ rax + 0x8 ]
imul rdx, [ rax + 0x20 ], 0x13
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x20 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r14
mulx r14, rdi, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], rdi
mulx rdi, r14, [ rsi + 0x18 ]
mov rdx, r9
mov [ rsp - 0x30 ], r13
mulx r13, r9, [ rsi + 0x18 ]
test al, al
adox rbp, r14
adox rdi, r12
mov r12, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x28 ], rdi
mulx rdi, r14, r11
adcx r14, r9
adcx r13, rdi
imul rdx, [ rax + 0x8 ], 0x13
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, rdi, r11
add r10, r8
adcx rbx, rcx
mov rdx, [ rsi + 0x20 ]
mulx rcx, r11, r9
add r11, rdi
adcx rbp, rcx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, r12
add r11, r8
adcx r9, rbp
add r11, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x48 ]
mov rdx, [ rax + 0x0 ]
mulx rcx, rdi, [ rsi + 0x0 ]
add r11, rdi
adcx rcx, r9
mov rdx, 0x7ffffffffffff 
mov rbp, r11
and rbp, rdx
mov rdx, r15
mulx r8, r15, [ rsi + 0x10 ]
mov r9, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x18 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
shrd r11, rcx, 51
xor rdx, rdx
adox r14, r15
adox r8, r13
adcx r14, rdi
adcx rbp, r8
mov rdx, r9
mulx r13, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mulx r15, rcx, r12
mov rdx, [ rax + 0x8 ]
mulx rdi, r12, [ rsi + 0x0 ]
test al, al
adox r14, r12
adox rdi, rbp
adcx r14, r11
adc rdi, 0x0
mov rdx, [ rax + 0x8 ]
mulx r8, r11, [ rsi + 0x8 ]
mov rdx, 0x33 
bzhi rbp, r14, rdx
adox rcx, r9
adox r13, r15
mov rdx, [ rax + 0x0 ]
mulx r15, r9, [ rsi + 0x10 ]
xor rdx, rdx
adox rcx, r9
adox r15, r13
adcx rcx, r11
adcx r8, r15
shrd r14, rdi, 51
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rax + 0x8 ]
mov rdx, r12
add rdx, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
add rdx, [ rsp - 0x38 ]
adcx rdi, [ rsp - 0x40 ]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r13, [ rax + 0x10 ]
xor rdx, rdx
adox rcx, r13
adox r9, r8
adcx rcx, r14
adc r9, 0x0
mov r15, 0x33 
bzhi r8, rcx, r15
shrd rcx, r9, 51
mov rdx, [ rsi + 0x10 ]
mulx r12, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r9, r13, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r13
adox r9, rdi
adcx r10, r14
adcx r12, rbx
mov rdx, [ rsi + 0x8 ]
mulx rdi, rbx, [ rax + 0x18 ]
add r11, rcx
adc r9, 0x0
bzhi rdx, r11, r15
shrd r11, r9, 51
mov rcx, rdx
mov rdx, [ rax + 0x20 ]
mulx r13, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r10, rbx
adox rdi, r12
adcx r10, r14
adcx r13, rdi
xor r12, r12
adox r10, r11
adox r13, r12
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], rcx
mov rbx, r10
shrd rbx, r13, 51
imul r9, rbx, 0x13
bzhi rcx, r10, r15
add r9, [ rsp - 0x18 ]
bzhi r11, r9, r15
mov [ rdx + 0x0 ], r11
shr r9, 51
lea r9, [ r9 + rbp ]
mov rbp, r9
shr rbp, 51
lea rbp, [ rbp + r8 ]
bzhi r8, r9, r15
mov [ rdx + 0x8 ], r8
mov [ rdx + 0x20 ], rcx
mov [ rdx + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.2404
; seed 1158549928672760 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1853863 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=157, initial num_batches=31): 128785 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06946845586755872
; number reverted permutation / tried permutation: 72654 / 90198 =80.549%
; number reverted decision / tried decision: 57347 / 89801 =63.860%
; validated in 0.581s
