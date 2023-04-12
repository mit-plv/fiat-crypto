SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x10 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx rcx, r10, [ rsi + 0x10 ]
mov rdx, r11
mulx r8, r11, [ rsi + 0x20 ]
mov r9, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
lea rbx, [r9 + 8 * r9]
lea rbp, [r9 + 2 * rbx]
mov r9, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
lea r13, [rdx + 8 * rdx]
lea r14, [rdx + 2 * r13]
imul rdx, [ rax + 0x18 ], 0x13
mov [ rsp - 0x58 ], r15
mulx r15, r13, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r12
mulx r12, rdi, [ rsi + 0x20 ]
mov [ rsp - 0x40 ], rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x38 ], rcx
mov [ rsp - 0x30 ], r10
mulx r10, rcx, r14
mov rdx, r9
mulx r14, r9, [ rsi + 0x18 ]
xor rdx, rdx
adox rcx, r9
adox r14, r10
mov rdx, [ rsi + 0x18 ]
mulx r9, r10, rbx
adcx rcx, r13
adcx r15, r14
mov rdx, rbp
mulx rbx, rbp, [ rsi + 0x18 ]
xor r13, r13
adox rdi, rbp
adox rbx, r12
mulx r14, r12, [ rsi + 0x10 ]
adcx r11, r10
adcx r9, r8
mulx r10, r8, [ rsi + 0x8 ]
add r11, r12
adcx r14, r9
xor rbp, rbp
adox rcx, r8
adox r10, r15
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx r12, r15, [ rax + 0x0 ]
adcx rcx, r15
adcx r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r8, r9, [ rax + 0x0 ]
mov rdx, rcx
shrd rdx, r12, 51
xor r10, r10
adox r11, r9
adox r8, r14
mov rbp, rdx
mov rdx, [ rax + 0x8 ]
mulx r15, r14, [ rsi + 0x0 ]
adcx r11, r14
adcx r15, r8
test al, al
adox r11, rbp
adox r15, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r12, [ rax + 0x8 ]
mov rdx, r11
shrd rdx, r15, 51
test al, al
adox rdi, [ rsp - 0x30 ]
adox rbx, [ rsp - 0x38 ]
adcx rdi, r12
adcx r9, rbx
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mulx r14, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r15, [ rax + 0x8 ]
xor rdx, rdx
adox rdi, r8
adox r14, r9
adcx rdi, rbp
adc r14, 0x0
mov r10, 0x7ffffffffffff 
mov rbp, rdi
and rbp, r10
mov rdx, r13
mulx rbx, r13, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r8, r9, [ rsi + 0x18 ]
shrd rdi, r14, 51
xor rdx, rdx
adox r13, r9
adox r8, rbx
adcx r13, r15
adcx r12, r8
mov rdx, [ rax + 0x10 ]
mulx r14, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox r13, r15
adox r14, r12
adcx r13, [ rsp - 0x40 ]
adcx r14, [ rsp - 0x48 ]
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r13, rdi
adox r14, rdx
mov rdi, r13
shrd rdi, r14, 51
mov rdx, [ rax + 0x0 ]
mulx r14, r15, [ rsi + 0x20 ]
test al, al
adox r15, rbx
adox r9, r14
mov rdx, [ rax + 0x20 ]
mulx r14, rbx, [ rsi + 0x0 ]
adcx r15, r8
adcx r12, r9
mov rdx, [ rax + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
add r15, r8
adcx r9, r12
xor rdx, rdx
adox r15, rbx
adox r14, r9
adcx r15, rdi
adc r14, 0x0
and rcx, r10
mov rdi, r15
shrd rdi, r14, 51
imul rbx, rdi, 0x13
lea rcx, [ rcx + rbx ]
mov r12, rcx
shr r12, 51
and rcx, r10
and r15, r10
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x20 ], r15
and r11, r10
lea r12, [ r12 + r11 ]
mov r9, r12
shr r9, 51
and r12, r10
lea r9, [ r9 + rbp ]
mov [ r8 + 0x10 ], r9
and r13, r10
mov [ r8 + 0x18 ], r13
mov [ r8 + 0x8 ], r12
mov [ r8 + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2242
; seed 0896592957519821 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 704082 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=404, initial num_batches=31): 78363 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.1112981158444613
; number reverted permutation / tried permutation: 73505 / 89958 =81.710%
; number reverted decision / tried decision: 60297 / 90041 =66.966%
; validated in 0.259s
