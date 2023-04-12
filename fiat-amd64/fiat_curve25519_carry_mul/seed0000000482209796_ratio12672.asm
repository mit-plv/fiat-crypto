SECTION .text
	GLOBAL fiat_curve25519_carry_mul
fiat_curve25519_carry_mul:
mov rax, [ rdx + 0x20 ]
lea r10, [rax + 8 * rax]
lea r11, [rax + 2 * r10]
imul rax, [ rdx + 0x10 ], 0x13
imul r10, [ rdx + 0x8 ], 0x13
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, rax
imul rdx, [ rcx + 0x18 ], 0x13
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x20 ]
mov [ rsp - 0x60 ], r14
xor r14, r14
adox r8, rbx
adox rbp, r9
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r14, r11
mov rdx, r10
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, [ rsi + 0x20 ]
adcx r12, r14
adcx r15, r13
mov rdx, rax
mulx r13, rax, [ rsi + 0x18 ]
xor rdx, rdx
adox r10, rax
adox r13, rdi
adcx r10, r9
adcx rbx, r13
mov rdx, r11
mulx r9, r11, [ rsi + 0x10 ]
xor r14, r14
adox r8, r11
adox r9, rbp
mulx rdi, rbp, [ rsi + 0x8 ]
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r13, [ rcx + 0x0 ]
adcx r10, rbp
adcx rdi, rbx
xor rdx, rdx
adox r8, r13
adox r11, r9
mov rdx, [ rcx + 0x0 ]
mulx rbx, r14, [ rsi + 0x0 ]
adcx r10, r14
adcx rbx, rdi
mov rdx, [ rcx + 0x8 ]
mulx rbp, r9, [ rsi + 0x0 ]
mov rdx, r10
shrd rdx, rbx, 51
mov r13, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, rdi, [ rcx + 0x0 ]
xor rdx, rdx
adox r8, r9
adox rbp, r11
adcx r12, rdi
adcx r14, r15
mov rdx, [ rsi + 0x8 ]
mulx r11, r15, [ rcx + 0x8 ]
mov rdx, [ rcx + 0x10 ]
mulx r9, rbx, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r13
adox rbp, rdx
adcx r12, r15
adcx r11, r14
mov r13, r8
shrd r13, rbp, 51
mov rdx, [ rcx + 0x8 ]
mulx r14, rdi, [ rsi + 0x10 ]
xor rdx, rdx
adox r12, rbx
adox r9, r11
mov rdx, rax
mulx r15, rax, [ rsi + 0x20 ]
adcx r12, r13
adc r9, 0x0
mov rdx, [ rcx + 0x0 ]
mulx rbp, rbx, [ rsi + 0x18 ]
test al, al
adox rax, rbx
adox rbp, r15
mov rdx, [ rcx + 0x10 ]
mulx r13, r11, [ rsi + 0x8 ]
mov rdx, [ rcx + 0x0 ]
mulx rbx, r15, [ rsi + 0x20 ]
adcx rax, rdi
adcx r14, rbp
xor rdx, rdx
adox rax, r11
adox r13, r14
mov rdx, [ rcx + 0x18 ]
mulx rbp, rdi, [ rsi + 0x0 ]
mov rdx, r12
shrd rdx, r9, 51
xor r9, r9
adox rax, rdi
adox rbp, r13
adcx rax, rdx
adc rbp, 0x0
mov rdx, [ rcx + 0x8 ]
mulx r14, r11, [ rsi + 0x18 ]
mov rdx, 0x7ffffffffffff 
mov r13, rax
and r13, rdx
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], r13
shrd rax, rbp, 51
mov rdx, [ rsi + 0x8 ]
mulx r13, rbp, [ rcx + 0x18 ]
add r15, r11
adcx r14, rbx
mov rdx, [ rcx + 0x10 ]
mulx r11, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r15, rbx
adox r11, r14
adcx r15, rbp
adcx r13, r11
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rcx + 0x20 ]
mov rdx, 0x7ffffffffffff 
and r10, rdx
adox r15, r9
adox rbp, r13
adcx r15, rax
adc rbp, 0x0
mov rax, r15
shrd rax, rbp, 51
imul r14, rax, 0x13
lea r10, [ r10 + r14 ]
mov rbx, r10
and rbx, rdx
shr r10, 51
and r8, rdx
mov [ rdi + 0x0 ], rbx
lea r10, [ r10 + r8 ]
mov r11, r10
shr r11, 51
and r10, rdx
and r12, rdx
lea r11, [ r11 + r12 ]
mov [ rdi + 0x10 ], r11
mov [ rdi + 0x8 ], r10
and r15, rdx
mov [ rdi + 0x20 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.2672
; seed 2736530094548435 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 714379 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=404, initial num_batches=31): 79717 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11158922644702601
; number reverted permutation / tried permutation: 74343 / 89744 =82.839%
; number reverted decision / tried decision: 61427 / 90255 =68.059%
; validated in 0.252s
