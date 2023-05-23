SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x8 ]
test al, al
adox rbp, r13
adox r14, r12
adcx rcx, r9
adcx rbx, r8
mov rdx, [ rax + 0x10 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mulx r13, r12, [ rax + 0x20 ]
test al, al
adox rbp, r10
adox r11, r14
mov rdx, [ rax + 0x18 ]
mulx r14, r10, [ rsi + 0x0 ]
adcx rbp, r10
adcx r14, r11
mov rdx, 0xfffffffffffff 
mov r11, r12
and r11, rdx
mov r10, 0x1000003d10 
mov rdx, r10
mov [ rsp - 0x58 ], r15
mulx r15, r10, r11
adox r10, rbp
adox r14, r15
mov rbp, r10
shrd rbp, r14, 52
mov rdx, [ rsi + 0x8 ]
mulx r15, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r14, [ rsi + 0x0 ]
shrd r12, r13, 52
test al, al
adox rcx, r8
adox r9, rbx
adcx rcx, r11
adcx r15, r9
xor rdx, rdx
adox rcx, r14
adox rdi, r15
adcx rbp, rcx
adc rdi, 0x0
mov rbx, 0x1000003d10 
mov rdx, rbx
mulx r8, rbx, r12
xor r13, r13
adox rbx, rbp
adox rdi, r8
mov r11, 0xfffffffffffff 
mov r14, rbx
and r14, r11
shrd rbx, rdi, 52
mov r12, r14
shr r12, 48
mov rdx, [ rax + 0x8 ]
mulx r15, r9, [ rsi + 0x20 ]
mov rdx, [ rax + 0x10 ]
mulx rbp, rcx, [ rsi + 0x18 ]
add r9, rcx
adcx rbp, r15
mov rdx, [ rax + 0x18 ]
mulx rdi, r8, [ rsi + 0x10 ]
xor rdx, rdx
adox r9, r8
adox rdi, rbp
mov rdx, [ rax + 0x20 ]
mulx r15, r13, [ rsi + 0x8 ]
adcx r9, r13
adcx r15, rdi
add rbx, r9
adc r15, 0x0
mov rdx, rbx
shrd rdx, r15, 52
mov rcx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x20 ]
mulx r13, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mulx r15, r9, [ rsi + 0x18 ]
and rbx, r11
shl rbx, 4
lea rbx, [ rbx + r12 ]
mov rdx, [ rsi + 0x0 ]
mulx r11, r12, [ rax + 0x0 ]
mov rdx, 0xffffffffffff 
and r14, rdx
adox rbp, r9
adox r15, r8
mov r8, 0x1000003d1 
mov rdx, r8
mulx r9, r8, rbx
adcx r8, r12
adcx r11, r9
mov rdx, [ rsi + 0x20 ]
mulx r12, rbx, [ rax + 0x18 ]
mov rdx, r8
shrd rdx, r11, 52
test al, al
adox rbp, rdi
adox r13, r15
mov rdi, rdx
mov rdx, [ rax + 0x20 ]
mulx r9, r15, [ rsi + 0x18 ]
adcx rcx, rbp
adc r13, 0x0
mov rdx, 0xfffffffffffff 
mov r11, rcx
and r11, rdx
adox rbx, r15
adox r9, r12
mov rdx, [ rax + 0x10 ]
mulx rbp, r12, [ rsi + 0x0 ]
shrd rcx, r13, 52
xor rdx, rdx
adox rcx, rbx
adox r9, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r15, [ rax + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r14
mulx r14, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r12
mulx r12, rbp, [ rax + 0x8 ]
adcx r15, rbp
adcx r12, r13
mov rdx, [ rax + 0x8 ]
mulx rbp, r13, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, r13
adox rbp, r14
adcx rdi, r15
adc r12, 0x0
mov r14, 0x1000003d10 
mov rdx, r14
mulx r15, r14, r11
xor r11, r11
adox r14, rdi
adox r12, r15
mov r13, 0xfffffffffffff 
mov rdi, r14
and rdi, r13
shrd r14, r12, 52
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x8 ], rdi
mov r12, rcx
and r12, r13
adox rbx, [ rsp - 0x38 ]
adox rbp, [ rsp - 0x40 ]
adcx r14, rbx
adc rbp, 0x0
and r10, r13
mulx rbx, rdi, r12
adox rdi, r14
adox rbp, rbx
mov r12, rdi
shrd r12, rbp, 52
shrd rcx, r9, 52
lea r10, [ r10 + r12 ]
and rdi, r13
mulx r14, r9, rcx
mov [ r15 + 0x10 ], rdi
adox r9, r10
adox r14, r11
mov rbx, r9
and rbx, r13
and r8, r13
shrd r9, r14, 52
mov [ r15 + 0x18 ], rbx
add r9, [ rsp - 0x48 ]
mov [ r15 + 0x20 ], r9
mov [ r15 + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3511
; seed 2953724408234328 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 814057 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=307, initial num_batches=31): 80371 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09872895878298449
; number reverted permutation / tried permutation: 72174 / 89915 =80.269%
; number reverted decision / tried decision: 52844 / 90084 =58.661%
; validated in 0.25s
