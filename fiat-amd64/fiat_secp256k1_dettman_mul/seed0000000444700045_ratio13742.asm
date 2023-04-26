SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rdx + 0x0 ]
mulx r11, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
xor rdx, rdx
adox rcx, r9
adox rbx, r8
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rax + 0x10 ]
adcx rcx, r8
adcx r9, rbx
mov rdx, [ rsi + 0x0 ]
mulx r8, rbx, [ rax + 0x18 ]
test al, al
adox rcx, rbx
adox r8, r9
mov rdx, [ rsi + 0x20 ]
mulx rbx, r9, [ rax + 0x20 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x78 ], rbp
mov rbp, r9
and rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
adox r14, rcx
adox r8, r15
adcx r10, r12
adcx r13, r11
mov rdx, [ rax + 0x10 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, r14
shrd rdx, r8, 52
xor rbp, rbp
adox r10, r11
adox rcx, r13
mov r12, rdx
mov rdx, [ rax + 0x18 ]
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x20 ]
mulx r11, r13, [ rsi + 0x0 ]
adcx r10, r15
adcx r8, rcx
xor rdx, rdx
adox r10, r13
adox r11, r8
shrd r9, rbx, 52
xor rbp, rbp
adox r12, r10
adox r11, rbp
mov rdx, 0x1000003d10 
mulx rcx, rbx, r9
mov rdx, [ rax + 0x8 ]
mulx r13, r15, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mulx r10, r8, [ rax + 0x10 ]
adcx rbx, r12
adcx r11, rcx
mov rdx, 0xfffffffffffff 
mov r9, rbx
and r9, rdx
adox r15, r8
adox r10, r13
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, [ rax + 0x18 ]
adcx r15, r12
adcx rcx, r10
mov rdx, [ rax + 0x20 ]
mulx r8, r13, [ rsi + 0x8 ]
add r15, r13
adcx r8, rcx
mov rdx, 0xffffffffffff 
mov r10, r9
and r10, rdx
shrd rbx, r11, 52
mov rdx, [ rsi + 0x20 ]
mulx r12, r11, [ rax + 0x10 ]
xor rdx, rdx
adox rbx, r15
adox r8, rdx
mov rbp, 0xfffffffffffff 
mov rcx, rbx
and rcx, rbp
shl rcx, 4
shrd rbx, r8, 52
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, [ rax + 0x18 ]
test al, al
adox r11, r13
adox r15, r12
mov rdx, [ rsi + 0x10 ]
mulx r8, r12, [ rax + 0x20 ]
adcx r11, r12
adcx r8, r15
xor rdx, rdx
adox rbx, r11
adox r8, rdx
shr r9, 48
mov r13, rbx
shrd r13, r8, 52
lea rcx, [ rcx + r9 ]
mov rdx, [ rax + 0x0 ]
mulx r12, r15, [ rsi + 0x0 ]
mov rdx, 0x1000003d1 
mulx r8, r11, rcx
xor r9, r9
adox r11, r15
adox r12, r8
mov rcx, r11
shrd rcx, r12, 52
and r11, rbp
mov rdx, [ rsi + 0x10 ]
mulx r8, r15, [ rax + 0x0 ]
mov [ rdi + 0x0 ], r11
mov rdx, [ rsi + 0x18 ]
mulx r11, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx rbp, r9, [ rax + 0x18 ]
adox r9, r12
adox r11, rbp
mov rdx, [ rax + 0x8 ]
mulx rbp, r12, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r10
mulx r10, rdi, [ rsi + 0x8 ]
adcx r13, r9
adc r11, 0x0
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r11
mulx r11, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r9
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r10, [ rax + 0x10 ]
adcx r15, r12
adcx rbp, r8
xor rdx, rdx
adox r15, r10
adox r9, rbp
mov r8, 0xfffffffffffff 
and rbx, r8
adox rcx, rdi
adox r11, rdx
mov r12, 0x1000003d10 
mov rdx, r12
mulx rdi, r12, rbx
adcx r12, rcx
adcx r11, rdi
mov r10, r12
shrd r10, r11, 52
and r12, r8
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r12
mov rbx, r13
and rbx, r8
mulx rdi, rcx, rbx
adox r10, r15
mov r11, 0x0 
adox r9, r11
adcx rcx, r10
adcx r9, rdi
mov r15, rcx
and r15, r8
mov [ rbp + 0x10 ], r15
shrd rcx, r9, 52
and r14, r8
mov r12, [ rsp - 0x40 ]
shrd r13, r12, 52
lea r14, [ r14 + rcx ]
mulx rbx, r12, r13
add r12, r14
adc rbx, 0x0
mov rdi, r12
shrd rdi, rbx, 52
add rdi, [ rsp - 0x48 ]
and r12, r8
mov [ rbp + 0x18 ], r12
mov [ rbp + 0x20 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.3742
; seed 3816970892045614 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 829187 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=307, initial num_batches=31): 79827 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09627140801773303
; number reverted permutation / tried permutation: 72820 / 90532 =80.436%
; number reverted decision / tried decision: 52762 / 89467 =58.974%
; validated in 0.248s
