SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x20 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x0 ]
lea r9, [rdx + rdx]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x80 ], rbx
mov rbx, rax
and rbx, rdx
mov rdx, r9
mov [ rsp - 0x78 ], rbp
mulx rbp, r9, [ rsi + 0x20 ]
mov [ rsp - 0x70 ], r12
mov r12, 0x1000003d10 
xchg rdx, rbx
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r12
shrd rax, r11, 52
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, r11, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r12, r10
xor rdx, rdx
adox r12, r11
adox r15, rdi
adcx r13, r12
adcx r15, r14
mov rdx, [ rsi + 0x10 ]
mulx r11, r14, rbx
mov rdx, [ rsi + 0x8 ]
mulx r12, rdi, rdx
add rdi, r14
adcx r11, r12
mov rdx, r10
mulx r14, r10, [ rsi + 0x18 ]
xor r12, r12
adox rcx, r10
adox r14, r8
mov r8, 0x1 
shlx r10, [ rsi + 0x10 ], r8
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r11
mulx r11, r8, r10
adcx rcx, r9
adcx rbp, r14
mov rdx, 0xfffffffffffff 
mov r9, r13
and r9, rdx
mov r14, 0x1000003d10 
mov rdx, rax
mov [ rsp - 0x40 ], r9
mulx r9, rax, r14
shrd r13, r15, 52
add r13, rcx
adc rbp, 0x0
test al, al
adox rax, r13
adox rbp, r9
mov rdx, rax
shrd rdx, rbp, 52
xchg rdx, r12
mulx rcx, r15, [ rsi + 0x20 ]
xor rdx, rdx
adox r8, r15
adox rcx, r11
adcx r12, r8
adc rcx, 0x0
mov r11, 0xfffffffffffff 
mov r9, r12
and r9, r11
shrd r12, rcx, 52
and rax, r11
mov r13, rax
shr r13, 48
shl r9, 4
mov rdx, [ rsi + 0x18 ]
mulx r15, rbp, rdx
mov rdx, 0xffffffffffff 
and rax, rdx
mov rdx, r10
mulx r8, r10, [ rsi + 0x20 ]
adox rbp, r10
adox r8, r15
mov rdx, [ rsi + 0x18 ]
mov rcx, rdx
shl rcx, 0x1
lea r9, [ r9 + r13 ]
mov rdx, [ rsi + 0x0 ]
mulx r15, r13, rdx
mov rdx, 0x1000003d1 
mulx r14, r10, r9
xor r9, r9
adox r10, r13
adox r15, r14
mov r13, r10
shrd r13, r15, 52
test al, al
adox r12, rbp
adox r8, r9
mov rbp, r12
shrd rbp, r8, 52
and r10, r11
mov rdx, [ rsi + 0x8 ]
mulx r15, r14, rbx
adox r13, r14
adox r15, r9
and r12, r11
mov rdx, [ rsi + 0x20 ]
mulx r8, rbx, rcx
adox rbp, rbx
adox r8, r9
mov rdx, rbp
shrd rdx, r8, 52
mov rcx, 0x1000003d10 
mulx rbx, r14, rcx
mov rdx, rcx
mulx r8, rcx, r12
test al, al
adox rcx, r13
adox r15, r8
mov r13, rcx
shrd r13, r15, 52
and rbp, r11
mulx r8, r12, rbp
adox r13, rdi
mov r15, [ rsp - 0x48 ]
adox r15, r9
adcx r12, r13
adcx r15, r8
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x0 ], r10
mov r10, r12
shrd r10, r15, 52
add r10, [ rsp - 0x40 ]
add r14, r10
adc rbx, 0x0
and r12, r11
mov rbp, r14
shrd rbp, rbx, 52
and r14, r11
mov [ rdi + 0x18 ], r14
and rcx, r11
lea rax, [ rax + rbp ]
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x20 ], rax
mov [ rdi + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 0.9742
; seed 3076211693309636 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 918299 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=252, initial num_batches=31): 81168 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0883895114771986
; number reverted permutation / tried permutation: 75974 / 89835 =84.571%
; number reverted decision / tried decision: 54417 / 90164 =60.353%
; validated in 0.253s
