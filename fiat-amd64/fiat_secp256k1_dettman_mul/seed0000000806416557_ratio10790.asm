SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r13
mulx r13, r14, [ rsi + 0x20 ]
xor rdx, rdx
adox r15, r10
adox r11, rdi
mov r10, 0xfffffffffffff 
mov rdi, r14
and rdi, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x38 ], rbx
mulx rbx, r10, [ rsi + 0x8 ]
shrd r14, r13, 52
xor rdx, rdx
adox r15, r10
adox rbx, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, r13, [ rax + 0x8 ]
adcx rcx, r13
adcx r11, r8
mov rdx, [ rax + 0x18 ]
mulx r10, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r14
mulx r14, r13, [ rax + 0x8 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x28 ], r14
mov [ rsp - 0x20 ], r13
mulx r13, r14, rdi
test al, al
adox r15, r8
adox r10, rbx
adcx r14, r15
adcx r10, r13
mov rdi, r14
shrd rdi, r10, 52
mov rdx, [ rax + 0x10 ]
mulx r8, rbx, [ rsi + 0x18 ]
xor rdx, rdx
adox rcx, rbp
adox r12, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx r15, r13, [ rax + 0x18 ]
adcx rcx, r13
adcx r15, r12
xor rdx, rdx
adox rcx, rbp
adox r11, r15
adcx r9, rbx
adcx r8, [ rsp - 0x38 ]
xor r10, r10
adox rdi, rcx
adox r11, r10
mov rdx, 0x1000003d10 
mulx r12, rbx, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
add rbx, rdi
adcx r11, r12
mov rdx, [ rax + 0x20 ]
mulx r13, rbp, [ rsi + 0x8 ]
mov rdx, 0x34 
bzhi r15, rbx, rdx
mov rcx, r15
shr rcx, 48
shrd rbx, r11, 52
test al, al
adox r9, rbp
adox r13, r8
mov rdi, 0xffffffffffff 
and r15, rdi
adox rbx, r9
adox r13, r10
bzhi r12, rbx, rdx
mov rdx, [ rax + 0x18 ]
mulx r11, r8, [ rsi + 0x18 ]
shl r12, 4
shrd rbx, r13, 52
mov rdx, [ rax + 0x20 ]
mulx r9, rbp, [ rsi + 0x10 ]
lea r12, [ r12 + rcx ]
mov rdx, [ rax + 0x10 ]
mulx r13, rcx, [ rsi + 0x20 ]
xor rdx, rdx
adox rcx, r8
adox r11, r13
adcx rcx, rbp
adcx r9, r11
add rbx, rcx
adc r9, 0x0
mov r10, rbx
shrd r10, r9, 52
mov r8, 0xfffffffffffff 
and rbx, r8
mov rdx, [ rsi + 0x18 ]
mulx r13, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rdi, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x18 ], r15
mulx r15, r8, [ rax + 0x18 ]
adox r8, rbp
adox r13, r15
adcx r10, r8
adc r13, 0x0
mov rdx, r10
shrd rdx, r13, 52
mov rbp, rdx
mov rdx, [ rsi + 0x0 ]
mulx r8, r15, [ rax + 0x8 ]
mov rdx, 0x1000003d1 
mov [ rsp - 0x10 ], rbp
mulx rbp, r13, r12
xor r12, r12
adox r13, r9
adox rdi, rbp
adcx r11, r15
adcx r8, rcx
mov rcx, 0xfffffffffffff 
mov r9, r13
and r9, rcx
shrd r13, rdi, 52
xor r15, r15
adox r13, r11
adox r8, r15
mov r12, 0x1000003d10 
mov rdx, r12
mulx rbp, r12, rbx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], r9
adcx r12, r13
adcx r8, rbp
mov rdi, r12
shrd rdi, r8, 52
and r12, rcx
mov rdx, [ rsi + 0x10 ]
mulx r9, r11, [ rax + 0x0 ]
and r10, rcx
mov [ rbx + 0x8 ], r12
mov rdx, 0x1000003d10 
mulx rbp, r13, r10
adox r11, [ rsp - 0x20 ]
adox r9, [ rsp - 0x28 ]
mov rdx, [ rax + 0x10 ]
mulx r12, r8, [ rsi + 0x0 ]
adcx r11, r8
adcx r12, r9
xor rdx, rdx
adox rdi, r11
adox r12, rdx
adcx r13, rdi
adcx r12, rbp
mov r15, r13
shrd r15, r12, 52
and r13, rcx
mov [ rbx + 0x10 ], r13
mov r10, 0x1000003d10 
mov rdx, [ rsp - 0x10 ]
mulx r9, rbp, r10
and r14, rcx
lea r14, [ r14 + r15 ]
adox rbp, r14
mov rdx, 0x0 
adox r9, rdx
mov r8, rbp
shrd r8, r9, 52
add r8, [ rsp - 0x18 ]
and rbp, rcx
mov [ rbx + 0x20 ], r8
mov [ rbx + 0x18 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.0790
; seed 1500674875758632 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1971736 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=332, initial num_batches=31): 163633 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08298930485622821
; number reverted permutation / tried permutation: 71715 / 89887 =79.784%
; number reverted decision / tried decision: 52980 / 90112 =58.794%
; validated in 0.715s
