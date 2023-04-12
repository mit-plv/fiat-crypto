SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x20 ]
mulx r11, rax, rdx
mov rdx, 0xfffffffffffff 
mov rcx, rax
and rcx, rdx
mov rdx, r10
mulx r8, r10, [ rsi + 0x10 ]
mov r9, 0x1000003d10 
xchg rdx, r9
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
lea r13, [rdx + rdx]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
adox r10, r14
adox r15, r8
adcx rbx, r10
adcx r15, rbp
mov rdx, r9
mulx r8, r9, [ rsi + 0x18 ]
xor rbp, rbp
adox rcx, r9
adox r8, r12
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mulx r10, r14, rdx
mov rdx, rbx
shrd rdx, r15, 52
mov r15, [ rsi + 0x10 ]
mov r9, r15
shl r9, 0x1
xchg rdx, r13
mulx rbp, r15, [ rsi + 0x20 ]
add rcx, r15
adcx rbp, r8
xor r8, r8
adox r13, rcx
adox rbp, r8
shrd rax, r11, 52
mov r11, 0x1000003d10 
xchg rdx, r11
mulx rcx, r15, rax
mov rax, 0x34 
bzhi r8, rbx, rax
adox r15, r13
adox rbp, rcx
mov rdx, r9
mulx rbx, r9, [ rsi + 0x18 ]
xchg rdx, r12
mulx rcx, r13, [ rsi + 0x20 ]
mov rdx, r15
shrd rdx, rbp, 52
test al, al
adox r9, r13
adox rcx, rbx
adcx rdx, r9
adc rcx, 0x0
bzhi rbp, rdx, rax
bzhi rbx, r15, rax
mov r15, rbx
shr r15, 48
shrd rdx, rcx, 52
mov r13, 0xffffffffffff 
and rbx, r13
shl rbp, 4
lea rbp, [ rbp + r15 ]
mov r9, rdx
mov rdx, [ rsi + 0x20 ]
mulx r15, rcx, r12
mov rdx, [ rsi + 0x0 ]
mulx rax, r12, rdx
mov rdx, 0x1000003d1 
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, rbp
xor rbp, rbp
adox r14, rcx
adox r15, r10
adcx r9, r14
adc r15, 0x0
xor r10, r10
adox r13, r12
adox rax, rdi
mov rbp, r9
shrd rbp, r15, 52
mov rcx, r13
shrd rcx, rax, 52
mov r12, 0xfffffffffffff 
and r9, r12
mov rdx, [ rsi + 0x8 ]
mulx r14, rdi, r11
mov rdx, 0x1000003d10 
mulx rax, r15, r9
mov r9, [ rsi + 0x18 ]
lea r10, [r9 + r9]
and r13, r12
mov rdx, [ rsi + 0x20 ]
mulx r12, r9, r10
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], r13
xchg rdx, r11
mulx r13, r10, [ rsi + 0x10 ]
adox rcx, rdi
mov rdx, 0x0 
adox r14, rdx
adcx rbp, r9
adc r12, 0x0
xor rdi, rdi
adox r15, rcx
adox r14, rax
mov rdx, 0x34 
bzhi rax, rbp, rdx
mov r9, 0x1000003d10 
mov rdx, r9
mulx rcx, r9, rax
mov rdx, [ rsi + 0x8 ]
mulx rdi, rax, rdx
adox rax, r10
adox r13, rdi
mov rdx, r15
shrd rdx, r14, 52
xor r10, r10
adox rdx, rax
adox r13, r10
adcx r9, rdx
adcx r13, rcx
mov r14, r9
shrd r14, r13, 52
lea r8, [ r8 + r14 ]
shrd rbp, r12, 52
mov r12, 0x1000003d10 
mov rdx, rbp
mulx rcx, rbp, r12
add rbp, r8
adc rcx, 0x0
mov rdi, 0xfffffffffffff 
mov rax, rbp
and rax, rdi
mov [ r11 + 0x18 ], rax
shrd rbp, rcx, 52
and r15, rdi
lea rbx, [ rbx + rbp ]
mov [ r11 + 0x8 ], r15
and r9, rdi
mov [ r11 + 0x10 ], r9
mov [ r11 + 0x20 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9261
; seed 2111706479582779 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1462543 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=161, initial num_batches=31): 112291 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07677791353826861
; number reverted permutation / tried permutation: 78830 / 90026 =87.564%
; number reverted decision / tried decision: 54022 / 89973 =60.042%
; validated in 0.342s
