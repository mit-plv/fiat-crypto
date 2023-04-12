SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x8 ]
lea r10, [rax + rax]
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, rdx
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rdx
mov rdx, r10
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov r12, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov r13, r12
shl r13, 0x1
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, rcx
shrd rdx, r8, 52
mov r8, 0x1000003d10 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, r8
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rax
mulx rax, r8, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], rax
mov [ rsp - 0x30 ], r8
mulx r8, rax, rdx
add r10, r14
adcx r15, rbp
mov rdx, 0x34 
bzhi rbp, rcx, rdx
mov rcx, 0x1000003d10 
mov rdx, rcx
mulx r14, rcx, rbp
mov rdx, r12
mulx rbp, r12, [ rsi + 0x18 ]
adox rcx, r10
adox r15, r14
test al, al
adox r9, r12
adox rbp, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x20 ]
mulx r14, r10, r13
adcx r9, r10
adcx r14, rbp
mov rdx, rcx
shrd rdx, r15, 52
imul r12, [ rsi + 0x10 ], 0x2
test al, al
adox rdx, r9
mov r15, 0x0 
adox r14, r15
mov rbp, rdx
mov rdx, [ rsi + 0x20 ]
mulx r9, r10, r12
adcx rdi, rbp
adcx r14, r11
mov rdx, [ rsi + 0x20 ]
mulx rbp, r11, rbx
mov rdx, r12
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, rdi
shrd rdx, r14, 52
test al, al
adox r12, r11
adox rbp, rbx
adcx rdx, r12
adc rbp, 0x0
mov r14, 0x34 
bzhi r11, rdx, r14
mov rbx, rdx
mov rdx, [ rsi + 0x0 ]
mulx r15, r12, rdx
bzhi rdx, rdi, r14
mov rdi, rdx
shr rdi, 48
shl r11, 4
lea r11, [ r11 + rdi ]
mov rdi, 0x1000003d1 
xchg rdx, r11
mov [ rsp - 0x28 ], r8
mulx r8, r14, rdi
test al, al
adox r14, r12
adox r15, r8
mov r12, 0xfffffffffffff 
mov rdx, r14
and rdx, r12
shrd r14, r15, 52
mov r8, r10
test al, al
adox r8, [ rsp - 0x40 ]
adox r9, [ rsp - 0x48 ]
adcx r14, [ rsp - 0x30 ]
mov r10, [ rsp - 0x38 ]
adc r10, 0x0
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x0 ], rdx
mov rdx, [ rsi + 0x18 ]
mov rdi, rdx
shl rdi, 0x1
shrd rbx, rbp, 52
test al, al
adox rbx, r8
mov rdx, 0x0 
adox r9, rdx
mov rbp, rbx
shrd rbp, r9, 52
mov rdx, [ rsi + 0x20 ]
mulx r9, r8, rdi
test al, al
adox rbp, r8
mov rdx, 0x0 
adox r9, rdx
mov rdx, r13
mulx rdi, r13, [ rsi + 0x10 ]
mov rdx, rbp
shrd rdx, r9, 52
and rbx, r12
adox rax, r13
adox rdi, [ rsp - 0x28 ]
mov r8, 0x1000003d10 
xchg rdx, rbx
mulx r13, r9, r8
adcx r9, r14
adcx r10, r13
mov r14, r9
shrd r14, r10, 52
and rcx, r12
and rbp, r12
mov rdx, rbp
mulx r13, rbp, r8
adox r14, rax
mov r10, 0x0 
adox rdi, r10
adcx rbp, r14
adcx rdi, r13
mov rax, rbp
shrd rax, rdi, 52
and rbp, r12
lea rcx, [ rcx + rax ]
mov [ r15 + 0x10 ], rbp
mov rdx, 0xffffffffffff 
and r11, rdx
mov rdx, rbx
mulx r13, rbx, r8
adox rbx, rcx
adox r13, r10
mov rdx, rbx
shrd rdx, r13, 52
lea r11, [ r11 + rdx ]
mov [ r15 + 0x20 ], r11
and rbx, r12
and r9, r12
mov [ r15 + 0x8 ], r9
mov [ r15 + 0x18 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0227
; seed 0457920433625596 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 715661 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=230, initial num_batches=31): 66393 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09277157760448033
; number reverted permutation / tried permutation: 75092 / 89951 =83.481%
; number reverted decision / tried decision: 61214 / 90048 =67.979%
; validated in 0.199s
