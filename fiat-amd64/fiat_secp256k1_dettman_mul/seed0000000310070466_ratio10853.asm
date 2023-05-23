SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
mov rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x20 ]
mulx r8, rcx, [ rax + 0x20 ]
mov rdx, 0x34 
bzhi r9, rcx, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rax + 0x10 ]
adox rbx, r10
adox r11, rbp
mov rdx, [ rsi + 0x0 ]
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbp
mulx rbp, rdi, [ rsi + 0x8 ]
shrd rcx, r8, 52
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r10
mulx r10, r8, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], rdi
mulx rdi, rbp, [ rsi + 0x20 ]
add rbx, r14
adcx r15, r11
mov rdx, 0x1000003d10 
mulx r11, r14, r9
xor r9, r9
adox rbx, r8
adox r10, r15
adcx r14, rbx
adcx r10, r11
mov r8, r14
shrd r8, r10, 52
mov r15, 0xfffffffffffff 
and r14, r15
mov rdx, [ rsi + 0x20 ]
mulx rbx, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mulx r9, r10, [ rsi + 0x18 ]
adox r11, r10
adox r9, rbx
mov rdx, [ rax + 0x10 ]
mulx r10, rbx, [ rsi + 0x10 ]
adcx r11, rbx
adcx r10, r9
mov rdx, [ rsi + 0x8 ]
mulx rbx, r9, [ rax + 0x18 ]
xor rdx, rdx
adox r11, r9
adox rbx, r10
adcx r11, r12
adcx r13, rbx
test al, al
adox r8, r11
adox r13, rdx
mov r12, 0x1000003d10 
mov rdx, rcx
mulx r10, rcx, r12
adcx rcx, r8
adcx r13, r10
mov rdx, [ rsi + 0x10 ]
mulx rbx, r9, [ rax + 0x18 ]
mov rdx, rcx
shrd rdx, r13, 52
and rcx, r15
mov r11, rdx
mov rdx, [ rsi + 0x20 ]
mulx r10, r8, [ rax + 0x8 ]
mov rdx, 0xffffffffffff 
mov r13, rcx
and r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r12, r15, [ rax + 0x10 ]
adox r8, r15
adox r12, r10
mov rdx, [ rsi + 0x8 ]
mulx r15, r10, [ rax + 0x20 ]
shr rcx, 48
xor rdx, rdx
adox r8, r9
adox rbx, r12
adcx r8, r10
adcx r15, rbx
add r11, r8
adc r15, 0x0
mov rdx, [ rsi + 0x20 ]
mulx r12, r9, [ rax + 0x10 ]
mov rdx, 0x34 
bzhi r10, r11, rdx
mov rdx, [ rax + 0x18 ]
mulx r8, rbx, [ rsi + 0x18 ]
shl r10, 4
test al, al
adox r9, rbx
adox r8, r12
mov rdx, [ rsi + 0x10 ]
mulx rbx, r12, [ rax + 0x20 ]
adcx r9, r12
adcx rbx, r8
lea r10, [ r10 + rcx ]
shrd r11, r15, 52
add r11, r9
adc rbx, 0x0
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, [ rax + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x28 ], r13
mulx r13, r9, [ rsi + 0x0 ]
xor rdx, rdx
adox rbp, rcx
adox r15, rdi
mov rdi, r11
shrd rdi, rbx, 52
mov rbx, 0x1000003d1 
mov rdx, rbx
mulx rcx, rbx, r10
test al, al
adox r8, [ rsp - 0x30 ]
adox r12, [ rsp - 0x38 ]
adcx rdi, rbp
adc r15, 0x0
mov rdx, [ rsi + 0x0 ]
mulx rbp, r10, [ rax + 0x0 ]
xor rdx, rdx
adox rbx, r10
adox rbp, rcx
mov rcx, rbx
shrd rcx, rbp, 52
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, [ rax + 0x0 ]
mov rdx, 0x34 
mov [ rsp - 0x20 ], r14
bzhi r14, r11, rdx
adox r10, r9
adox r13, rbp
mov r11, 0x1000003d10 
mov rdx, r14
mulx r9, r14, r11
xor rbp, rbp
adox rcx, r10
adox r13, rbp
adcx r14, rcx
adcx r13, r9
mov rdx, 0x34 
bzhi r10, r14, rdx
bzhi r9, rdi, rdx
adox r8, [ rsp - 0x40 ]
adox r12, [ rsp - 0x48 ]
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r10
shrd r14, r13, 52
test al, al
adox r14, r8
adox r12, rbp
mov rdx, r9
mulx r13, r9, r11
adcx r9, r14
adcx r12, r13
shrd rdi, r15, 52
mov rdx, rdi
mulx r15, rdi, r11
mov r10, 0xfffffffffffff 
mov r8, r9
and r8, r10
mov [ rcx + 0x10 ], r8
shrd r9, r12, 52
add r9, [ rsp - 0x20 ]
xor r14, r14
adox rdi, r9
adox r15, r14
mov rbp, rdi
and rbp, r10
shrd rdi, r15, 52
add rdi, [ rsp - 0x28 ]
mov [ rcx + 0x20 ], rdi
mov [ rcx + 0x18 ], rbp
and rbx, r10
mov [ rcx + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.0853
; seed 2493674894606780 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 989516 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=175, initial num_batches=31): 72166 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07293060445712854
; number reverted permutation / tried permutation: 68356 / 89776 =76.141%
; number reverted decision / tried decision: 46455 / 90223 =51.489%
; validated in 0.309s
