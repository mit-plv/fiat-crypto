SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, [ rsi + 0x0 ]
mov r10, rax
shl r10, 0x1
mov rdx, [ rsi + 0x18 ]
mulx r11, rax, rdx
mov rdx, 0x1 
shlx rcx, [ rsi + 0x18 ], rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
lea r12, [rdx + rdx]
mov rdx, r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x20 ]
xor rdx, rdx
adox rax, r14
adox r15, r11
mov rdx, [ rsi + 0x20 ]
mulx r14, r11, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x50 ], rdi
lea rdi, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rbx
mulx rbx, rbp, rcx
mov rdx, 0xfffffffffffff 
mov rcx, r11
and rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], rbx
mov [ rsp - 0x30 ], rbp
mulx rbp, rbx, rdi
mov rdx, 0x1000003d10 
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rax
mulx rax, r15, rcx
adox rbx, r8
adox r9, rbp
mov rdx, rdi
mulx r8, rdi, [ rsi + 0x20 ]
adcx r12, rdi
adcx r8, r13
shrd r11, r14, 52
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, 0x1000003d10 
mulx rbp, rcx, r11
xor rdi, rdi
adox r15, rbx
adox r9, rax
mov rdx, [ rsi + 0x10 ]
mulx rbx, rax, rdx
mov rdx, r10
mulx r11, r10, [ rsi + 0x20 ]
adcx rax, r13
adcx r14, rbx
mov r13, r15
shrd r13, r9, 52
xor r9, r9
adox rax, r10
adox r11, r14
adcx r13, rax
adc r11, 0x0
xor rdi, rdi
adox rcx, r13
adox r11, rbp
mov r9, rcx
shrd r9, r11, 52
mov rbp, 0xfffffffffffff 
and r15, rbp
and rcx, rbp
adox r9, r12
adox r8, rdi
mov r12, rcx
shr r12, 48
mov rbx, 0xffffffffffff 
and rcx, rbx
mov r10, r9
and r10, rbp
shl r10, 4
lea r10, [ r10 + r12 ]
mulx rax, r14, [ rsi + 0x10 ]
shrd r9, r8, 52
add r9, [ rsp - 0x20 ]
mov rdx, [ rsp - 0x28 ]
adc rdx, 0x0
mov r13, r9
and r13, rbp
shrd r9, rdx, 52
mov rdx, [ rsi + 0x8 ]
mulx r8, r11, rdx
xor rdx, rdx
adox r9, [ rsp - 0x30 ]
mov rdi, [ rsp - 0x38 ]
adox rdi, rdx
mov r12, r9
shrd r12, rdi, 52
test al, al
adox r11, r14
adox rax, r8
mov r14, 0x1000003d10 
mov rdx, r12
mulx r8, r12, r14
mov rdx, [ rsi + 0x0 ]
mulx rbx, rdi, rdx
mov rdx, 0x1000003d1 
mulx rbp, r14, r10
adcx r14, rdi
adcx rbx, rbp
mov r10, r14
shrd r10, rbx, 52
test al, al
adox r10, [ rsp - 0x40 ]
mov rdi, [ rsp - 0x48 ]
mov rbp, 0x0 
adox rdi, rbp
mov rbx, 0x1000003d10 
mov rdx, r13
mulx rbp, r13, rbx
adcx r13, r10
adcx rdi, rbp
mov rdx, 0x34 
bzhi r10, r13, rdx
shrd r13, rdi, 52
bzhi rbp, r14, rdx
bzhi r14, r9, rdx
adox r13, r11
mov r9, 0x0 
adox rax, r9
mov rdx, rbx
mulx r11, rbx, r14
xor rdi, rdi
adox rbx, r13
adox rax, r11
mov r9, rbx
shrd r9, rax, 52
lea r15, [ r15 + r9 ]
test al, al
adox r12, r15
adox r8, rdi
mov r14, r12
shrd r14, r8, 52
lea rcx, [ rcx + r14 ]
mov r13, 0xfffffffffffff 
and rbx, r13
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x10 ], rbx
and r12, r13
mov [ r11 + 0x18 ], r12
mov [ r11 + 0x0 ], rbp
mov [ r11 + 0x8 ], r10
mov [ r11 + 0x20 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 0.9805
; seed 4165422984695448 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5971 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=270, initial num_batches=31): 504 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08440797186400938
; number reverted permutation / tried permutation: 413 / 500 =82.600%
; number reverted decision / tried decision: 314 / 499 =62.926%
; validated in 0.271s
