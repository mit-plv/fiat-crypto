SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 152
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x10 ]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r8
mov [ rsp - 0x40 ], rcx
mulx rcx, r8, [ rax + 0x20 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], rdi
mov [ rsp - 0x30 ], r15
mulx r15, rdi, [ rsi + 0x18 ]
mov rdx, r8
shrd rdx, rcx, 52
mov rcx, 0x1000003d10 
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rdi
mulx rdi, r15, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rcx, [ rax + 0x8 ]
add r9, rcx
adcx rdi, rbx
mov rdx, [ rsi + 0x0 ]
mulx rcx, rbx, [ rax + 0x8 ]
xor rdx, rdx
adox r9, r10
adox r11, rdi
mov r10, 0xfffffffffffff 
and r8, r10
mov rdi, 0x1000003d10 
mov rdx, rdi
mulx r10, rdi, r8
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x10 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], rbx
mov [ rsp + 0x0 ], r15
mulx r15, rbx, [ rax + 0x18 ]
adox r8, rbp
adox r12, rcx
adcx r9, rbx
adcx r15, r11
add rdi, r9
adcx r15, r10
mov rdx, [ rsi + 0x0 ]
mulx r11, rbp, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r9, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, rbx
adox r9, r12
adcx r8, r10
adcx rcx, r9
add r8, rbp
adcx r11, rcx
mov r12, rdi
shrd r12, r15, 52
xor r15, r15
adox r12, r8
adox r11, r15
mov rdx, [ rax + 0x8 ]
mulx r10, rbp, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x20 ]
mulx r9, rbx, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x8 ], r9
mulx r9, r15, [ rsi + 0x8 ]
adcx rbp, r13
adcx r14, r10
mov rdx, r12
xor r13, r13
adox rdx, [ rsp + 0x0 ]
adox r11, [ rsp - 0x18 ]
adcx rbp, rcx
adcx r8, r14
mov r12, 0x34 
bzhi r10, rdx, r12
mov rcx, 0x30 
bzhi r14, r10, rcx
shrd rdx, r11, 52
xor r11, r11
adox rbp, r15
adox r9, r8
adcx rdx, rbp
adc r9, 0x0
bzhi r13, rdx, r12
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r8, [ rax + 0x0 ]
shrd r15, r9, 52
shl r13, 4
shr r10, 48
lea r13, [ r13 + r10 ]
mov rdx, 0x1000003d1 
mulx r10, r9, r13
xor r13, r13
adox r9, r8
adox rbp, r10
mov rdx, [ rsi + 0x10 ]
mulx r8, r11, [ rax + 0x20 ]
mov rdx, [ rsp - 0x30 ]
adcx rdx, [ rsp - 0x20 ]
mov r10, [ rsp - 0x38 ]
adcx r10, [ rsp - 0x28 ]
mov r13, r9
shrd r13, rbp, 52
xor rbp, rbp
adox rdx, r11
adox r8, r10
adcx r15, rdx
adc r8, 0x0
bzhi r11, r15, r12
shrd r15, r8, 52
mov rdx, [ rsi + 0x8 ]
mulx r8, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, [ rax + 0x20 ]
test al, al
adox rbx, rbp
adox rcx, [ rsp + 0x8 ]
adcx r15, rbx
adc rcx, 0x0
mov rdx, [ rax + 0x0 ]
mulx rbx, rbp, [ rsi + 0x10 ]
bzhi rdx, r15, r12
shrd r15, rcx, 52
xor rcx, rcx
adox r10, [ rsp - 0x8 ]
adox r8, [ rsp - 0x10 ]
mov rcx, 0x1000003d10 
xchg rdx, rcx
mov [ rsp + 0x10 ], r14
mulx r14, r12, r11
adcx r13, r10
adc r8, 0x0
xor r11, r11
adox r12, r13
adox r8, r14
mov r10, 0x34 
bzhi r14, r12, r10
shrd r12, r8, 52
mov rdx, [ rsi + 0x8 ]
mulx r8, r13, [ rax + 0x8 ]
xor rdx, rdx
adox rbp, r13
adox r8, rbx
adcx rbp, [ rsp - 0x40 ]
adcx r8, [ rsp - 0x48 ]
xor r11, r11
adox r12, rbp
adox r8, r11
mov rdx, 0x1000003d10 
mulx r13, rbx, rcx
bzhi rcx, rdi, r10
adox rbx, r12
adox r8, r13
mov rdi, rbx
shrd rdi, r8, 52
bzhi rbp, rbx, r10
lea rcx, [ rcx + rdi ]
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], rbp
mulx rbx, r13, r15
adox r13, rcx
adox rbx, r11
mov r15, r13
shrd r15, rbx, 52
add r15, [ rsp + 0x10 ]
mov [ r12 + 0x20 ], r15
bzhi r8, r13, r10
bzhi rdi, r9, r10
mov [ r12 + 0x0 ], rdi
mov [ r12 + 0x18 ], r8
mov [ r12 + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 152
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 0.9782
; seed 2769048008053590 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 999515 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=180, initial num_batches=31): 72471 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07250616549026277
; number reverted permutation / tried permutation: 68435 / 90226 =75.848%
; number reverted decision / tried decision: 46348 / 89773 =51.628%
; validated in 0.315s
