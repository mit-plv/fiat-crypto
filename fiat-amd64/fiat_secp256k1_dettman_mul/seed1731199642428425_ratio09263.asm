SECTION .text
	GLOBAL fiat_secp256k1_dettman_mul
fiat_secp256k1_dettman_mul:
sub rsp, 200
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
add r13, r10
adcx r11, r14
mov rdx, [ rsi + 0x0 ]
mulx r14, r10, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x48 ], r11
mov r11, r9
and r11, rdx
adox rcx, rbp
adox r12, r8
mov rdx, [ rax + 0x18 ]
mulx rbp, r8, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], r14
mulx r14, r13, [ rsi + 0x20 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rbp
mulx rbp, r10, [ rax + 0x10 ]
mov rdx, 0x1000003d10 
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r12
mulx r12, r8, r11
adcx r13, r10
adcx rbp, r14
test al, al
adox rcx, r15
adox rdi, [ rsp - 0x18 ]
mov rdx, [ rax + 0x0 ]
mulx r11, r15, [ rsi + 0x10 ]
adcx rcx, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
shrd r9, rbx, 52
mov rdx, [ rsi + 0x20 ]
mulx r14, rbx, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x10 ], rbp
mulx rbp, r10, [ rax + 0x20 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x8 ], r13
mov [ rsp + 0x0 ], r9
mulx r9, r13, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x8 ], r11
mov [ rsp + 0x10 ], r15
mulx r15, r11, [ rsi + 0x18 ]
add rbx, r11
adcx r15, r14
mov rdx, [ rsi + 0x10 ]
mulx r11, r14, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x18 ], r9
mov [ rsp + 0x20 ], r13
mulx r13, r9, [ rsi + 0x8 ]
add rbx, r14
adcx r11, r15
add rbx, r9
adcx r13, r11
test al, al
adox rbx, r10
adox rbp, r13
mov rdx, [ rax + 0x18 ]
mulx r15, r10, [ rsi + 0x20 ]
mov rdx, [ rax + 0x20 ]
mulx r9, r14, [ rsi + 0x18 ]
adcx r10, r14
adcx r9, r15
mov rdx, [ rsi + 0x10 ]
mulx r13, r11, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mulx r14, r15, [ rsi + 0x0 ]
test al, al
adox r8, rcx
adox rdi, r12
mov rdx, [ rsp + 0x20 ]
mov r12, rdx
adcx r12, [ rsp + 0x10 ]
mov rcx, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x8 ]
test al, al
adox r12, r15
adox r14, rcx
mov rdx, r8
shrd rdx, rdi, 52
mov r15, 0x1000003d10 
xchg rdx, r15
mulx rcx, rdi, [ rsp + 0x0 ]
mov rdx, [ rax + 0x20 ]
mov [ rsp + 0x28 ], r14
mov [ rsp + 0x30 ], r12
mulx r12, r14, [ rsi + 0x10 ]
xor rdx, rdx
adox r15, rbx
adox rbp, rdx
mov rbx, r11
adcx rbx, [ rsp - 0x8 ]
adcx r13, [ rsp - 0x10 ]
xor r11, r11
adox rdi, r15
adox rbp, rcx
mov rdx, [ rax + 0x20 ]
mulx r15, rcx, [ rsi + 0x8 ]
adcx rbx, rcx
adcx r15, r13
mov rdx, 0xfffffffffffff 
mov r13, rdi
and r13, rdx
mov rdx, [ rsi + 0x18 ]
mulx r11, rcx, [ rax + 0x18 ]
shrd rdi, rbp, 52
mov rdx, r13
shr rdx, 48
mov rbp, rdx
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x38 ], r9
mov [ rsp + 0x40 ], r10
mulx r10, r9, [ rsi + 0x20 ]
test al, al
adox rdi, rbx
mov rdx, 0x0 
adox r15, rdx
mov rbx, 0xfffffffffffff 
mov rdx, rdi
and rdx, rbx
shl rdx, 4
test al, al
adox r9, rcx
adox r11, r10
adcx r9, r14
adcx r12, r11
shrd rdi, r15, 52
test al, al
adox rdi, r9
mov r14, 0x0 
adox r12, r14
mov rcx, rdi
shrd rcx, r12, 52
and rdi, rbx
mov r10, 0x1000003d10 
xchg rdx, rdi
mulx r11, r15, r10
adox rcx, [ rsp + 0x40 ]
mov r9, [ rsp + 0x38 ]
adox r9, r14
mov r12, rcx
shrd r12, r9, 52
lea rdi, [ rdi + rbp ]
mov rbp, 0x1000003d1 
mov rdx, rdi
mulx r9, rdi, rbp
add rdi, [ rsp - 0x30 ]
adcx r9, [ rsp - 0x38 ]
mov rdx, rdi
shrd rdx, r9, 52
xor r9, r9
adox rdx, [ rsp - 0x40 ]
mov r14, [ rsp - 0x48 ]
adox r14, r9
adcx r15, rdx
adcx r14, r11
mov r11, r15
shrd r11, r14, 52
and rdi, rbx
and r15, rbx
and rcx, rbx
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], rdi
adox r11, [ rsp + 0x30 ]
mov r14, [ rsp + 0x28 ]
adox r14, r9
xchg rdx, r10
mulx r9, rdi, rcx
adcx rdi, r11
adcx r14, r9
mov rcx, rdi
shrd rcx, r14, 52
mov r11, 0xffffffffffff 
and r13, r11
and r8, rbx
lea r8, [ r8 + rcx ]
and rdi, rbx
mulx r14, r9, r12
adox r9, r8
mov r12, 0x0 
adox r14, r12
mov rcx, r9
and rcx, rbx
shrd r9, r14, 52
lea r13, [ r13 + r9 ]
mov [ r10 + 0x18 ], rcx
mov [ r10 + 0x8 ], r15
mov [ r10 + 0x20 ], r13
mov [ r10 + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9263
; seed 1731199642428425 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 14749 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=121, initial num_batches=31): 766 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.05193572445589532
; number reverted permutation / tried permutation: 346 / 491 =70.468%
; number reverted decision / tried decision: 200 / 508 =39.370%
; validated in 0.595s
