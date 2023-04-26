SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rax, 0x1 
shlx r10, [ rsi + 0x8 ], rax
shlx r11, [ rsi + 0x0 ], rax
shlx rdx, [ rsi + 0x18 ], rax
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, r10
mov rdx, [ rsi + 0x10 ]
lea rax, [rdx + rdx]
mov rdx, [ rsi + 0x20 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, 0xfffffffffffff 
mov [ rsp - 0x70 ], r12
mov r12, rbx
and r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r10
mov rdx, r11
mov [ rsp - 0x48 ], r14
mulx r14, r11, [ rsi + 0x18 ]
adox r15, r11
adox r14, rdi
mov rdi, 0x1000003d10 
xchg rdx, r12
mov [ rsp - 0x40 ], r13
mulx r13, r11, rdi
adcx r11, r15
adcx r14, r13
mov rdx, r11
shrd rdx, r14, 52
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r13, rdx
test al, al
adox r13, r8
adox r9, r14
mov rdx, r12
mulx r8, r12, [ rsi + 0x20 ]
adcx r13, r12
adcx r8, r9
test al, al
adox r15, r13
mov r14, 0x0 
adox r8, r14
shrd rbx, rbp, 52
xchg rdx, rdi
mulx r9, rbp, rbx
add rbp, r15
adcx r8, r9
mov r12, rbp
shrd r12, r8, 52
mov rdx, [ rsi + 0x18 ]
mulx r15, r13, rax
mov rdx, [ rsi + 0x20 ]
mulx r9, rbx, r10
test al, al
adox r13, rbx
adox r9, r15
mov rdx, [ rsi + 0x18 ]
mulx r8, r10, rdx
adcx r12, r13
adc r9, 0x0
mov rdx, 0x34 
bzhi r15, r12, rdx
shl r15, 4
mov rdx, rax
mulx rbx, rax, [ rsi + 0x20 ]
shrd r12, r9, 52
xor rdx, rdx
adox r10, rax
adox rbx, r8
mov r14, 0x34 
bzhi r13, rbp, r14
mov rbp, r13
shr rbp, 48
lea r15, [ r15 + rbp ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0x30 
bzhi rax, r13, rdx
mov r13, 0x1000003d1 
mov rdx, r13
mulx rbp, r13, r15
adox r13, r8
adox r9, rbp
bzhi r15, r13, r14
shrd r13, r9, 52
xor r8, r8
adox r12, r10
adox rbx, r8
mov rdx, [ rsi + 0x8 ]
mulx rbp, r10, rdi
mov rdx, rcx
mulx r9, rcx, [ rsi + 0x20 ]
bzhi rdx, r12, r14
adox r13, r10
adox rbp, r8
mov r10, 0x1000003d10 
mulx r14, r8, r10
test al, al
adox r8, r13
adox rbp, r14
shrd r12, rbx, 52
mov rbx, r8
shrd rbx, rbp, 52
test al, al
adox r12, rcx
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x10 ]
mulx r13, rcx, rdi
mov rdx, rcx
adcx rdx, [ rsp - 0x40 ]
adcx r13, [ rsp - 0x48 ]
mov rdi, 0xfffffffffffff 
mov r14, r12
and r14, rdi
xchg rdx, r10
mulx rcx, rbp, r14
adox rbx, r10
mov r14, 0x0 
adox r13, r14
adcx rbp, rbx
adcx r13, rcx
mov r10, rbp
and r10, rdi
shrd rbp, r13, 52
shrd r12, r9, 52
mulx rcx, r9, r12
and r11, rdi
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], r10
lea r11, [ r11 + rbp ]
adox r9, r11
adox rcx, r14
mov r13, r9
and r13, rdi
shrd r9, rcx, 52
lea rax, [ rax + r9 ]
mov [ rbx + 0x0 ], r15
mov [ rbx + 0x20 ], rax
and r8, rdi
mov [ rbx + 0x18 ], r13
mov [ rbx + 0x8 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 0.9249
; seed 1611997365195876 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1383305 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=155, initial num_batches=31): 106567 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0770379634281666
; number reverted permutation / tried permutation: 81867 / 90088 =90.874%
; number reverted decision / tried decision: 55343 / 89911 =61.553%
; validated in 0.331s
