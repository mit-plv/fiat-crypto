SECTION .text
	GLOBAL fiat_secp256k1_dettman_square
fiat_secp256k1_dettman_square:
mov rdx, [ rsi + 0x20 ]
mulx r10, rax, rdx
mov r11, [ rsi + 0x0 ]
lea rdx, [r11 + r11]
mov r11, [ rsi + 0x8 ]
lea rcx, [r11 + r11]
mov r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, rax
shrd rdx, r10, 52
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r11
mov rdx, 0x1000003d10 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, r10
mov r10, 0x34 
mov [ rsp - 0x60 ], r14
bzhi r14, rax, r10
mov [ rsp - 0x58 ], r15
mulx r15, rax, r14
mov rdx, [ rsi + 0x10 ]
mulx r10, r14, rcx
mov rdx, rcx
mov [ rsp - 0x50 ], rdi
mulx rdi, rcx, [ rsi + 0x20 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, rdx
adox r14, rbx
adox rbp, r10
xor rdx, rdx
adox r13, r9
adox r8, r12
adcx rax, r14
adcx rbp, r15
mov rbx, rax
shrd rbx, rbp, 52
mov rdx, r11
mulx r15, r11, [ rsi + 0x20 ]
mov r10, [ rsi + 0x10 ]
mov r9, r10
shl r9, 0x1
xchg rdx, r9
mulx r12, r10, [ rsi + 0x18 ]
xor r14, r14
adox r10, rcx
adox rdi, r12
mulx rbp, rcx, [ rsi + 0x20 ]
adcx r13, r11
adcx r15, r8
test al, al
adox rbx, r13
adox r15, r14
mov r8, rbx
adcx r8, [ rsp - 0x30 ]
adcx r15, [ rsp - 0x38 ]
mov r11, r8
shrd r11, r15, 52
add r11, r10
adc rdi, 0x0
mov rdx, 0xfffffffffffff 
and r8, rdx
mov r12, r11
and r12, rdx
shl r12, 4
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, rdx
shrd r11, rdi, 52
add r10, rcx
adcx rbp, r13
test al, al
adox r11, r10
adox rbp, r14
mov rdx, 0xfffffffffffff 
mov rcx, r11
and rcx, rdx
shrd r11, rbp, 52
mov rbx, [ rsi + 0x18 ]
lea r15, [rbx + rbx]
mov rbx, 0xffffffffffff 
mov rdi, r8
and rdi, rbx
shr r8, 48
lea r12, [ r12 + r8 ]
mov r13, 0x1000003d10 
mov rdx, rcx
mulx r10, rcx, r13
mov rdx, [ rsi + 0x8 ]
mulx r8, rbp, r9
mov rdx, 0x1000003d1 
mulx r13, r14, r12
test al, al
adox r14, [ rsp - 0x40 ]
adox r13, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x20 ]
mulx rbx, r12, r15
adcx r11, r12
adc rbx, 0x0
mov rdx, r11
shrd rdx, rbx, 52
mov r15, r14
shrd r15, r13, 52
mov r13, 0xfffffffffffff 
and r11, r13
adox r15, rbp
mov r12, 0x0 
adox r8, r12
adcx rcx, r15
adcx r8, r10
mov r10, rcx
and r10, r13
and r14, r13
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x0 ], r14
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r14, r15, r9
mov rdx, [ rsi + 0x8 ]
mulx r12, r9, rdx
shrd rcx, r8, 52
xor rdx, rdx
adox r9, r15
adox r14, r12
mov [ rbp + 0x8 ], r10
adcx rcx, r9
adc r14, 0x0
mov r8, 0x1000003d10 
mov rdx, r8
mulx r10, r8, r11
and rax, r13
adox r8, rcx
adox r14, r10
mov r11, r8
shrd r11, r14, 52
lea rax, [ rax + r11 ]
and r8, r13
mulx r12, r15, rbx
adox r15, rax
mov rbx, 0x0 
adox r12, rbx
mov [ rbp + 0x10 ], r8
mov r9, r15
shrd r9, r12, 52
and r15, r13
mov [ rbp + 0x18 ], r15
lea rdi, [ rdi + r9 ]
mov [ rbp + 0x20 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 0.9932
; seed 3599198233748203 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 935342 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=271, initial num_batches=31): 89077 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09523468421176426
; number reverted permutation / tried permutation: 73795 / 89776 =82.199%
; number reverted decision / tried decision: 53560 / 90223 =59.364%
; validated in 0.261s
