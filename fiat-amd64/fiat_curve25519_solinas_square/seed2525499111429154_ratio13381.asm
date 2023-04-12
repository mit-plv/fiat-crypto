SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
xor r11, r11
adox rax, rax
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x10 ]
mulx r11, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
adcx r9, r10
adcx r12, r11
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
adcx r10, r13
adcx rdi, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, r13, [ rsi + 0x8 ]
adox r9, r9
mov rdx, 0x0 
adcx rbx, rdx
clc
adcx r13, r12
adox r13, r13
adcx r11, r10
mov r12, rdx
adcx r12, rdi
mov r10, rdx
adcx r10, rbx
adox r11, r11
adox r12, r12
adox r10, r10
setc dil
clc
adcx rbp, rax
adcx r14, r9
movzx rax, dil
adox rax, rdx
adcx r15, r13
movzx r9, dil
lea r9, [ r9 + rax ]
adcx rcx, r11
adcx r8, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, rdx
adcx rbx, r10
adcx r9, r13
mov rdx, 0x26 
mulx r11, rdi, r9
mulx r10, r12, r8
xor rax, rax
adox r12, rbp
mulx r8, rbp, rcx
adcx rbp, [ rsp - 0x48 ]
adcx r8, r12
mulx r13, rcx, rbx
adox rcx, r14
adox rdi, r15
adcx r10, rcx
adcx r13, rdi
adox r11, rax
adc r11, 0x0
mulx r15, r14, r11
test al, al
adox r14, rbp
mov r15, rax
adox r15, r8
mov rbx, rax
adox rbx, r10
mov r9, rax
adox r9, r13
mov r12, rax
cmovo r12, rdx
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x8 ], r15
mov [ rbp + 0x18 ], r9
adcx r14, r12
mov [ rbp + 0x0 ], r14
mov [ rbp + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3381
; seed 2525499111429154 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3507 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=271, initial num_batches=31): 387 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.11035072711719418
; number reverted permutation / tried permutation: 322 / 492 =65.447%
; number reverted decision / tried decision: 280 / 507 =55.227%
; validated in 0.417s
