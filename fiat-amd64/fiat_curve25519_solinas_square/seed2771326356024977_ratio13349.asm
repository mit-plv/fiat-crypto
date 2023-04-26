SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox r11, r9
adox r12, rcx
mov rdx, [ rsi + 0x8 ]
mulx r9, rcx, rdx
adox rax, r13
adox rbx, r10
mov rdx, [ rsi + 0x8 ]
mulx r13, r10, [ rsi + 0x10 ]
mov rdx, 0x0 
adox rbp, rdx
adcx r10, r12
mov r12, -0x3 
inc r12
adox r8, r8
adox r11, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
adox r10, r10
adcx r13, rax
mov rdx, 0x0 
mov rax, rdx
adcx rax, rbx
mov rbx, rdx
adcx rbx, rbp
setc bpl
clc
adcx r15, r8
adox r13, r13
adox rax, rax
mov rdx, [ rsi + 0x10 ]
mulx r12, r8, rdx
adcx rcx, r11
adcx r9, r10
adcx r8, r13
adox rbx, rbx
movzx rdx, bpl
mov r11, 0x0 
adox rdx, r11
movzx r10, bpl
lea r10, [ r10 + rdx ]
adcx r12, rax
mov rdx, [ rsi + 0x18 ]
mulx r13, rbp, rdx
adcx rbp, rbx
mov rdx, 0x26 
mulx rbx, rax, rbp
adcx r10, r13
mulx rbp, r13, r12
mulx r11, r12, r8
xor r8, r8
adox r12, r14
adcx r13, r15
adcx rax, rcx
mulx r15, r14, r10
adcx r14, r9
adox r11, r13
adox rbp, rax
adcx r15, r8
adox rbx, r14
adox r15, r8
mulx r9, rcx, r15
xor r9, r9
adox rcx, r12
mov r8, r9
adox r8, r11
mov [ rdi + 0x8 ], r8
mov r10, r9
adox r10, rbp
mov r12, r9
adox r12, rbx
mov [ rdi + 0x18 ], r12
mov r13, r9
cmovo r13, rdx
adcx rcx, r13
mov [ rdi + 0x10 ], r10
mov [ rdi + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3349
; seed 2771326356024977 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5259 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=247, initial num_batches=31): 577 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1097166761741776
; number reverted permutation / tried permutation: 339 / 500 =67.800%
; number reverted decision / tried decision: 283 / 499 =56.713%
; validated in 0.522s
