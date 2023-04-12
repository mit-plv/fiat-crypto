SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
adox r8, rcx
adox r10, r9
adcx rax, rax
mov rdx, [ rsi + 0x10 ]
mulx r9, rcx, [ rsi + 0x18 ]
adox rcx, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, 0x0 
adox r9, rdx
mov [ rsp - 0x70 ], r12
mov r12, -0x3 
inc r12
adox rbx, r8
adox rbp, r10
adcx r11, r11
mov r8, rdx
adox r8, rcx
mov r10, rdx
adox r10, r9
adcx rbx, rbx
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
seto dl
inc r12
adox r9, rax
adox r13, r11
adox r14, rbx
adcx rbp, rbp
mov al, dl
mov rdx, [ rsi + 0x10 ]
mulx rbx, r11, rdx
adox r11, rbp
adcx r8, r8
adox rbx, r8
adcx r10, r10
movzx rdx, al
mov rbp, 0x0 
adcx rdx, rbp
movzx r8, al
lea r8, [ r8 + rdx ]
mov rdx, [ rsi + 0x18 ]
mulx rbp, rax, rdx
adox rax, r10
mov rdx, 0x26 
mov [ rsp - 0x58 ], r15
mulx r15, r10, r11
clc
adcx r10, rcx
mulx r11, rcx, rbx
adox r8, rbp
mulx rbp, rbx, r8
inc r12
adox rcx, r9
mulx r8, r9, rax
adcx r15, rcx
adox r9, r13
adcx r11, r9
adox rbx, r14
adox rbp, r12
adcx r8, rbx
adc rbp, 0x0
mulx r14, r13, rbp
test al, al
adox r13, r10
mov r14, r12
adox r14, r15
mov [ rdi + 0x8 ], r14
mov rax, r12
adox rax, r11
mov r10, r12
adox r10, r8
mov [ rdi + 0x10 ], rax
mov rcx, r12
cmovo rcx, rdx
adcx r13, rcx
mov [ rdi + 0x0 ], r13
mov [ rdi + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.4360
; seed 1400031411541571 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3422 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=248, initial num_batches=31): 359 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.10490940970192869
; number reverted permutation / tried permutation: 305 / 491 =62.118%
; number reverted decision / tried decision: 272 / 508 =53.543%
; validated in 0.424s
