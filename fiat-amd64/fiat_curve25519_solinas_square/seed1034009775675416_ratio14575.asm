SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox rbx, r9
adox rax, rbp
adox r12, r10
mov rdx, [ rsi + 0x10 ]
mulx r9, r10, [ rsi + 0x8 ]
adcx r10, rax
mov rdx, [ rsi + 0x18 ]
mulx rax, rbp, [ rsi + 0x10 ]
adox rbp, r13
adcx r9, r12
mov rdx, 0x0 
mov r13, rdx
adcx r13, rbp
adox rax, rdx
mov r12, rdx
adcx r12, rax
mov rbp, -0x3 
inc rbp
adox r8, r8
adox rbx, rbx
adox r10, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, rax, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx rbp, r15, rdx
adox r9, r9
setc dl
clc
adcx r14, r8
adcx r15, rbx
adcx rbp, r10
adox r13, r13
adox r12, r12
movzx r8, dl
mov rbx, 0x0 
adox r8, rbx
movzx r10, dl
lea r10, [ r10 + r8 ]
adcx r11, r9
mov rdx, 0x26 
mulx r8, r9, r11
adcx rcx, r13
mulx r11, r13, rcx
mov rdx, [ rsi + 0x18 ]
mulx rbx, rcx, rdx
adcx rcx, r12
adcx r10, rbx
mov rdx, 0x26 
mulx rbx, r12, r10
xor r10, r10
adox r9, rax
adcx r13, r14
mulx r14, rax, rcx
adox r8, r13
adcx rax, r15
adox r11, rax
adcx r12, rbp
adcx rbx, r10
adox r14, r12
adox rbx, r10
mulx rbp, r15, rbx
test al, al
adox r15, r9
mov rbp, r10
adox rbp, r8
mov rcx, r10
adox rcx, r11
mov r9, r10
adox r9, r14
mov [ rdi + 0x18 ], r9
mov r13, r10
cmovo r13, rdx
adcx r15, r13
mov [ rdi + 0x0 ], r15
mov [ rdi + 0x8 ], rbp
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4575
; seed 1034009775675416 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2199 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=284, initial num_batches=31): 262 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.11914506593906321
; number reverted permutation / tried permutation: 337 / 483 =69.772%
; number reverted decision / tried decision: 259 / 516 =50.194%
; validated in 0.261s
