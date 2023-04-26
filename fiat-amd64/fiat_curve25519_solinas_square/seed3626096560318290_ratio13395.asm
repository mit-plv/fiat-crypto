SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
xor rdx, rdx
adox rbx, rbx
adcx rax, rbp
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
adcx r11, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mulx r13, r10, [ rsi + 0x10 ]
adcx rbp, rcx
adcx r10, r12
mov rdx, [ rsi + 0x8 ]
mulx r12, rcx, [ rsi + 0x10 ]
setc dl
clc
adcx rcx, r11
movzx r11, dl
lea r11, [ r11 + r13 ]
adcx r12, rbp
mov r13, 0x0 
mov rbp, r13
adcx rbp, r10
adox rax, rax
mov rdx, r13
adcx rdx, r11
setc r10b
clc
adcx r9, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x8 ]
mulx r13, r11, rdx
adox rcx, rcx
adcx r11, rax
adcx r13, rcx
adox r12, r12
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, rdx
adox rbp, rbp
adox rbx, rbx
adcx rax, r12
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r12, rdx
adcx rcx, rbp
mov rdx, 0x26 
mov [ rsp - 0x58 ], r15
mulx r15, rbp, rcx
adcx r12, rbx
movzx rbx, r10b
mov rcx, 0x0 
adox rbx, rcx
movzx rcx, r10b
lea rcx, [ rcx + rbx ]
mulx rbx, r10, r12
adcx rcx, r14
xor r14, r14
adox rbp, r9
mulx r12, r9, rax
adox r10, r11
adcx r9, r8
adcx r12, rbp
adcx r15, r10
mulx r11, r8, rcx
adox r8, r13
adcx rbx, r8
adox r11, r14
adc r11, 0x0
mulx rax, r13, r11
xor rax, rax
adox r13, r9
mov r14, rax
adox r14, r12
mov [ rdi + 0x8 ], r14
mov rcx, rax
adox rcx, r15
mov rbp, rax
adox rbp, rbx
mov [ rdi + 0x18 ], rbp
mov r10, rax
cmovo r10, rdx
adcx r13, r10
mov [ rdi + 0x0 ], r13
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.3395
; seed 3626096560318290 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4913 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=504, initial num_batches=31): 783 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.15937309179727255
; number reverted permutation / tried permutation: 380 / 527 =72.106%
; number reverted decision / tried decision: 268 / 472 =56.780%
; validated in 0.546s
