SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox rax, rcx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x18 ]
adox rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
adox r10, rbx
adcx r12, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbx, [ rsi + 0x10 ]
adcx r13, r10
adox rbx, rbp
mov rdx, 0x0 
adox rcx, rdx
mov rbp, -0x3 
inc rbp
adox r11, r11
adox rax, rax
adox r12, r12
adox r13, r13
mov r10, rdx
adcx r10, rbx
mov rbx, rdx
adcx rbx, rcx
adox r10, r10
setc cl
clc
adcx r9, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, r11, rdx
adcx r11, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, rax, rdx
adox rbx, rbx
adcx r14, r12
movzx rdx, cl
mov r12, 0x0 
adox rdx, r12
adcx rax, r13
movzx r13, cl
lea r13, [ r13 + rdx ]
adcx r15, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, rdx
adcx rcx, rbx
mov rdx, 0x26 
mulx r12, rbx, r15
mulx rbp, r15, rax
adcx r13, r10
xor rax, rax
adox r15, r8
mulx r10, r8, r13
adcx rbx, r9
mulx r13, r9, rcx
adcx r9, r11
adox rbp, rbx
adox r12, r9
adcx r8, r14
adox r13, r8
adcx r10, rax
adox r10, rax
mulx r14, r11, r10
test al, al
adox r11, r15
mov r14, rax
adox r14, rbp
mov rcx, rax
adox rcx, r12
mov r15, rax
adox r15, r13
mov [ rdi + 0x18 ], r15
mov rbx, rax
cmovo rbx, rdx
adcx r11, rbx
mov [ rdi + 0x0 ], r11
mov [ rdi + 0x8 ], r14
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3284
; seed 3033498274158400 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 930357 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=266, initial num_batches=31): 105547 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11344784851406503
; number reverted permutation / tried permutation: 62909 / 90039 =69.869%
; number reverted decision / tried decision: 49695 / 89960 =55.241%
; validated in 0.488s
