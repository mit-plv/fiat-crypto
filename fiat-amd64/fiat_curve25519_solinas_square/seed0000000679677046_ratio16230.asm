SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x18 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
xor rdx, rdx
adox r11, r11
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
adcx rcx, r9
adcx rax, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rsi + 0x18 ]
adcx r9, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r14, rdx
clc
adcx r10, rcx
adcx r15, rax
mov rcx, rdx
adcx rcx, r9
adox r8, r8
mov rax, rdx
adcx rax, r14
adox r10, r10
adox r15, r15
adox rcx, rcx
adox rax, rax
seto r9b
mov r14, -0x3 
inc r14
adox rbp, r11
adox r12, r8
adox r13, r10
mov rdx, [ rsi + 0x10 ]
mulx r8, r11, rdx
adox r11, r15
movzx rdx, r9b
setc r10b
mov r15, 0x0 
adcx rdx, r15
movzx r9, r10b
lea r9, [ r9 + rdx ]
adox r8, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
adox r10, rax
mov rdx, 0x26 
mulx r15, rax, r8
mulx r14, r8, r10
mov [ rsp - 0x50 ], rdi
mulx rdi, r10, r11
adox r9, rcx
xor r11, r11
adox r10, rbx
adcx rax, rbp
adcx r8, r12
mulx rbp, rbx, r9
adcx rbx, r13
adox rdi, rax
adox r15, r8
adox r14, rbx
adcx rbp, r11
adox rbp, r11
mulx r13, r12, rbp
xor r13, r13
adox r12, r10
mov r11, r13
adox r11, rdi
mov rcx, r13
adox rcx, r15
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], rcx
mov r10, r13
adox r10, r14
mov rax, r13
cmovo rax, rdx
mov [ r9 + 0x18 ], r10
adcx r12, rax
mov [ r9 + 0x8 ], r11
mov [ r9 + 0x0 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6230
; seed 2493593397743513 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 518698 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=293, initial num_batches=31): 60367 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.11638178670440218
; number reverted permutation / tried permutation: 71389 / 89895 =79.414%
; number reverted decision / tried decision: 51834 / 90104 =57.527%
; validated in 0.375s
