SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r11, r11
adcx r12, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, rcx, [ rsi + 0x0 ]
adcx rcx, r13
adcx r8, r14
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, [ rsi + 0x10 ]
adcx rax, r9
mov rdx, 0x0 
adcx r10, rdx
clc
adcx r13, rcx
adox r12, r12
adcx r14, r8
mov r9, rdx
adcx r9, rax
adox r13, r13
adox r14, r14
mov rcx, rdx
adcx rcx, r10
adox r9, r9
adox rcx, rcx
mov rdx, [ rsi + 0x0 ]
mulx rax, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, rdx
setc dl
clc
adcx rax, r11
adcx r10, r12
movzx r11, dl
mov r12, 0x0 
adox r11, r12
movzx r12, dl
lea r12, [ r12 + r11 ]
adcx r15, r13
adcx rbx, r14
adcx rbp, r9
mov rdx, [ rsi + 0x18 ]
mulx r14, r13, rdx
adcx r13, rcx
adcx r12, r14
mov rdx, 0x26 
mulx rcx, r9, rbx
test al, al
adox r9, r8
mulx r11, r8, rbp
adcx r8, rax
adox rcx, r8
mulx rbx, rax, r13
adcx rax, r10
mulx rbp, r10, r12
adcx r10, r15
adox r11, rax
mov r15, 0x0 
adcx rbp, r15
adox rbx, r10
adox rbp, r15
mulx r13, r14, rbp
test al, al
adox r14, r9
mov r13, r15
adox r13, rcx
mov r12, r15
adox r12, r11
mov r9, r15
adox r9, rbx
mov r8, r15
cmovo r8, rdx
adcx r14, r8
mov [ rdi + 0x18 ], r9
mov [ rdi + 0x8 ], r13
mov [ rdi + 0x0 ], r14
mov [ rdi + 0x10 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3373
; seed 1852292936045315 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5276 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=247, initial num_batches=31): 625 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.11846095526914328
; number reverted permutation / tried permutation: 371 / 540 =68.704%
; number reverted decision / tried decision: 255 / 459 =55.556%
; validated in 0.506s
