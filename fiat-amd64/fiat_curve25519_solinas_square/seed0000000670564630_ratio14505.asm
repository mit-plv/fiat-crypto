SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
xor rdx, rdx
adox r8, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
adcx rbx, r9
adcx r12, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r9, [ rsi + 0x10 ]
adcx r11, r13
adcx r9, rcx
mov rdx, [ rsi + 0x10 ]
mulx r13, rcx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx rcx, r12
adcx r13, r11
adox rbx, rbx
adox rcx, rcx
mov r12, rdx
adcx r12, r9
mov r11, rdx
adcx r11, rbp
adox r13, r13
adox r12, r12
setc r9b
clc
adcx r10, r8
adox r11, r11
mov rdx, [ rsi + 0x8 ]
mulx rbp, r8, rdx
adcx r8, rbx
adcx rbp, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, rbx, rdx
adcx rbx, r13
adcx rcx, r12
movzx rdx, r9b
mov r13, 0x0 
adox rdx, r13
movzx r12, r9b
lea r12, [ r12 + rdx ]
mov r9, 0x26 
mov rdx, rbx
mulx r13, rbx, r9
mov rdx, -0x2 
inc rdx
adox rbx, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, rax, rdx
adcx rax, r11
mov rdx, rcx
mulx r11, rcx, r9
adcx r12, r14
clc
adcx rcx, r10
adox r13, rcx
mov rdx, rax
mulx r10, rax, r9
adcx rax, r8
mov rdx, r9
mulx r8, r9, r12
adcx r9, rbp
mov rbp, 0x0 
adcx r8, rbp
adox r11, rax
adox r10, r9
adox r8, rbp
mulx r12, r14, r8
test al, al
adox r14, rbx
mov r12, rbp
adox r12, r13
mov rbx, rbp
adox rbx, r11
mov [ rdi + 0x10 ], rbx
mov rcx, rbp
adox rcx, r10
mov [ rdi + 0x8 ], r12
mov [ rdi + 0x18 ], rcx
mov r13, rbp
cmovo r13, rdx
adcx r14, r13
mov [ rdi + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4505
; seed 1324772535143581 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 512435 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=297, initial num_batches=31): 62831 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12261262404012216
; number reverted permutation / tried permutation: 68639 / 90107 =76.175%
; number reverted decision / tried decision: 34446 / 89892 =38.319%
; validated in 0.328s
