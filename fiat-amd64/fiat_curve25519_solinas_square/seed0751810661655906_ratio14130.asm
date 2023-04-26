SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adox r10, r13
adox r15, r14
adox rbx, rdi
adcx r11, r10
mov rdx, 0x0 
adox rbp, rdx
adcx rcx, r15
mov r13, -0x3 
inc r13
adox rax, rax
adox r12, r12
mov r14, rdx
adcx r14, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, rdi, rdx
adox r11, r11
mov rdx, 0x0 
mov r15, rdx
adcx r15, rbp
adox rcx, rcx
setc bl
clc
adcx r9, rax
adcx rdi, r12
mov rdx, [ rsi + 0x10 ]
mulx rax, rbp, rdx
adcx r10, r11
adcx rbp, rcx
adox r14, r14
adcx rax, r14
adox r15, r15
movzx rdx, bl
mov r12, 0x0 
adox rdx, r12
mov r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rcx, rdx
adcx rcx, r15
mov rdx, 0x26 
mulx r12, r15, rax
movzx rax, bl
lea rax, [ rax + r11 ]
mulx r11, rbx, rcx
mulx r13, rcx, rbp
adcx rax, r14
xor rbp, rbp
adox rcx, r8
mulx r14, r8, rax
adcx r15, r9
adcx rbx, rdi
adcx r8, r10
adox r13, r15
adcx r14, rbp
adox r12, rbx
adox r11, r8
adox r14, rbp
mulx rdi, r9, r14
add r9, rcx
mov rdi, rbp
adcx rdi, r13
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], rdi
mov rax, rbp
adcx rax, r12
mov [ r10 + 0x10 ], rax
mov rcx, rbp
adcx rcx, r11
mov [ r10 + 0x18 ], rcx
mov r15, rbp
cmovc r15, rdx
mov rbx, -0x3 
inc rbx
adox r9, r15
mov [ r10 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4130
; seed 0751810661655906 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2390 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=541, initial num_batches=31): 380 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1589958158995816
; number reverted permutation / tried permutation: 441 / 527 =83.681%
; number reverted decision / tried decision: 290 / 472 =61.441%
; validated in 0.227s
