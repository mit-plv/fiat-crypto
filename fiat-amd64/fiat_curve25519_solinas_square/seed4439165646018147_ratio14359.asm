SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
test al, al
adox rax, rax
adcx rbx, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, r10, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
adcx r13, rbp
adcx r15, r14
adcx r10, rdi
mov rdx, [ rsi + 0x10 ]
mulx r14, rbp, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
clc
adcx rbp, r13
adcx r14, r15
mov rdi, rdx
adcx rdi, r10
mov r13, rdx
adcx r13, r12
setc r15b
clc
adcx rcx, rax
adox rbx, rbx
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
adcx rax, rbx
adox rbp, rbp
adox r14, r14
adox rdi, rdi
adox r13, r13
movzx rdx, r15b
mov r12, 0x0 
adox rdx, r12
adcx r10, rbp
adcx r8, r14
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r14, rbp, rdx
movzx rdx, r15b
lea rdx, [ rdx + rbx ]
adcx r9, rdi
adcx rbp, r13
adcx rdx, r14
mov r15, 0x26 
mulx r13, rdi, r15
mov rdx, r15
mulx rbx, r15, r9
mulx r9, r14, r8
xor r8, r8
adox r15, rcx
adcx r14, r11
mulx r11, r12, rbp
adox r12, rax
adcx r9, r15
adcx rbx, r12
adox rdi, r10
adox r13, r8
adcx r11, rdi
adc r13, 0x0
mulx rax, rcx, r13
xor rax, rax
adox rcx, r14
mov r8, rax
adox r8, r9
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], r8
mov rbp, rax
adox rbp, rbx
mov r15, rax
adox r15, r11
mov [ r10 + 0x18 ], r15
mov r14, rax
cmovo r14, rdx
adcx rcx, r14
mov [ r10 + 0x0 ], rcx
mov [ r10 + 0x10 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4359
; seed 4439165646018147 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2367 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=283, initial num_batches=31): 272 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1149133924799324
; number reverted permutation / tried permutation: 354 / 492 =71.951%
; number reverted decision / tried decision: 270 / 507 =53.254%
; validated in 0.262s
