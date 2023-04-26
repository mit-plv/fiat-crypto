SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x18 ]
xor rdx, rdx
adox rax, rcx
adox r8, r10
mov rdx, [ rsi + 0x10 ]
mulx rcx, r10, [ rsi + 0x8 ]
adox r12, r9
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r9, [ rsi + 0x10 ]
adox r9, r13
adcx r10, r8
adcx rcx, r12
mov rdx, 0x0 
adox r14, rdx
mov r13, rdx
adcx r13, r9
mov r8, -0x3 
inc r8
adox r11, r11
adox rax, rax
mov rdx, [ rsi + 0x8 ]
mulx r9, r12, rdx
mov rdx, 0x0 
mov [ rsp - 0x58 ], r15
mov r15, rdx
adcx r15, r14
setc r14b
clc
adcx rbp, r11
adox r10, r10
adcx r12, rax
adcx r9, r10
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, rdx
adox rcx, rcx
adcx r11, rcx
adox r13, r13
adcx rax, r13
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, rdx
mov rdx, 0x26 
mulx r8, r13, r11
mov [ rsp - 0x50 ], rdi
mulx rdi, r11, rax
adox r15, r15
movzx rax, r14b
mov rdx, 0x0 
adox rax, rdx
adcx r10, r15
movzx r15, r14b
lea r15, [ r15 + rax ]
adcx r15, rcx
mov r14, 0x26 
mov rdx, r14
mulx rcx, r14, r15
xor rax, rax
adox r11, rbp
adcx r13, rbx
adcx r8, r11
mulx rbp, rbx, r10
adox rbx, r12
adox r14, r9
adcx rdi, rbx
adox rcx, rax
adcx rbp, r14
adc rcx, 0x0
mulx r9, r12, rcx
test al, al
adox r12, r13
mov r9, rax
adox r9, r8
mov r10, rax
adox r10, rdi
mov r15, rax
adox r15, rbp
mov r11, rax
cmovo r11, rdx
adcx r12, r11
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], r12
mov [ r13 + 0x8 ], r9
mov [ r13 + 0x10 ], r10
mov [ r13 + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3770
; seed 2950628564935764 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4761 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=201, initial num_batches=31): 458 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09619827767275782
; number reverted permutation / tried permutation: 385 / 490 =78.571%
; number reverted decision / tried decision: 159 / 509 =31.238%
; validated in 0.451s
