SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
test al, al
adox r8, r10
adox rbx, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rsi + 0x18 ]
adcx r11, rbx
adox r10, rbp
adcx rcx, r10
mov rdx, [ rsi + 0x10 ]
mulx rbx, rbp, [ rsi + 0x18 ]
adox rbp, r9
mov rdx, 0x0 
mov r9, rdx
adcx r9, rbp
adox rbx, rdx
mov r10, -0x3 
inc r10
adox rax, rax
adox r8, r8
adox r11, r11
adox rcx, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, 0x0 
mov [ rsp - 0x68 ], r13
mov r13, rdx
adcx r13, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, rbx, rdx
setc dl
clc
adcx r12, rax
adcx rbx, r8
adcx r14, r11
adox r9, r9
adox r13, r13
movzx rax, dl
mov r8, 0x0 
adox rax, r8
movzx r11, dl
lea r11, [ r11 + rax ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rax, rdx
adcx rax, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, rcx, rdx
adcx r8, r9
adcx rcx, r13
adcx r11, r15
mov rdx, 0x26 
mulx r13, r9, r8
xor r15, r15
adox r9, r12
mulx r8, r12, rax
adcx r12, rbp
mulx rax, rbp, rcx
adcx r8, r9
adox rbp, rbx
adcx r13, rbp
mulx rcx, rbx, r11
adox rbx, r14
adox rcx, r15
adcx rax, rbx
adc rcx, 0x0
mulx r11, r14, rcx
xor r11, r11
adox r14, r12
mov r15, r11
adox r15, r8
mov r9, r11
adox r9, r13
mov [ rdi + 0x10 ], r9
mov [ rdi + 0x8 ], r15
mov r12, r11
adox r12, rax
mov r8, r11
cmovo r8, rdx
adcx r14, r8
mov [ rdi + 0x0 ], r14
mov [ rdi + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.4689
; seed 3579199592384032 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2932 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=297, initial num_batches=31): 373 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.1272169167803547
; number reverted permutation / tried permutation: 350 / 492 =71.138%
; number reverted decision / tried decision: 175 / 507 =34.517%
; validated in 0.329s
