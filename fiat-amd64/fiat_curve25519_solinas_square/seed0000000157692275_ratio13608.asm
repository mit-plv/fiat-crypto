SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
adox r10, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mulx r13, rcx, [ rsi + 0x10 ]
adcx rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mulx r14, r10, [ rsi + 0x18 ]
adox r10, rbx
adcx r13, r10
mov rdx, [ rsi + 0x10 ]
mulx r10, rbx, [ rsi + 0x18 ]
adox rbx, r14
mov rdx, 0x0 
mov r14, rdx
adcx r14, rbx
adox r10, rdx
mov rbx, -0x3 
inc rbx
adox rax, rax
mov [ rsp - 0x58 ], r15
mov r15, rdx
adcx r15, r10
adox r11, r11
adox rcx, rcx
adox r13, r13
adox r14, r14
setc r10b
clc
adcx r9, rax
adcx rbp, r11
adcx r12, rcx
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, rdx
adcx rax, r13
adcx r11, r14
adox r15, r15
mov rdx, [ rsi + 0x18 ]
mulx r13, rcx, rdx
mov rdx, 0x26 
mulx rbx, r14, rax
adcx rcx, r15
movzx rax, r10b
mov r15, 0x0 
adox rax, r15
movzx r15, r10b
lea r15, [ r15 + rax ]
adcx r15, r13
mulx r13, r10, r11
test al, al
adox r10, r9
mulx r11, r9, rcx
adox r9, rbp
mulx rcx, rbp, r15
adox rbp, r12
mov r12, 0x0 
adox rcx, r12
adcx r14, r8
adcx rbx, r10
adcx r13, r9
adcx r11, rbp
adc rcx, 0x0
mulx rax, r8, rcx
xor rax, rax
adox r8, r14
mov r12, rax
adox r12, rbx
mov [ rdi + 0x8 ], r12
mov r15, rax
adox r15, r13
mov r10, rax
adox r10, r11
mov [ rdi + 0x18 ], r10
mov r9, rax
cmovo r9, rdx
adcx r8, r9
mov [ rdi + 0x10 ], r15
mov [ rdi + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3608
; seed 1827849984670503 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 835764 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=202, initial num_batches=31): 80485 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09630110892548614
; number reverted permutation / tried permutation: 67311 / 89964 =74.820%
; number reverted decision / tried decision: 26056 / 90035 =28.940%
; validated in 0.441s
