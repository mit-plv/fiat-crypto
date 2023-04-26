SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
test al, al
adox r15, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r9
mulx r9, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x40 ], r13
mov [ rsp - 0x38 ], rcx
mulx rcx, r13, [ rsi + 0x8 ]
adcx r10, r15
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r13
mulx r13, r15, [ rax + 0x18 ]
adox r12, r13
mov rdx, 0x0 
adox rcx, rdx
adcx rdi, r12
mov r13, rdx
adcx r13, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r12, [ rax + 0x0 ]
adc r8, 0x0
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], r15
mov [ rsp - 0x20 ], rbp
mulx rbp, r15, [ rax + 0x8 ]
xor rdx, rdx
adox r12, rbp
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r15
mulx r15, rbp, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], rbx
mulx rbx, r15, [ rax + 0x10 ]
adox rcx, r10
adox r15, rdi
adox rbp, r13
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, [ rax + 0x8 ]
adcx r10, r12
mov rdx, [ rax + 0x10 ]
mulx r12, r13, [ rsi + 0x8 ]
adcx r13, rcx
adcx r11, r15
adcx r9, rbp
mov rdx, 0x0 
mov rcx, rdx
adox rcx, r8
mov r8, rdx
adcx r8, rcx
adox r14, rdx
mov rdx, [ rsi + 0x8 ]
mulx rbp, r15, [ rax + 0x0 ]
mov rdx, 0x0 
adcx r14, rdx
xor rcx, rcx
adox r15, [ rsp - 0x8 ]
adox rbp, r10
adox rdi, r13
adcx r15, [ rsp - 0x18 ]
adcx rbp, [ rsp - 0x20 ]
adcx rdi, [ rsp - 0x28 ]
adox r11, [ rsp - 0x30 ]
adox r9, [ rsp - 0x38 ]
adcx r12, r11
adox r8, [ rsp - 0x40 ]
mov rdx, 0x26 
mulx r13, r10, r12
adcx rbx, r9
mulx r9, r11, rbx
adcx r8, [ rsp - 0x10 ]
adox r14, rcx
adcx r14, rcx
mulx rbx, r12, r14
test al, al
adox r11, r15
mulx r14, r15, r8
adox r15, rbp
adcx r10, [ rsp - 0x48 ]
adox r12, rdi
adox rbx, rcx
adcx r13, r11
adcx r9, r15
adcx r14, r12
adc rbx, 0x0
mulx rdi, rbp, rbx
xor rdi, rdi
adox rbp, r10
mov rcx, rdi
adox rcx, r13
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x8 ], rcx
mov r11, rdi
adox r11, r9
mov r15, rdi
adox r15, r14
mov [ r8 + 0x10 ], r11
mov r10, rdi
cmovo r10, rdx
adcx rbp, r10
mov [ r8 + 0x0 ], rbp
mov [ r8 + 0x18 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.7097
; seed 0160442424583463 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 773612 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=178, initial num_batches=31): 68317 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.08830912653888513
; number reverted permutation / tried permutation: 66701 / 89940 =74.162%
; number reverted decision / tried decision: 39394 / 90059 =43.742%
; validated in 0.418s
