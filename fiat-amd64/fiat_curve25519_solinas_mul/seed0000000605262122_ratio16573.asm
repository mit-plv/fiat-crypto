SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
test al, al
adox r9, r11
adox rbp, r14
mov rdx, [ rax + 0x8 ]
mulx r14, r11, [ rsi + 0x10 ]
adcx r11, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r15, r9, [ rax + 0x18 ]
adcx rbx, rbp
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, rbp, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r15, rdx
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r10
mulx r10, r13, [ rsi + 0x10 ]
mov rdx, 0x0 
mov [ rsp - 0x38 ], rcx
mov rcx, rdx
adcx rcx, r15
adc r8, 0x0
xor r15, r15
adox r13, rdi
adox r10, r11
mov rdx, [ rsi + 0x8 ]
mulx rdi, r11, [ rax + 0x8 ]
adcx r11, r13
mov rdx, [ rsi + 0x10 ]
mulx r15, r13, [ rax + 0x10 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x30 ], r15
mov [ rsp - 0x28 ], r9
mulx r9, r15, [ rsi + 0x8 ]
adcx r15, r10
adox r13, rbx
adcx r14, r13
mov rdx, [ rsi + 0x18 ]
mulx r10, rbx, [ rax + 0x10 ]
adox rbx, rcx
mov rdx, 0x0 
mov rcx, rdx
adox rcx, r8
adcx r12, rbx
mov rdx, [ rsi + 0x0 ]
mulx r13, r8, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x20 ], r8
mulx r8, rbx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r9
mulx r9, r10, [ rax + 0x0 ]
mov rdx, 0x0 
adox r8, rdx
mov [ rsp - 0x8 ], rbx
mov rbx, rdx
adcx rbx, rcx
adcx r8, rdx
xor rcx, rcx
adox r10, r13
adox r9, r11
adcx rbp, r10
adox rdi, r15
adox r14, [ rsp - 0x28 ]
adox r12, [ rsp - 0x38 ]
adox rbx, [ rsp - 0x8 ]
adox r8, rcx
adcx r9, [ rsp - 0x40 ]
adcx rdi, [ rsp - 0x48 ]
adcx r14, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x30 ]
adcx rbx, [ rsp - 0x18 ]
mov rdx, 0x26 
mulx r15, r11, rbx
mulx r10, r13, r12
adcx r8, rcx
mulx rbx, r12, r14
mulx rcx, r14, r8
xor r8, r8
adox r12, [ rsp - 0x20 ]
adcx r13, rbp
adcx r11, r9
adox rbx, r13
adcx r14, rdi
adcx rcx, r8
adox r10, r11
adox r15, r14
adox rcx, r8
mulx r9, rbp, rcx
xor r9, r9
adox rbp, r12
mov r8, r9
adox r8, rbx
mov rdi, r9
adox rdi, r10
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r8
mov [ r12 + 0x10 ], rdi
mov r13, r9
adox r13, r15
mov [ r12 + 0x18 ], r13
mov r11, r9
cmovo r11, rdx
adcx rbp, r11
mov [ r12 + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6573
; seed 1575242966132777 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 609657 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=304, initial num_batches=31): 66887 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.10971251047720275
; number reverted permutation / tried permutation: 70627 / 89766 =78.679%
; number reverted decision / tried decision: 50580 / 90233 =56.055%
; validated in 0.319s
