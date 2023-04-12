SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x8 ]
mulx r8, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], r10
mov [ rsp - 0x40 ], r15
mulx r15, r10, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r11
adcx rcx, r9
mov rdx, [ rax + 0x10 ]
mulx r9, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r9
mov [ rsp - 0x30 ], r15
mulx r15, r9, [ rax + 0x18 ]
adox rbp, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r9
mulx r9, r15, [ rax + 0x18 ]
mov rdx, 0x0 
adox r9, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r14
mulx r14, r15, [ rax + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], r13
mulx r13, r15, [ rax + 0x0 ]
mov rdx, -0x2 
inc rdx
adox r15, rdi
adox r13, rcx
adcx rbx, rbp
mov rdi, 0x0 
mov rcx, rdi
adcx rcx, r9
adcx r14, rdi
mov rdx, [ rsi + 0x18 ]
mulx r9, rbp, [ rax + 0x10 ]
adox r11, rbx
adox rbp, rcx
mov rdx, rdi
adox rdx, r14
clc
adcx r10, r15
mov r15, rdx
mov rdx, [ rax + 0x10 ]
mulx rcx, rbx, [ rsi + 0x8 ]
adcx rbx, r13
adcx r8, r11
mov rdx, [ rax + 0x0 ]
mulx r14, r13, [ rsi + 0x0 ]
adcx r12, rbp
mov rdx, [ rax + 0x18 ]
mulx rbp, r11, [ rsi + 0x18 ]
mov rdx, rdi
adcx rdx, r15
adox rbp, rdi
mov r15, -0x3 
inc r15
adox r14, [ rsp - 0x8 ]
adox r10, [ rsp - 0x18 ]
setc r15b
clc
adcx r14, [ rsp - 0x40 ]
adcx r10, [ rsp - 0x48 ]
adox rbx, [ rsp - 0x30 ]
adox r8, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x28 ]
adcx rcx, r8
adox r12, [ rsp - 0x10 ]
adcx r12, [ rsp - 0x38 ]
movzx r15, r15b
lea rbp, [ rbp + rdi ]
lea rbp, [ rbp + r15 ]
adox r11, rdx
adox rbp, rdi
mov r15, 0x26 
mov rdx, r12
mulx r8, r12, r15
adcx r9, r11
mov rdx, -0x3 
inc rdx
adox r12, r14
mov rdx, r9
mulx r14, r9, r15
adox r9, r10
adcx rbp, rdi
mov rdx, r15
mulx r10, r15, rcx
mulx r11, rcx, rbp
clc
adcx r15, r13
adcx r10, r12
adox rcx, rbx
adox r11, rdi
adcx r8, r9
adcx r14, rcx
adc r11, 0x0
mulx rbx, r13, r11
xor rbx, rbx
adox r13, r15
mov rdi, rbx
adox rdi, r10
mov r12, rbx
adox r12, r8
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], r12
mov rbp, rbx
adox rbp, r14
mov r15, rbx
cmovo r15, rdx
adcx r13, r15
mov [ r9 + 0x18 ], rbp
mov [ r9 + 0x8 ], rdi
mov [ r9 + 0x0 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.6667
; seed 3296523837007477 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 797539 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=204, initial num_batches=31): 74343 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09321550419477918
; number reverted permutation / tried permutation: 65546 / 89648 =73.115%
; number reverted decision / tried decision: 38901 / 90351 =43.055%
; validated in 0.413s
