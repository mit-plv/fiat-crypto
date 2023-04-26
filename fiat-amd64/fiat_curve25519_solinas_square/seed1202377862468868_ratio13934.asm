SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r12
adcx r10, r12
setc r12b
clc
adcx r8, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adcx r13, r9
adcx r15, r14
mov rdx, [ rsi + 0x10 ]
mulx r14, r9, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rax
mov [ rsp - 0x40 ], r10
mulx r10, rax, [ rsi + 0x10 ]
adcx r9, rdi
setc dl
clc
adcx rax, r13
adox r8, r8
adcx r10, r15
adox rax, rax
movzx rdi, dl
lea rdi, [ rdi + r14 ]
mov r13, 0x0 
mov r15, r13
adcx r15, r9
mov r14, r13
adcx r14, rdi
adox r10, r10
adox r15, r15
setc dl
clc
mov r9, -0x1 
movzx r12, r12b
adcx r12, r9
adcx r8, rbx
adcx rbp, rax
adcx r11, r10
mov rbx, 0x26 
xchg rdx, r11
mulx rax, r12, rbx
adox r14, r14
adcx rcx, r15
movzx rdi, r11b
adox rdi, r13
movzx r10, r11b
lea r10, [ r10 + rdi ]
mov rdx, rcx
mulx r11, rcx, rbx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r15, rdx
adcx r15, r14
adcx r10, rdi
mov rdx, r15
mulx r14, r15, rbx
test al, al
adox rcx, [ rsp - 0x40 ]
adox r15, r8
adcx r12, [ rsp - 0x48 ]
adcx rax, rcx
adcx r11, r15
mov rdx, rbx
mulx r8, rbx, r10
adox rbx, rbp
adox r8, r13
adcx r14, rbx
adc r8, 0x0
mulx rdi, rbp, r8
xor rdi, rdi
adox rbp, r12
mov r13, rdi
adox r13, rax
mov r10, rdi
adox r10, r11
mov rcx, rdi
adox rcx, r14
mov r15, rdi
cmovo r15, rdx
adcx rbp, r15
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x10 ], r10
mov [ r12 + 0x0 ], rbp
mov [ r12 + 0x8 ], r13
mov [ r12 + 0x18 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.3934
; seed 1202377862468868 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 3308 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=324, initial num_batches=31): 411 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.12424425634824668
; number reverted permutation / tried permutation: 362 / 488 =74.180%
; number reverted decision / tried decision: 278 / 511 =54.403%
; validated in 0.337s
