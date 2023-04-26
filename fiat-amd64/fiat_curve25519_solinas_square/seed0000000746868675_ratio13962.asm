SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
xor rdx, rdx
adox rax, rax
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
adcx r11, r10
adcx r8, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r10, [ rsi + 0x8 ]
adcx r10, r9
adox r11, r11
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
adcx r9, rcx
mov rdx, 0x0 
adcx rbp, rdx
clc
adcx r14, r8
adox r14, r14
adcx r15, r10
mov r8, rdx
adcx r8, r9
adox r15, r15
mov rcx, rdx
adcx rcx, rbp
setc r10b
clc
adcx rdi, rax
adcx r12, r11
mov rdx, [ rsi + 0x10 ]
mulx r11, rax, rdx
adcx r13, r14
adox r8, r8
adcx rax, r15
adox rcx, rcx
adcx r11, r8
mov rdx, 0x26 
mulx rbp, r9, r11
movzx r14, r10b
mov r15, 0x0 
adox r14, r15
movzx r8, r10b
lea r8, [ r8 + r14 ]
adcx rbx, rcx
adcx r8, [ rsp - 0x40 ]
mulx rcx, r10, rbx
mulx r14, r11, rax
test al, al
adox r11, [ rsp - 0x48 ]
mulx rbx, rax, r8
adcx r9, rdi
adox r14, r9
adcx r10, r12
adcx rax, r13
adcx rbx, r15
adox rbp, r10
adox rcx, rax
adox rbx, r15
mulx r12, rdi, rbx
xor r12, r12
adox rdi, r11
mov r15, r12
adox r15, r14
mov r13, r12
adox r13, rbp
mov r8, [ rsp - 0x50 ]
mov [ r8 + 0x10 ], r13
mov r11, r12
adox r11, rcx
mov r9, r12
cmovo r9, rdx
mov [ r8 + 0x18 ], r11
adcx rdi, r9
mov [ r8 + 0x0 ], rdi
mov [ r8 + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.3962
; seed 0055195596728753 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 406130 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=289, initial num_batches=31): 51147 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12593750769458056
; number reverted permutation / tried permutation: 71908 / 90271 =79.658%
; number reverted decision / tried decision: 45472 / 89728 =50.678%
; validated in 0.25s
