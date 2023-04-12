SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
test al, al
adox rax, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
adox r13, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r10, [ rsi + 0x8 ]
adcx r10, r13
adox r11, r14
adcx r15, r11
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, [ rsi + 0x18 ]
adox r14, rcx
mov rdx, 0x0 
mov rcx, rdx
adcx rcx, r14
adox r13, rdx
mov r11, -0x3 
inc r11
adox r8, r8
mov r14, rdx
adcx r14, r13
adox rax, rax
mov rdx, [ rsi + 0x8 ]
mulx r11, r13, rdx
setc dl
clc
adcx rbp, r8
adox r10, r10
adox r15, r15
adcx r13, rax
adcx r11, r10
adox rcx, rcx
adox r14, r14
adcx r9, r15
movzx r8, dl
mov rax, 0x0 
adox r8, rax
adcx r12, rcx
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, rdx
mov rdx, 0x26 
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, r12
adcx r15, r14
movzx r14, r10b
lea r14, [ r14 + r8 ]
mulx r8, r10, r9
adcx r14, rcx
xor r9, r9
adox rax, rbp
mulx r12, rbp, r15
mulx r15, rcx, r14
adox rbp, r13
adox rcx, r11
adcx r10, rbx
adcx r8, rax
adcx rdi, rbp
adcx r12, rcx
adox r15, r9
adc r15, 0x0
mulx r13, rbx, r15
test al, al
adox rbx, r10
mov r13, r9
adox r13, r8
mov r11, [ rsp - 0x50 ]
mov [ r11 + 0x8 ], r13
mov r14, r9
adox r14, rdi
mov rax, r9
adox rax, r12
mov [ r11 + 0x18 ], rax
mov rbp, r9
cmovo rbp, rdx
adcx rbx, rbp
mov [ r11 + 0x10 ], r14
mov [ r11 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4925
; seed 0620316959369425 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 539531 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=320, initial num_batches=31): 69643 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.12908062743382678
; number reverted permutation / tried permutation: 68388 / 89871 =76.096%
; number reverted decision / tried decision: 34990 / 90128 =38.823%
; validated in 0.328s
