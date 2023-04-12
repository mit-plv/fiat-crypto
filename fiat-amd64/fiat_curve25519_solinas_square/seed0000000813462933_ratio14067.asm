SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
adox r10, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
adox rcx, rbx
adox r12, rbp
mov rdx, [ rsi + 0x10 ]
mulx rbp, rbx, [ rsi + 0x8 ]
adcx rbx, r10
mov rdx, 0x0 
adox r13, rdx
adcx rbp, rcx
mov r10, rdx
adcx r10, r12
mov rcx, -0x3 
inc rcx
adox rax, rax
mov r12, rdx
adcx r12, r13
adox r11, r11
adox rbx, rbx
adox rbp, rbp
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r13, rdx
adox r10, r10
adox r12, r12
seto dl
inc rcx
adox r14, rax
movzx rax, dl
mov [ rsp - 0x58 ], r15
setc r15b
mov rcx, 0x0 
adcx rax, rcx
movzx rdx, r15b
lea rdx, [ rdx + rax ]
adox r8, r11
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, rdx
adox r9, rbx
adox r11, rbp
adox rax, r10
mov rdx, [ rsi + 0x18 ]
mulx rbp, rbx, rdx
adox rbx, r12
adox r15, rbp
mov rdx, 0x26 
mulx r12, r10, rax
mulx rbp, rax, rbx
xor rbx, rbx
adox r10, r14
adox rax, r8
mulx r14, rcx, r15
mulx r15, r8, r11
adcx r8, r13
adcx r15, r10
adox rcx, r9
adox r14, rbx
adcx r12, rax
adcx rbp, rcx
adc r14, 0x0
mulx r9, r13, r14
test al, al
adox r13, r8
mov r9, rbx
adox r9, r15
mov r11, rbx
adox r11, r12
mov [ rdi + 0x8 ], r9
mov r10, rbx
adox r10, rbp
mov rax, rbx
cmovo rax, rdx
adcx r13, rax
mov [ rdi + 0x0 ], r13
mov [ rdi + 0x18 ], r10
mov [ rdi + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.4067
; seed 2735769366771116 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 536925 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=328, initial num_batches=31): 70543 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.131383340317549
; number reverted permutation / tried permutation: 69995 / 89545 =78.167%
; number reverted decision / tried decision: 34615 / 90454 =38.268%
; validated in 0.338s
