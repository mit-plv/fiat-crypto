SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
xor rdx, rdx
adox rax, rcx
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, rcx, [ rsi + 0x0 ]
adox rcx, r10
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, r10, [ rsi + 0x18 ]
adox r10, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbx, [ rsi + 0x18 ]
adox rbx, rbp
adcx r11, r11
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mulx r13, rbp, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, -0x2 
inc rdx
adox r8, rcx
adox r9, r10
mov rcx, 0x0 
mov r10, rcx
adox r10, rbx
adcx rax, rax
adcx r8, r8
mov rbx, rcx
adox rbx, r12
adcx r9, r9
seto r12b
mov rdx, -0x3 
inc rdx
adox r13, r11
adox r14, rax
adcx r10, r10
adcx rbx, rbx
adox r15, r8
mov rdx, [ rsi + 0x10 ]
mulx rax, r11, rdx
adox r11, r9
adox rax, r10
mov rdx, 0x26 
mulx r9, r8, rax
movzx r10, r12b
adcx r10, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rax, rdx
adox rax, rbx
movzx rdx, r12b
lea rdx, [ rdx + r10 ]
mov r12, 0x26 
xchg rdx, rax
mulx r10, rbx, r12
adox rax, rcx
xor rcx, rcx
adox r8, r13
adox rbx, r14
mov rdx, r12
mulx r13, r12, r11
adcx r12, rbp
adcx r13, r8
mulx r14, rbp, rax
adox rbp, r15
adcx r9, rbx
adcx r10, rbp
adox r14, rcx
adc r14, 0x0
mulx r11, r15, r14
test al, al
adox r15, r12
mov r11, rcx
adox r11, r13
mov [ rdi + 0x8 ], r11
mov rax, rcx
adox rax, r9
mov r8, rcx
adox r8, r10
mov rbx, rcx
cmovo rbx, rdx
adcx r15, rbx
mov [ rdi + 0x0 ], r15
mov [ rdi + 0x18 ], r8
mov [ rdi + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3538
; seed 2649655814196508 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4865 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=200, initial num_batches=31): 462 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.09496402877697842
; number reverted permutation / tried permutation: 346 / 508 =68.110%
; number reverted decision / tried decision: 151 / 491 =30.754%
; validated in 0.449s
