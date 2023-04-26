SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x10 ]
xor rdx, rdx
adox r11, r10
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, [ rsi + 0x18 ]
adox r8, rcx
adox r10, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rsi + 0x10 ]
adcx rax, rax
adcx r11, r11
adox rcx, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r9, rdx
mov [ rsp - 0x70 ], r12
mov r12, -0x3 
inc r12
adox rbx, r8
adox rbp, r10
adcx rbx, rbx
mov r8, rdx
adox r8, rcx
adcx rbp, rbp
adcx r8, r8
mov rdx, [ rsi + 0x8 ]
mulx rcx, r10, rdx
mov rdx, 0x0 
mov [ rsp - 0x68 ], r13
mov r13, rdx
adox r13, r9
adcx r13, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x60 ], r14
mulx r14, r9, rdx
seto dl
inc r12
adox r14, rax
adox r10, r11
movzx rax, dl
mov r11, 0x0 
adcx rax, r11
movzx r11, dl
lea r11, [ r11 + rax ]
adox rcx, rbx
mov rdx, [ rsi + 0x10 ]
mulx rax, rbx, rdx
adox rbx, rbp
adox rax, r8
mov rdx, 0x26 
mulx r8, rbp, rax
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mulx r15, rax, rdx
adox rax, r13
adox r11, r15
mov rdx, 0x26 
mulx r15, r13, r11
mulx r12, r11, rax
mov [ rsp - 0x50 ], rdi
mulx rdi, rax, rbx
xor rbx, rbx
adox rbp, r14
adcx rax, r9
adcx rdi, rbp
adox r11, r10
adcx r8, r11
adox r13, rcx
adox r15, rbx
adcx r12, r13
adc r15, 0x0
mulx r14, r9, r15
xor r14, r14
adox r9, rax
mov rbx, r14
adox rbx, rdi
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], rbx
mov rcx, r14
adox rcx, r8
mov rbp, r14
adox rbp, r12
mov [ r10 + 0x10 ], rcx
mov [ r10 + 0x18 ], rbp
mov rax, r14
cmovo rax, rdx
adcx r9, rax
mov [ r10 + 0x0 ], r9
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.4232
; seed 0405360427430591 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 398660 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=540, initial num_batches=31): 65422 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.16410475091556714
; number reverted permutation / tried permutation: 75924 / 89842 =84.508%
; number reverted decision / tried decision: 54335 / 90157 =60.267%
; validated in 0.227s
