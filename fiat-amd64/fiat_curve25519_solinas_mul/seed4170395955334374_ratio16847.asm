SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
sub rsp, 144
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x10 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x48 ], r14
mov [ rsp - 0x40 ], r10
mulx r10, r14, [ rsi + 0x8 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], rbp
mulx rbp, r15, [ rsi + 0x0 ]
xor rdx, rdx
adox rcx, r11
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r15
mulx r15, r11, [ rax + 0x8 ]
adox r11, rbp
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rbx
mulx rbx, rbp, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r10
mov [ rsp - 0x10 ], r15
mulx r15, r10, [ rax + 0x18 ]
adcx rbp, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r10
mulx r10, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x0 ], rcx
mov [ rsp + 0x8 ], r14
mulx r14, rcx, [ rax + 0x0 ]
mov rdx, 0x0 
adox r12, rdx
adcx r8, r11
mov r11, rdx
adcx r11, r12
mov r12, -0x3 
inc r12
adox rcx, r10
adcx r15, rdx
adox r14, rbp
mov rdx, [ rsi + 0x10 ]
mulx r10, rbp, [ rax + 0x10 ]
adox rbp, r8
adox r13, r11
mov rdx, [ rax + 0x0 ]
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, 0x0 
mov r12, rdx
adox r12, r15
adox rdi, rdx
add r9, rcx
mov rdx, [ rax + 0x10 ]
mulx r15, rcx, [ rsi + 0x8 ]
adcx rcx, r14
adcx rbx, rbp
mov rdx, -0x2 
inc rdx
adox r11, [ rsp + 0x8 ]
adcx r13, [ rsp - 0x10 ]
mov r14, 0x0 
mov rbp, r14
adcx rbp, r12
adcx rdi, r14
adox r9, [ rsp - 0x18 ]
adox rcx, [ rsp - 0x20 ]
adox rbx, [ rsp - 0x30 ]
adox r13, [ rsp - 0x8 ]
clc
adcx r11, [ rsp + 0x0 ]
adox rbp, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x40 ]
adcx rcx, [ rsp - 0x28 ]
adcx r15, rbx
adcx r10, r13
mov r12, 0x26 
mov rdx, r12
mulx rbx, r12, r10
adox rdi, r14
adcx rbp, [ rsp - 0x48 ]
mulx r10, r13, rbp
adcx rdi, r14
mulx r14, rbp, r15
test al, al
adox rbp, r8
adcx r12, r11
adcx r13, r9
mulx r11, r8, rdi
adox r14, r12
adcx r8, rcx
adox rbx, r13
mov r9, 0x0 
adcx r11, r9
adox r10, r8
adox r11, r9
mulx r15, rcx, r11
xor r15, r15
adox rcx, rbp
mov r9, r15
adox r9, r14
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r9
mov rbp, r15
adox rbp, rbx
mov [ rdi + 0x10 ], rbp
mov r12, r15
adox r12, r10
mov r13, r15
cmovo r13, rdx
adcx rcx, r13
mov [ rdi + 0x18 ], r12
mov [ rdi + 0x0 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.6847
; seed 4170395955334374 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 4939 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=215, initial num_batches=31): 384 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.0777485320915165
; number reverted permutation / tried permutation: 376 / 496 =75.806%
; number reverted decision / tried decision: 294 / 503 =58.449%
; validated in 0.498s
