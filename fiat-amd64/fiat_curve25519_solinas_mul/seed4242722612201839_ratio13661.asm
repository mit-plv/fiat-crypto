SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rax + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r10
mulx r10, r13, [ rsi + 0x0 ]
xor rdx, rdx
adox r15, r10
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r13
mulx r13, r10, [ rax + 0x8 ]
adcx r10, r15
adox r9, r11
mov rdx, [ rsi + 0x8 ]
mulx r15, r11, [ rax + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x30 ], r12
mov [ rsp - 0x28 ], rcx
mulx rcx, r12, [ rsi + 0x8 ]
setc dl
clc
adcx r11, r14
setc r14b
clc
mov [ rsp - 0x20 ], r12
mov r12, -0x1 
movzx rdx, dl
adcx rdx, r12
adcx r9, rdi
mov rdx, [ rsi + 0x10 ]
mulx r12, rdi, [ rax + 0x0 ]
mov rdx, 0x0 
adox rcx, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r15
mulx r15, r11, [ rax + 0x18 ]
mov rdx, 0x0 
mov [ rsp - 0x8 ], r11
mov r11, rdx
adcx r11, rcx
adc r15, 0x0
test al, al
adox rdi, r8
adox r12, r10
adcx rbp, rdi
mov rdx, [ rax + 0x10 ]
mulx r10, r8, [ rsi + 0x8 ]
adcx r8, r12
mov rdx, [ rsi + 0x10 ]
mulx rdi, rcx, [ rax + 0x10 ]
adox rcx, r9
mov rdx, [ rsi + 0x18 ]
mulx r12, r9, [ rax + 0x10 ]
adox r9, r11
adcx r13, rcx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rax + 0x18 ]
adcx rbx, r9
mov rdx, 0x0 
mov r9, rdx
adox r9, r15
mov r15, rdx
adcx r15, r9
adox rcx, rdx
adcx rcx, rdx
add r14b, 0xFF
adcx rbp, [ rsp - 0x10 ]
mov r14, [ rsp - 0x18 ]
adox r14, [ rsp - 0x28 ]
adcx r8, [ rsp - 0x30 ]
adcx r13, [ rsp - 0x20 ]
adox rbp, [ rsp - 0x38 ]
adox r8, [ rsp - 0x40 ]
adox r10, r13
mov r9, 0x26 
mov rdx, r9
mulx r13, r9, r10
adcx rbx, [ rsp - 0x8 ]
adcx r11, r15
adox rdi, rbx
mov r15, 0x0 
adcx rcx, r15
adox r12, r11
mulx rbx, r10, r12
adox rcx, r15
add r9, [ rsp - 0x48 ]
mulx r12, r11, rdi
mov rdi, -0x3 
inc rdi
adox r11, r14
adcx r13, r11
mulx r11, r14, rcx
adox r10, rbp
adox r14, r8
adox r11, r15
adcx r12, r10
adcx rbx, r14
adc r11, 0x0
mulx r8, rbp, r11
xor r8, r8
adox rbp, r9
mov r15, r8
adox r15, r13
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x8 ], r15
mov r9, r8
adox r9, r12
mov r13, r8
adox r13, rbx
mov r10, r8
cmovo r10, rdx
mov [ rcx + 0x10 ], r9
adcx rbp, r10
mov [ rcx + 0x18 ], r13
mov [ rcx + 0x0 ], rbp
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.3661
; seed 4242722612201839 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7607 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=171, initial num_batches=31): 656 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.08623636124622058
; number reverted permutation / tried permutation: 299 / 517 =57.834%
; number reverted decision / tried decision: 242 / 482 =50.207%
; validated in 0.636s
