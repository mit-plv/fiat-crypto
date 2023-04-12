SECTION .text
	GLOBAL fiat_curve25519_solinas_square
fiat_curve25519_solinas_square:
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
xor rdx, rdx
adox rax, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
adcx rbx, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mulx r12, r10, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
adox rbx, rbx
adcx r15, rbp
adcx r10, rdi
mov rdx, [ rsi + 0x10 ]
mulx rdi, rbp, [ rsi + 0x18 ]
seto dl
mov [ rsp - 0x48 ], r8
mov r8, -0x2 
inc r8
adox r9, rax
adcx rbp, r12
mov rax, 0x0 
adcx rdi, rax
clc
adcx r13, r15
adcx r14, r10
mov r12, rax
adcx r12, rbp
mov r15, rax
adcx r15, rdi
setc r10b
clc
movzx rdx, dl
adcx rdx, r8
adcx r13, r13
adcx r14, r14
adox r11, rbx
mov rdx, [ rsi + 0x10 ]
mulx rbp, rbx, rdx
adox rcx, r13
adox rbx, r14
adcx r12, r12
adox rbp, r12
adcx r15, r15
mov rdx, [ rsi + 0x18 ]
mulx r13, rdi, rdx
adox rdi, r15
mov rdx, 0x26 
mulx r12, r14, rbp
movzx rbp, r10b
adcx rbp, rax
mulx rax, r15, rdi
movzx rdi, r10b
lea rdi, [ rdi + rbp ]
adox rdi, r13
mulx r13, r10, rbx
mulx rbp, rbx, rdi
xor rdi, rdi
adox r14, r9
adcx r10, [ rsp - 0x48 ]
adcx r13, r14
adox r15, r11
adcx r12, r15
adox rbx, rcx
adox rbp, rdi
adcx rax, rbx
adc rbp, 0x0
mulx r11, r9, rbp
xor r11, r11
adox r9, r10
mov rdi, r11
adox rdi, r13
mov rcx, r11
adox rcx, r12
mov r14, r11
adox r14, rax
mov r10, r11
cmovo r10, rdx
adcx r9, r10
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x10 ], rcx
mov [ r13 + 0x18 ], r14
mov [ r13 + 0x0 ], r9
mov [ r13 + 0x8 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.3140
; seed 4275833522231209 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 5154 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=499, initial num_batches=31): 757 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.14687621265036865
; number reverted permutation / tried permutation: 366 / 514 =71.206%
; number reverted decision / tried decision: 286 / 485 =58.969%
; validated in 0.554s
