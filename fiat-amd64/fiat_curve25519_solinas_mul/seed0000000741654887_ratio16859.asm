SECTION .text
	GLOBAL fiat_curve25519_solinas_mul
fiat_curve25519_solinas_mul:
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x48 ], rdi
mov [ rsp - 0x40 ], r13
mulx r13, rdi, [ rsi + 0x18 ]
xor rdx, rdx
adox r9, r12
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x38 ], rbp
mulx rbp, r12, [ rsi + 0x10 ]
adox rdi, r14
adcx r12, r9
adcx rbx, rdi
mov rdx, [ rax + 0x18 ]
mulx r9, r14, [ rsi + 0x10 ]
mov rdx, 0x0 
adox r8, rdx
mov rdi, rdx
adcx rdi, r8
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x30 ], r10
mulx r10, r8, [ rsi + 0x10 ]
adc r9, 0x0
add r8, r11
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], r14
mulx r14, r11, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r13
mulx r13, rcx, [ rax + 0x10 ]
adcx r10, r12
mov rdx, -0x2 
inc rdx
adox r11, r8
adcx rcx, rbx
mov rdx, [ rax + 0x10 ]
mulx rbx, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], rbx
mulx rbx, r8, [ rsi + 0x0 ]
adcx r12, rdi
adox r15, r10
adox rbp, rcx
mov rdx, 0x0 
mov rdi, rdx
adcx rdi, r9
mov rdx, [ rax + 0x0 ]
mulx r10, r9, [ rsi + 0x8 ]
setc dl
clc
adcx r9, rbx
adcx r10, r11
adcx r14, r15
adox r12, [ rsp - 0x18 ]
adcx rbp, [ rsp - 0x20 ]
adcx r12, [ rsp - 0x28 ]
mov r11, 0x0 
mov rcx, r11
adox rcx, rdi
seto bl
mov r15, -0x3 
inc r15
adox r9, [ rsp - 0x30 ]
adox r10, [ rsp - 0x38 ]
mov dil, dl
mov rdx, [ rsi + 0x18 ]
mulx r15, r11, [ rax + 0x18 ]
movzx rdx, dil
lea rdx, [ rdx + r15 ]
adox r14, [ rsp - 0x40 ]
adox rbp, [ rsp - 0x48 ]
adcx r11, rcx
adox r13, r12
adox r11, [ rsp - 0x10 ]
mov rdi, 0x0 
movzx rbx, bl
lea rdx, [ rdx + rdi ]
lea rdx, [ rdx + rbx ]
adcx rdx, rdi
adox rdx, rdi
mov r12, 0x26 
xchg rdx, r12
mulx rcx, rbx, r13
mulx r13, r15, r11
mulx rdi, r11, rbp
test al, al
adox rbx, r9
adcx r11, r8
adcx rdi, rbx
adox r15, r10
adcx rcx, r15
mulx r9, r8, r12
adox r8, r14
mov r10, 0x0 
adox r9, r10
adcx r13, r8
adc r9, 0x0
mulx rbp, r14, r9
xor rbp, rbp
adox r14, r11
mov r10, rbp
adox r10, rdi
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], r10
mov rbx, rbp
adox rbx, rcx
mov r11, rbp
adox r11, r13
mov [ r12 + 0x18 ], r11
mov rdi, rbp
cmovo rdi, rdx
mov [ r12 + 0x10 ], rbx
adcx r14, rdi
mov [ r12 + 0x0 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.6859
; seed 1953586900750229 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 758699 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=178, initial num_batches=31): 69846 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.09206022414686194
; number reverted permutation / tried permutation: 65951 / 90287 =73.046%
; number reverted decision / tried decision: 37795 / 89712 =42.129%
; validated in 0.429s
