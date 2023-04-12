SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov r13, 0xfffffffefffffc2f 
mov rdx, r12
mov [ rsp - 0x60 ], r14
mulx r14, r12, r13
mov [ rsp - 0x58 ], r15
mov r15, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r13, [ rsi + 0x10 ]
xor rdx, rdx
adox r8, r10
mov r10, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp - 0x48 ], rdi
mulx rdi, r15, r10
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r13
mulx r13, r10, rdx
mov rdx, r15
adcx rdx, r14
mov r14, r15
adcx r14, rdi
mov [ rsp - 0x38 ], r13
mov r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r10
mov [ rsp - 0x28 ], rcx
mulx rcx, r10, [ rsi + 0x8 ]
adcx r15, rdi
mov rdx, 0x0 
adcx rdi, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rcx
mov [ rsp - 0x18 ], r10
mulx r10, rcx, [ rsi + 0x18 ]
adox rbx, r9
clc
adcx r12, rax
adcx r13, r8
adcx r14, rbx
adox rcx, rbp
mov rdx, [ rsi + 0x0 ]
mulx rax, r12, [ rsi + 0x8 ]
seto dl
mov r9, -0x2 
inc r9
adox r12, r13
adcx r15, rcx
movzx rbp, dl
lea rbp, [ rbp + r10 ]
adcx rdi, rbp
mov r8, 0xd838091dd2253531 
mov rdx, r8
mulx r10, r8, r12
mov rdx, [ rsi + 0x8 ]
mulx rbx, r10, [ rsi + 0x10 ]
setc dl
clc
adcx r11, rax
adcx r10, [ rsp - 0x28 ]
adox r11, r14
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mulx rcx, r14, [ rsi + 0x18 ]
adox r10, r15
adcx r14, rbx
mov rdx, 0x0 
adcx rcx, rdx
adox r14, rdi
mov rax, 0xfffffffefffffc2f 
mov rdx, rax
mulx r15, rax, r8
mov rbp, 0xffffffffffffffff 
mov rdx, r8
mulx rdi, r8, rbp
movzx rdx, r13b
adox rdx, rcx
mov r13, r8
clc
adcx r13, r15
mov rbx, r8
adcx rbx, rdi
adcx r8, rdi
setc cl
clc
adcx rax, r12
adcx r13, r11
adcx rbx, r10
adcx r8, r14
seto al
inc r9
adox r13, [ rsp - 0x40 ]
mov r12, 0xd838091dd2253531 
xchg rdx, r12
mulx r10, r11, r13
mov rdx, [ rsi + 0x10 ]
mulx r14, r10, [ rsi + 0x8 ]
movzx rdx, cl
lea rdx, [ rdx + rdi ]
mov r15, 0xfffffffefffffc2f 
xchg rdx, r15
mulx rcx, rdi, r11
adcx r15, r12
setc r12b
clc
adcx r10, [ rsp - 0x48 ]
adox r10, rbx
movzx rbx, r12b
movzx rax, al
lea rbx, [ rbx + rax ]
mov rdx, [ rsi + 0x10 ]
mulx r12, rax, rdx
adcx rax, r14
adox rax, r8
mov rdx, [ rsi + 0x10 ]
mulx r14, r8, [ rsi + 0x18 ]
adcx r8, r12
adox r8, r15
adcx r14, r9
adox r14, rbx
mov rdx, r11
mulx r15, r11, rbp
mov rdx, r11
clc
adcx rdx, rcx
mov rcx, r11
adcx rcx, r15
adcx r11, r15
adcx r15, r9
clc
adcx rdi, r13
adcx rdx, r10
mov rdi, rdx
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, [ rsi + 0x18 ]
seto dl
mov rbx, -0x3 
inc rbx
adox r13, rdi
adcx rcx, rax
adcx r11, r8
mov r12, 0xd838091dd2253531 
xchg rdx, r13
mulx r8, rax, r12
adcx r15, r14
mov r8, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r14, [ rsi + 0x10 ]
movzx rdx, r13b
adcx rdx, r9
clc
adcx r10, [ rsp - 0x18 ]
adox r10, rcx
adcx r14, [ rsp - 0x20 ]
adox r14, r11
adcx rdi, [ rsp - 0x30 ]
mov r13, [ rsp - 0x38 ]
adcx r13, r9
xchg rdx, rbp
mulx r11, rcx, rax
adox rdi, r15
adox r13, rbp
mov r15, 0xfffffffefffffc2f 
mov rdx, rax
mulx rbp, rax, r15
mov rdx, rcx
clc
adcx rdx, rbp
mov rbp, rcx
adcx rbp, r11
adcx rcx, r11
adcx r11, r9
clc
adcx rax, r8
adcx rdx, r10
adcx rbp, r14
adcx rcx, rdi
adcx r11, r13
seto al
adc al, 0x0
movzx rax, al
mov r8, rdx
sub r8, r15
mov r10, rbp
mov r14, 0xffffffffffffffff 
sbb r10, r14
mov rdi, rcx
sbb rdi, r14
mov r13, r11
sbb r13, r14
movzx rbx, al
sbb rbx, 0x00000000
cmovc rdi, rcx
cmovc r13, r11
cmovc r8, rdx
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x0 ], r8
mov [ rbx + 0x18 ], r13
cmovc r10, rbp
mov [ rbx + 0x8 ], r10
mov [ rbx + 0x10 ], rdi
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.6716
; seed 4210775200736669 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 946530 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=116, initial num_batches=31): 62969 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06652615342355762
; number reverted permutation / tried permutation: 69864 / 90558 =77.148%
; number reverted decision / tried decision: 51927 / 89441 =58.057%
; validated in 2.023s
