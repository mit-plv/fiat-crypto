SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r9
mulx r9, rbx, [ rsi + 0x10 ]
xor rdx, rdx
adox r13, r10
adcx rbp, rax
adox rbx, r14
mov rbp, r15
seto al
mov r10, -0x3 
inc r10
adox rbp, r12
adcx rbp, r13
mov r12, r15
adox r12, rdi
adcx r12, rbx
mov rdx, [ rsi + 0x10 ]
mulx r13, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r10, rbx, [ rsi + 0x0 ]
adox r15, rdi
mov rdx, 0x0 
adox rdi, rdx
mov [ rsp - 0x40 ], r8
mov r8, -0x3 
inc r8
adox r14, r10
adox r11, r13
mov rdx, [ rsi + 0x0 ]
mulx r10, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x38 ], r11
mulx r11, r8, [ rsi + 0x18 ]
adox r8, rcx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r8
mulx r8, rcx, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x28 ], r14
mov r14, -0x1 
inc r14
mov r14, -0x1 
movzx rax, al
adox rax, r14
adox r9, r13
mov rax, 0x0 
adox r10, rax
mov r13, -0x3 
inc r13
adox rcx, rbp
movzx rbp, dl
lea rbp, [ rbp + r11 ]
mov r11, 0xd838091dd2253531 
mov rdx, rcx
mulx rax, rcx, r11
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r14, r13, rdx
adcx r15, r9
mov rdx, 0xfffffffefffffc2f 
mulx r11, r9, rcx
adcx rdi, r10
setc r10b
clc
adcx r13, r8
adox r13, r12
mov rdx, [ rsi + 0x8 ]
mulx r8, r12, [ rsi + 0x10 ]
adcx r12, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r14, [ rsi + 0x18 ]
adox r12, r15
adcx r14, r8
mov rdx, 0x0 
adcx rbp, rdx
adox r14, rdi
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx rdi, r15, rcx
movzx rcx, r10b
adox rcx, rbp
mov r10, r15
clc
adcx r10, r11
mov r11, r15
adcx r11, rdi
seto r8b
mov rbp, -0x2 
inc rbp
adox r9, rax
adcx r15, rdi
adox r10, r13
adox r11, r12
mov r9, 0x0 
adcx rdi, r9
clc
adcx rbx, r10
mov rax, 0xd838091dd2253531 
mov rdx, rbx
mulx r13, rbx, rax
mov r13, 0xfffffffefffffc2f 
xchg rdx, rbx
mulx r10, r12, r13
adox r15, r14
adox rdi, rcx
adcx r11, [ rsp - 0x28 ]
adcx r15, [ rsp - 0x38 ]
movzx r14, r8b
adox r14, r9
mov r8, 0xffffffffffffffff 
mulx r9, rcx, r8
adcx rdi, [ rsp - 0x30 ]
mov rdx, rcx
inc rbp
adox rdx, r10
mov r10, rcx
adox r10, r9
adcx r14, [ rsp - 0x20 ]
adox rcx, r9
setc r8b
clc
adcx r12, rbx
adcx rdx, r11
adcx r10, r15
adcx rcx, rdi
mov r12, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rdi, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mulx r13, rbp, [ rsi + 0x18 ]
mov rdx, 0x0 
adox r9, rdx
adcx r9, r14
movzx r14, r8b
adc r14, 0x0
test al, al
adox rbx, rdi
adox rbp, r11
adcx r15, r12
adcx rbx, r10
adox r13, [ rsp - 0x40 ]
adcx rbp, rcx
adcx r13, r9
mov rdx, r15
mulx r8, r15, rax
mov r8, [ rsp - 0x48 ]
mov r12, 0x0 
adox r8, r12
adcx r8, r14
mov r10, 0xfffffffefffffc2f 
xchg rdx, r15
mulx r11, rcx, r10
mov rdi, 0xffffffffffffffff 
mulx r14, r9, rdi
mov rdx, r9
mov rdi, -0x3 
inc rdi
adox rdx, r11
mov r11, r9
adox r11, r14
adox r9, r14
setc dil
clc
adcx rcx, r15
adox r14, r12
adcx rdx, rbx
adcx r11, rbp
adcx r9, r13
adcx r14, r8
movzx rcx, dil
adc rcx, 0x0
mov r15, rdx
sub r15, r10
mov rbx, r11
mov rbp, 0xffffffffffffffff 
sbb rbx, rbp
mov r13, r9
sbb r13, rbp
mov rdi, r14
sbb rdi, rbp
sbb rcx, 0x00000000
cmovc r15, rdx
cmovc r13, r9
cmovc rdi, r14
cmovc rbx, r11
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x18 ], rdi
mov [ rcx + 0x8 ], rbx
mov [ rcx + 0x10 ], r13
mov [ rcx + 0x0 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.6121
; seed 0249651019087320 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1943725 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=83, initial num_batches=31): 111874 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05755649590348429
; number reverted permutation / tried permutation: 74944 / 90118 =83.162%
; number reverted decision / tried decision: 42115 / 89881 =46.856%
; validated in 3.43s
