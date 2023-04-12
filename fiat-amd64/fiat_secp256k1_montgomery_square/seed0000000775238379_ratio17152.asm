SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 136
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mulx r9, r8, rax
mov r9, 0xffffffffffffffff 
mov rdx, r8
mov [ rsp - 0x80 ], rbx
mulx rbx, r8, r9
mov [ rsp - 0x78 ], rbp
mov rbp, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbp
mov rbp, r8
add rbp, r15
mov r15, r8
adcx r15, rbx
adcx r8, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mulx rdi, r9, [ rsi + 0x8 ]
adc rbx, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r9
mulx r9, rdi, [ rsi + 0x0 ]
test al, al
adox r12, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x18 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r8
mov [ rsp - 0x8 ], r12
mulx r12, r8, [ rsi + 0x8 ]
adox r9, r13
adcx r11, r10
adox r8, rbx
mov rdx, [ rsi + 0x0 ]
mulx r13, r10, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x0 ], r8
mulx r8, rbx, [ rsi + 0x18 ]
adcx r10, rcx
adcx rbx, r13
mov rdx, 0x0 
adcx r8, rdx
adox r12, rdx
test al, al
adox r14, rax
adox rbp, r11
adox r15, r10
adcx rdi, rbp
adcx r15, [ rsp - 0x8 ]
mov r14, 0xd838091dd2253531 
mov rdx, rdi
mulx rax, rdi, r14
adox rbx, [ rsp - 0x10 ]
adcx r9, rbx
adox r8, [ rsp - 0x18 ]
mov rax, 0xffffffffffffffff 
xchg rdx, rax
mulx r11, rcx, rdi
mov r13, 0xfffffffefffffc2f 
mov rdx, r13
mulx r10, r13, rdi
mov rbp, rcx
seto dil
mov rbx, -0x2 
inc rbx
adox rbp, r10
mov r10, rcx
adox r10, r11
adox rcx, r11
mov rbx, 0x0 
adox r11, rbx
mov rdx, -0x3 
inc rdx
adox r13, rax
adox rbp, r15
adox r10, r9
adcx r8, [ rsp + 0x0 ]
adox rcx, r8
movzx r13, dil
adcx r13, r12
adox r11, r13
mov rdx, [ rsi + 0x10 ]
mulx rax, r12, [ rsi + 0x0 ]
seto dl
mov r15, -0x3 
inc r15
adox r12, rbp
xchg rdx, r12
mulx rdi, r9, r14
movzx rdi, r12b
adcx rdi, rbx
clc
adcx rax, [ rsp - 0x20 ]
mov rbp, [ rsp - 0x28 ]
adcx rbp, [ rsp - 0x30 ]
adox rax, r10
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r8, [ rsi + 0x10 ]
adcx r8, [ rsp - 0x38 ]
adox rbp, rcx
mov rdx, 0xffffffffffffffff 
mulx r12, rcx, r9
adox r8, r11
adcx r13, rbx
mov r11, 0xfffffffefffffc2f 
mov rdx, r11
mulx rbx, r11, r9
mov r9, rcx
clc
adcx r9, rbx
mov rbx, rcx
adcx rbx, r12
adcx rcx, r12
setc r15b
clc
adcx r11, r10
adcx r9, rax
adcx rbx, rbp
adox r13, rdi
adcx rcx, r8
movzx r11, r15b
lea r11, [ r11 + r12 ]
adcx r11, r13
mov rdx, [ rsi + 0x18 ]
mulx rdi, r10, [ rsi + 0x0 ]
seto dl
mov rax, -0x2 
inc rax
adox r10, r9
mov bpl, dl
mov rdx, [ rsi + 0x18 ]
mulx r8, r12, [ rsi + 0x8 ]
movzx rdx, bpl
mov r15, 0x0 
adcx rdx, r15
clc
adcx r12, rdi
adox r12, rbx
adcx r8, [ rsp - 0x40 ]
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, rbx, rdx
adox r8, rcx
mov rdx, r14
mulx r13, r14, r10
adcx rbx, [ rsp - 0x48 ]
adox rbx, r11
mov r13, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, r13
adcx rbp, r15
mov r11, 0xfffffffefffffc2f 
mulx r15, rdi, r11
clc
adcx rdi, r10
adox rbp, r9
mov rdi, r14
setc r10b
clc
adcx rdi, r15
mov r9, r14
adcx r9, rcx
adcx r14, rcx
seto dl
inc rax
mov r15, -0x1 
movzx r10, r10b
adox r10, r15
adox r12, rdi
adox r9, r8
adox r14, rbx
adcx rcx, rax
adox rcx, rbp
seto r8b
mov rbx, r12
sub rbx, r11
movzx r10, r8b
movzx rdx, dl
lea r10, [ r10 + rdx ]
mov rdx, r9
sbb rdx, r13
mov rbp, r14
sbb rbp, r13
mov rdi, rcx
sbb rdi, r13
sbb r10, 0x00000000
cmovc rbp, r14
cmovc rdx, r9
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x8 ], rdx
mov [ r10 + 0x10 ], rbp
cmovc rdi, rcx
cmovc rbx, r12
mov [ r10 + 0x18 ], rdi
mov [ r10 + 0x0 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 136
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.7152
; seed 0136897850233349 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1201669 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 75663 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06296492628169655
; number reverted permutation / tried permutation: 68810 / 89881 =76.557%
; number reverted decision / tried decision: 45314 / 90118 =50.283%
; validated in 2.651s
