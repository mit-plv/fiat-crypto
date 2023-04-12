SECTION .text
	GLOBAL fiat_secp256k1_montgomery_mul
fiat_secp256k1_montgomery_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x8 ]
mulx r11, r10, [ rsi + 0x0 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rax + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbp
mov r14, 0xfffffffefffffc2f 
mov rdx, r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r13
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rax + 0x0 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], rdi
mov [ rsp - 0x38 ], r9
mulx r9, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], r9
mov [ rsp - 0x28 ], rdi
mulx rdi, r9, [ rax + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x20 ], rbx
mov [ rsp - 0x18 ], r8
mulx r8, rbx, [ rsi + 0x0 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], rcx
mulx rcx, rdi, [ rsi + 0x8 ]
xor rdx, rdx
adox r10, r12
adox rbx, r11
adox r9, r8
mov r11, 0xffffffffffffffff 
mov rdx, r13
mulx r12, r13, r11
adcx r14, rbp
mov r14, r13
seto bpl
mov rdx, -0x2 
inc rdx
adox r14, r15
mov r15, r13
adox r15, r12
adox r13, r12
adcx r14, r10
seto r8b
inc rdx
adox r14, [ rsp - 0x8 ]
mov r10, 0xd838091dd2253531 
mov rdx, r14
mulx r11, r14, r10
adcx r15, rbx
movzx r11, r8b
lea r11, [ r11 + r12 ]
movzx rbx, bpl
mov r12, [ rsp - 0x10 ]
lea rbx, [ rbx + r12 ]
adcx r13, r9
adcx r11, rbx
mov r12, rdx
mov rdx, [ rax + 0x8 ]
mulx r9, rbp, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mulx rbx, r8, r14
setc r10b
clc
adcx rbp, [ rsp - 0x18 ]
adox rbp, r15
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], rbp
mulx rbp, r15, [ rax + 0x10 ]
adcx r15, r9
adcx rdi, rbp
adox r15, r13
mov rdx, 0xffffffffffffffff 
mulx r9, r13, r14
mov r14, 0x0 
adcx rcx, r14
mov rbp, r13
clc
adcx rbp, rbx
mov rbx, r13
adcx rbx, r9
adox rdi, r11
movzx r11, r10b
adox r11, rcx
adcx r13, r9
setc r10b
clc
adcx r8, r12
adcx rbp, [ rsp + 0x0 ]
adcx rbx, r15
mov rdx, [ rax + 0x0 ]
mulx r12, r8, [ rsi + 0x10 ]
adcx r13, rdi
mov rdx, [ rsi + 0x18 ]
mulx rcx, r15, [ rax + 0x8 ]
mov rdx, [ rax + 0x18 ]
mulx r14, rdi, [ rsi + 0x10 ]
movzx rdx, r10b
lea rdx, [ rdx + r9 ]
adcx rdx, r11
setc r9b
clc
adcx r15, [ rsp - 0x20 ]
movzx r11, r9b
mov r10, 0x0 
adox r11, r10
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], r15
mulx r15, r10, [ rax + 0x10 ]
mov rdx, -0x2 
inc rdx
adox r8, rbp
adcx r10, rcx
seto bpl
inc rdx
adox r12, [ rsp - 0x28 ]
setc cl
clc
mov rdx, -0x1 
movzx rbp, bpl
adcx rbp, rdx
adcx rbx, r12
mov rbp, [ rsp - 0x30 ]
adox rbp, [ rsp - 0x38 ]
mov r12, 0xd838091dd2253531 
mov rdx, r12
mov [ rsp + 0x10 ], r10
mulx r10, r12, r8
mov r10, 0xfffffffefffffc2f 
mov rdx, r10
mov [ rsp + 0x18 ], r15
mulx r15, r10, r12
mov rdx, 0xffffffffffffffff 
mov byte [ rsp + 0x20 ], cl
mov [ rsp + 0x28 ], r11
mulx r11, rcx, r12
setc r12b
clc
adcx r10, r8
adox rdi, [ rsp - 0x48 ]
mov r10, rcx
setc r8b
clc
adcx r10, r15
mov r15, rcx
adcx r15, r11
adcx rcx, r11
mov rdx, 0x0 
adox r14, rdx
adc r11, 0x0
add r8b, 0x7F
adox rbx, r10
adcx rbx, [ rsp - 0x40 ]
setc r8b
clc
mov r10, -0x1 
movzx r12, r12b
adcx r12, r10
adcx r13, rbp
adox r15, r13
adcx rdi, r9
adcx r14, [ rsp + 0x28 ]
setc r9b
clc
movzx r8, r8b
adcx r8, r10
adcx r15, [ rsp + 0x8 ]
adox rcx, rdi
mov r12, 0xd838091dd2253531 
mov rdx, r12
mulx rbp, r12, rbx
mov rbp, 0xfffffffefffffc2f 
mov rdx, r12
mulx r8, r12, rbp
adox r11, r14
movzx r13, r9b
mov rdi, 0x0 
adox r13, rdi
mov r9, rdx
mov rdx, [ rax + 0x18 ]
mulx rdi, r14, [ rsi + 0x18 ]
movzx rdx, byte [ rsp + 0x20 ]
inc r10
mov r10, -0x1 
adox rdx, r10
adox r14, [ rsp + 0x18 ]
mov rdx, 0xffffffffffffffff 
mulx rbp, r10, r9
adcx rcx, [ rsp + 0x10 ]
adcx r14, r11
mov r9, 0x0 
adox rdi, r9
adcx rdi, r13
mov r11, r10
mov r13, -0x3 
inc r13
adox r11, r8
mov r8, r10
adox r8, rbp
setc r13b
clc
adcx r12, rbx
adcx r11, r15
adcx r8, rcx
adox r10, rbp
adcx r10, r14
adox rbp, r9
adcx rbp, rdi
movzx r12, r13b
adc r12, 0x0
mov rbx, r11
mov r15, 0xfffffffefffffc2f 
sub rbx, r15
mov rcx, r8
sbb rcx, rdx
mov r14, r10
sbb r14, rdx
mov r13, rbp
sbb r13, rdx
sbb r12, 0x00000000
cmovc rcx, r8
cmovc rbx, r11
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x8 ], rcx
cmovc r14, r10
mov [ r12 + 0x10 ], r14
cmovc r13, rbp
mov [ r12 + 0x0 ], rbx
mov [ r12 + 0x18 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.7215
; seed 3418854808872228 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1253242 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 79232 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06322162838462164
; number reverted permutation / tried permutation: 67701 / 89860 =75.341%
; number reverted decision / tried decision: 60556 / 90139 =67.181%
; validated in 3.354s
