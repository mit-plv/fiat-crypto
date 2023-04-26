SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 192
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x10 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x10 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], rbp
mov [ rsp - 0x40 ], rdi
mulx rdi, rbp, rdx
xor rdx, rdx
adox rbp, rcx
adox r8, rdi
mov rcx, 0xffffffffffffffff 
mov rdx, rbx
mulx rdi, rbx, rcx
mov rdx, rbx
adcx rdx, r14
mov r14, rbx
adcx r14, rdi
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r15
mov [ rsp - 0x30 ], r12
mulx r12, r15, [ rsi + 0x8 ]
adox r15, r9
mov rdx, 0x0 
adox r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r12
mulx r12, r9, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], r15
mov [ rsp - 0x18 ], r8
mulx r8, r15, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox r15, r10
adcx rbx, rdi
adox r9, r8
mov r10, 0x0 
adcx rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx r10, r8, [ rsi + 0x18 ]
adox r8, r12
mov rdx, 0x0 
adox r10, rdx
add r13, rax
adcx rcx, r15
mov r13, -0x3 
inc r13
adox r11, rcx
adcx r14, r9
adcx rbx, r8
adox rbp, r14
adox rbx, [ rsp - 0x18 ]
adcx rdi, r10
mov rdx, [ rsi + 0x0 ]
mulx r12, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r15, [ rsi + 0x8 ]
mov rdx, 0xd838091dd2253531 
mulx r10, r8, r11
mov r10, 0xfffffffefffffc2f 
mov rdx, r10
mulx rcx, r10, r8
seto r14b
inc r13
adox r15, r12
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], r15
mov [ rsp - 0x8 ], rax
mulx rax, r15, rdx
adox r12, r9
mov rdx, [ rsp - 0x38 ]
setc r9b
clc
adcx rdx, [ rsp - 0x30 ]
mov [ rsp + 0x0 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], rbx
mov [ rsp + 0x10 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
adcx r15, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x18 ], rbp
mov [ rsp + 0x20 ], r15
mulx r15, rbp, rdx
adox rbp, r13
adcx rbx, rax
mov rdx, 0xffffffffffffffff 
mulx rax, r13, r8
mov r8, r13
setc dl
clc
adcx r8, rcx
mov rcx, r13
adcx rcx, rax
adcx r13, rax
mov [ rsp + 0x28 ], rbp
setc bpl
clc
mov byte [ rsp + 0x30 ], dl
mov rdx, -0x1 
movzx r14, r14b
adcx r14, rdx
adcx rdi, [ rsp - 0x20 ]
mov r14, 0x0 
adox r15, r14
movzx r9, r9b
movzx r14, r9b
adcx r14, [ rsp - 0x28 ]
inc rdx
adox r10, r11
adox r8, [ rsp + 0x10 ]
setc r10b
clc
adcx r8, [ rsp - 0x48 ]
mov r11, 0xd838091dd2253531 
mov rdx, r11
mulx r9, r11, r8
mov r9, 0xfffffffefffffc2f 
mov rdx, r11
mov [ rsp + 0x38 ], r15
mulx r15, r11, r9
adox rcx, [ rsp + 0x8 ]
adcx r12, rcx
movzx rcx, bpl
lea rcx, [ rcx + rax ]
adox r13, rdi
adox rcx, r14
adcx r13, [ rsp + 0x20 ]
adcx rbx, rcx
mov rax, 0xffffffffffffffff 
mulx rdi, rbp, rax
movzx r14, r10b
mov rdx, 0x0 
adox r14, rdx
mov r10, rbp
mov rcx, -0x3 
inc rcx
adox r10, r15
mov r15, rbp
adox r15, rdi
adox rbp, rdi
adox rdi, rdx
mov rcx, -0x3 
inc rcx
adox r11, r8
movzx r11, byte [ rsp + 0x30 ]
mov r8, [ rsp + 0x18 ]
lea r11, [ r11 + r8 ]
adcx r11, r14
adox r10, r12
adox r15, r13
setc r8b
clc
adcx r10, [ rsp - 0x8 ]
adcx r15, [ rsp - 0x10 ]
adox rbp, rbx
adcx rbp, [ rsp + 0x0 ]
adox rdi, r11
movzx r12, r8b
adox r12, rdx
mov r13, 0xd838091dd2253531 
mov rdx, r13
mulx rbx, r13, r10
mov rdx, r13
mulx r13, rbx, r9
adcx rdi, [ rsp + 0x28 ]
inc rcx
adox rbx, r10
adcx r12, [ rsp + 0x38 ]
mulx r14, rbx, rax
mov r8, rbx
setc r11b
clc
adcx r8, r13
mov r10, rbx
adcx r10, r14
adcx rbx, r14
adox r8, r15
mov r15, 0x0 
adcx r14, r15
adox r10, rbp
adox rbx, rdi
adox r14, r12
movzx rbp, r11b
adox rbp, r15
mov rdx, r8
sub rdx, r9
mov r13, r10
sbb r13, rax
mov rdi, rbx
sbb rdi, rax
mov r11, r14
sbb r11, rax
sbb rbp, 0x00000000
cmovc r13, r10
cmovc rdi, rbx
cmovc r11, r14
mov rbp, [ rsp - 0x50 ]
mov [ rbp + 0x18 ], r11
cmovc rdx, r8
mov [ rbp + 0x10 ], rdi
mov [ rbp + 0x0 ], rdx
mov [ rbp + 0x8 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 192
ret
; cpu 13th Gen Intel(R) Core(TM) i9-13900KF
; ratio 1.7238
; seed 1203677378932072 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 944725 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=205, initial num_batches=31): 73165 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07744581756595835
; number reverted permutation / tried permutation: 75588 / 90100 =83.893%
; number reverted decision / tried decision: 64388 / 89899 =71.623%
; validated in 1.735s
