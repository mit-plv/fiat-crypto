SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, r8
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rbx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x48 ], rcx
mov [ rsp - 0x40 ], r11
mulx r11, rcx, rbx
mov rbx, rcx
xor rdx, rdx
adox rbx, rdi
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r12
mulx r12, rdi, [ rsi + 0x10 ]
mov rdx, rcx
adox rdx, r11
adox rcx, r11
adcx rax, r9
setc r9b
clc
adcx r15, r8
adcx rbx, rax
mov r15, rdx
mov rdx, [ rsi + 0x10 ]
mulx rax, r8, [ rsi + 0x0 ]
seto dl
mov [ rsp - 0x30 ], rdi
mov rdi, -0x1 
inc rdi
mov rdi, -0x1 
movzx r9, r9b
adox r9, rdi
adox r10, r8
adox r13, rax
mov r9, 0x0 
adox r14, r9
mov r8b, dl
mov rdx, [ rsi + 0x8 ]
mulx r9, rax, [ rsi + 0x0 ]
inc rdi
adox rax, rbx
adcx r15, r10
mov rdx, 0xd838091dd2253531 
mulx r10, rbx, rax
mov r10, 0xffffffffffffffff 
mov rdx, rbx
mulx rdi, rbx, r10
adcx rcx, r13
movzx r13, r8b
lea r13, [ r13 + r11 ]
mov r11, rdx
mov rdx, [ rsi + 0x8 ]
mulx r10, r8, rdx
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], rdi
mulx rdi, r12, r11
adcx r13, r14
setc r14b
clc
adcx r8, r9
adox r8, r15
adcx rbp, r10
adox rbp, rcx
mov rdx, [ rsi + 0x18 ]
mulx r15, r9, [ rsi + 0x8 ]
adcx r9, [ rsp - 0x38 ]
adox r9, r13
mov rdx, 0x0 
adcx r15, rdx
mov r11, rbx
clc
adcx r11, rdi
mov rcx, rbx
adcx rcx, [ rsp - 0x20 ]
adcx rbx, [ rsp - 0x20 ]
mov rdx, [ rsi + 0x8 ]
mulx rdi, r10, [ rsi + 0x10 ]
setc dl
clc
adcx r12, rax
seto r12b
mov rax, -0x2 
inc rax
adox r10, [ rsp - 0x28 ]
adcx r11, r8
seto r13b
inc rax
mov r8, -0x1 
movzx r14, r14b
movzx r12, r12b
adox r12, r8
adox r15, r14
adcx rcx, rbp
movzx r14, dl
mov rbp, [ rsp - 0x20 ]
lea r14, [ r14 + rbp ]
adcx rbx, r9
mov rdx, [ rsi + 0x10 ]
mulx r12, rbp, rdx
adcx r14, r15
setc dl
clc
adcx r11, [ rsp - 0x30 ]
mov r9, 0xd838091dd2253531 
xchg rdx, r9
mulx rax, r15, r11
seto al
inc r8
mov r8, -0x1 
movzx r13, r13b
adox r13, r8
adox rdi, rbp
adcx r10, rcx
mov r13, 0xffffffffffffffff 
mov rdx, r15
mulx rcx, r15, r13
adox r12, [ rsp - 0x40 ]
adcx rdi, rbx
adcx r12, r14
movzx rbx, r9b
movzx rax, al
lea rbx, [ rbx + rax ]
mov rax, [ rsp - 0x48 ]
mov rbp, 0x0 
adox rax, rbp
mov r9, rdx
mov rdx, [ rsi + 0x18 ]
mulx rbp, r14, [ rsi + 0x0 ]
mov rdx, 0xfffffffefffffc2f 
mulx r13, r8, r9
mov r9, r15
mov rdx, -0x2 
inc rdx
adox r9, r13
adcx rax, rbx
mov rdx, [ rsi + 0x18 ]
mulx r13, rbx, [ rsi + 0x8 ]
setc dl
clc
adcx r8, r11
mov r8, r15
adox r8, rcx
adox r15, rcx
adcx r9, r10
mov r11, 0x0 
adox rcx, r11
adcx r8, rdi
adcx r15, r12
adcx rcx, rax
mov r10, -0x3 
inc r10
adox rbx, rbp
movzx rdi, dl
adcx rdi, r11
clc
adcx r14, r9
adcx rbx, r8
mov rdx, [ rsi + 0x10 ]
mulx rbp, r12, [ rsi + 0x18 ]
adox r12, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, rax, rdx
adox rax, rbp
adox r13, r11
adcx r12, r15
adcx rax, rcx
mov rdx, 0xd838091dd2253531 
mulx r8, r9, r14
adcx r13, rdi
mov r8, 0xffffffffffffffff 
mov rdx, r9
mulx r15, r9, r8
mov rcx, 0xfffffffefffffc2f 
mulx rbp, rdi, rcx
mov rdx, r9
mov r10, -0x3 
inc r10
adox rdx, rbp
mov rbp, r9
adox rbp, r15
setc r10b
clc
adcx rdi, r14
adcx rdx, rbx
adox r9, r15
adcx rbp, r12
adcx r9, rax
adox r15, r11
adcx r15, r13
movzx rdi, r10b
adc rdi, 0x0
mov r14, rdx
sub r14, rcx
mov rbx, rbp
sbb rbx, r8
mov r12, r9
sbb r12, r8
mov rax, r15
sbb rax, r8
sbb rdi, 0x00000000
cmovc rax, r15
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x18 ], rax
cmovc r12, r9
cmovc r14, rdx
mov [ rdi + 0x10 ], r12
mov [ rdi + 0x0 ], r14
cmovc rbx, rbp
mov [ rdi + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5860
; seed 0101953203649838 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1133012 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=127, initial num_batches=31): 74668 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06590221462791215
; number reverted permutation / tried permutation: 69307 / 89674 =77.288%
; number reverted decision / tried decision: 60661 / 90325 =67.159%
; validated in 3.146s
