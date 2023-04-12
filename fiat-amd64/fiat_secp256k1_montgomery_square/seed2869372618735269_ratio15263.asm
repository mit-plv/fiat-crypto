SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 216
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rcx
mov [ rsp - 0x38 ], r8
mulx r8, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r14
mov [ rsp - 0x28 ], r10
mulx r10, r14, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x20 ], r14
mov [ rsp - 0x18 ], r9
mulx r9, r14, rdi
xor r9, r9
adox rcx, r10
adcx rbx, r15
mov rdx, [ rsi + 0x18 ]
mulx r10, r15, [ rsi + 0x8 ]
adcx r12, rbp
mov rdx, [ rsi + 0x18 ]
mulx r9, rbp, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], rbp
mov [ rsp - 0x8 ], rcx
mulx rcx, rbp, [ rsi + 0x18 ]
setc dl
clc
adcx r15, r9
adcx rbp, r10
mov r10b, dl
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], rbp
mulx rbp, r9, rdx
adox rax, r8
mov rdx, 0xfffffffefffffc2f 
mov [ rsp + 0x8 ], r15
mulx r15, r8, r14
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], rax
mov [ rsp + 0x18 ], r12
mulx r12, rax, rdx
adcx r9, rcx
mov rdx, 0x0 
adcx rbp, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x20 ], rbp
mulx rbp, rcx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x28 ], r9
mov [ rsp + 0x30 ], rbp
mulx rbp, r9, [ rsi + 0x10 ]
clc
mov rdx, -0x1 
movzx r10, r10b
adcx r10, rdx
adcx r13, r11
setc r11b
clc
adcx rax, [ rsp - 0x18 ]
adox rcx, [ rsp - 0x28 ]
mov r10, 0xffffffffffffffff 
mov rdx, r14
mov [ rsp + 0x38 ], rcx
mulx rcx, r14, r10
adcx r9, r12
adcx rbp, [ rsp - 0x30 ]
mov rdx, r14
setc r12b
clc
adcx rdx, r15
mov r15, r14
adcx r15, rcx
adcx r14, rcx
setc r10b
clc
adcx r8, rdi
adcx rdx, rbx
seto r8b
mov rdi, -0x2 
inc rdi
adox rdx, [ rsp - 0x38 ]
mov rbx, 0xd838091dd2253531 
mov byte [ rsp + 0x40 ], r8b
mulx r8, rdi, rbx
adcx r15, [ rsp + 0x18 ]
adox rax, r15
mov r8, 0xfffffffefffffc2f 
xchg rdx, r8
mulx rbx, r15, rdi
adcx r14, r13
adox r9, r14
movzx r13, r10b
lea r13, [ r13 + rcx ]
movzx rcx, r11b
mov r10, [ rsp - 0x40 ]
lea rcx, [ rcx + r10 ]
seto r10b
mov r11, -0x2 
inc r11
adox r15, r8
adcx r13, rcx
mov r15, 0xffffffffffffffff 
mov rdx, r15
mulx r8, r15, rdi
mov rdi, r15
setc r14b
clc
adcx rdi, rbx
mov rbx, r15
adcx rbx, r8
adcx r15, r8
adox rdi, rax
setc al
clc
adcx rdi, [ rsp - 0x20 ]
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r11, rcx, rdi
mov r11, 0xffffffffffffffff 
mov rdx, r11
mov byte [ rsp + 0x48 ], r14b
mulx r14, r11, rcx
movzx rdx, r12b
mov [ rsp + 0x50 ], r14
mov r14, [ rsp - 0x48 ]
lea rdx, [ rdx + r14 ]
movzx r14, al
lea r14, [ r14 + r8 ]
adox rbx, r9
adcx rbx, [ rsp - 0x8 ]
setc r12b
clc
mov r9, -0x1 
movzx r10, r10b
adcx r10, r9
adcx r13, rbp
adox r15, r13
movzx rbp, byte [ rsp + 0x48 ]
adcx rbp, rdx
mov r10, 0xfffffffefffffc2f 
mov rdx, r10
mulx r8, r10, rcx
setc al
clc
adcx r10, rdi
mov r10, r11
setc dil
clc
adcx r10, r8
adox r14, rbp
movzx rcx, al
mov r13, 0x0 
adox rcx, r13
mov rax, r11
adcx rax, [ rsp + 0x50 ]
adcx r11, [ rsp + 0x50 ]
mov rbp, [ rsp + 0x50 ]
adc rbp, 0x0
add r12b, 0xFF
adcx r15, [ rsp + 0x10 ]
movzx r12, byte [ rsp + 0x40 ]
adox r12, [ rsp + 0x30 ]
inc r9
mov r13, -0x1 
movzx rdi, dil
adox rdi, r13
adox rbx, r10
adox rax, r15
adcx r14, [ rsp + 0x38 ]
adox r11, r14
adcx r12, rcx
adox rbp, r12
seto r8b
mov rdi, -0x3 
inc rdi
adox rbx, [ rsp - 0x10 ]
movzx r10, r8b
adcx r10, r9
mov rcx, 0xd838091dd2253531 
mov rdx, rcx
mulx r15, rcx, rbx
mov r15, 0xffffffffffffffff 
mov rdx, rcx
mulx r14, rcx, r15
mov r12, 0xfffffffefffffc2f 
mulx r9, r8, r12
adox rax, [ rsp + 0x8 ]
adox r11, [ rsp + 0x0 ]
mov rdx, rcx
clc
adcx rdx, r9
mov r9, rcx
adcx r9, r14
adcx rcx, r14
mov rdi, 0x0 
adcx r14, rdi
adox rbp, [ rsp + 0x28 ]
clc
adcx r8, rbx
adcx rdx, rax
adcx r9, r11
adox r10, [ rsp + 0x20 ]
adcx rcx, rbp
adcx r14, r10
seto r8b
adc r8b, 0x0
movzx r8, r8b
mov rbx, rdx
sub rbx, r12
mov rax, r9
sbb rax, r15
mov r11, rcx
sbb r11, r15
mov rbp, r14
sbb rbp, r15
movzx r10, r8b
sbb r10, 0x00000000
cmovc rax, r9
cmovc r11, rcx
cmovc rbx, rdx
cmovc rbp, r14
mov r10, [ rsp - 0x50 ]
mov [ r10 + 0x18 ], rbp
mov [ r10 + 0x10 ], r11
mov [ r10 + 0x0 ], rbx
mov [ r10 + 0x8 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 216
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.5263
; seed 2869372618735269 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 7910 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=126, initial num_batches=31): 461 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.058280657395701645
; number reverted permutation / tried permutation: 358 / 490 =73.061%
; number reverted decision / tried decision: 363 / 509 =71.316%
; validated in 3.301s
