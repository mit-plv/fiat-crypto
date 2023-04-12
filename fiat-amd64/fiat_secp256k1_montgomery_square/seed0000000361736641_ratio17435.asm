SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mulx rcx, r11, [ rsi + 0x8 ]
test al, al
adox r11, r10
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, rdx
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x80 ], rbx
mulx rbx, r10, r8
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, [ rsi + 0x18 ]
adox r14, rcx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x40 ], r14
mulx r14, rcx, r10
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x38 ], rax
mov [ rsp - 0x30 ], r11
mulx r11, rax, r10
mov r10, rcx
adcx r10, r11
mov r11, rcx
adcx r11, r14
adcx rcx, r14
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], r13
mulx r13, rdi, rdx
adox rdi, r15
mov rdx, 0x0 
adcx r14, rdx
adox r13, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r13
mulx r13, r15, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], rdi
mov [ rsp - 0x8 ], r12
mulx r12, rdi, [ rsi + 0x0 ]
xor rdx, rdx
adox rdi, r9
adox rbx, r12
adox r15, rbp
adox r13, rdx
mov rdx, [ rsi + 0x0 ]
mulx rbp, r9, [ rsi + 0x8 ]
adcx rax, r8
adcx r10, rdi
mov rax, -0x2 
inc rax
adox r9, r10
mov rdx, 0xd838091dd2253531 
mulx r12, r8, r9
mov rdx, [ rsi + 0x10 ]
mulx rdi, r12, [ rsi + 0x8 ]
adcx r11, rbx
adcx rcx, r15
mov rdx, [ rsi + 0x8 ]
mulx r15, rbx, rdx
adcx r14, r13
setc dl
clc
adcx rbx, rbp
adcx r12, r15
mov r13b, dl
mov rdx, [ rsi + 0x8 ]
mulx r10, rbp, [ rsi + 0x18 ]
adcx rbp, rdi
adox rbx, r11
adox r12, rcx
adox rbp, r14
mov rdx, 0xffffffffffffffff 
mulx r11, rdi, r8
mov rcx, 0xfffffffefffffc2f 
mov rdx, rcx
mulx r15, rcx, r8
mov r8, rdi
setc r14b
clc
adcx r8, r15
movzx r15, r14b
lea r15, [ r15 + r10 ]
mov r10, rdi
adcx r10, r11
adcx rdi, r11
movzx r14, r13b
adox r14, r15
seto r13b
inc rax
adox rcx, r9
adox r8, rbx
adox r10, r12
adcx r11, rax
mov rdx, [ rsi + 0x0 ]
mulx r9, rcx, [ rsi + 0x10 ]
clc
adcx rcx, r8
mov rdx, 0xd838091dd2253531 
mulx r12, rbx, rcx
mov rdx, [ rsi + 0x8 ]
mulx r15, r12, [ rsi + 0x10 ]
adox rdi, rbp
adox r11, r14
movzx rdx, r13b
adox rdx, rax
mov rbp, -0x3 
inc rbp
adox r12, r9
adcx r12, r10
adox r15, [ rsp - 0x8 ]
mov r13, [ rsp - 0x28 ]
adox r13, [ rsp - 0x20 ]
mov r14, [ rsp - 0x30 ]
adox r14, rax
adcx r15, rdi
adcx r13, r11
adcx r14, rdx
mov r8, 0xfffffffefffffc2f 
mov rdx, r8
mulx r10, r8, rbx
mov r9, -0x3 
inc r9
adox r8, rcx
mov r8, 0xffffffffffffffff 
mov rdx, r8
mulx r9, r8, rbx
mov rcx, r8
setc bl
clc
adcx rcx, r10
mov rdi, r8
adcx rdi, r9
adcx r8, r9
adox rcx, r12
setc r11b
clc
adcx rcx, [ rsp - 0x38 ]
adox rdi, r15
adox r8, r13
adcx rdi, [ rsp - 0x48 ]
adcx r8, [ rsp - 0x40 ]
movzx r12, r11b
lea r12, [ r12 + r9 ]
adox r12, r14
adcx r12, [ rsp - 0x10 ]
mov r15, 0xd838091dd2253531 
mov rdx, r15
mulx r13, r15, rcx
mov r13, 0xffffffffffffffff 
mov rdx, r15
mulx r14, r15, r13
movzx r10, bl
adox r10, rax
mov rbx, 0xfffffffefffffc2f 
mulx r11, r9, rbx
adcx r10, [ rsp - 0x18 ]
mov rdx, r15
mov rbp, -0x3 
inc rbp
adox rdx, r11
mov r11, r15
adox r11, r14
adox r15, r14
setc bpl
clc
adcx r9, rcx
adcx rdx, rdi
adcx r11, r8
adox r14, rax
adcx r15, r12
adcx r14, r10
movzx r9, bpl
adc r9, 0x0
mov rcx, rdx
sub rcx, rbx
mov rdi, r11
sbb rdi, r13
mov r8, r15
sbb r8, r13
mov r12, r14
sbb r12, r13
sbb r9, 0x00000000
cmovc rcx, rdx
cmovc r8, r15
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x10 ], r8
cmovc r12, r14
cmovc rdi, r11
mov [ r9 + 0x8 ], rdi
mov [ r9 + 0x0 ], rcx
mov [ r9 + 0x18 ], r12
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.7435
; seed 4146935321735588 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1817699 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=186, initial num_batches=31): 136574 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07513565227246095
; number reverted permutation / tried permutation: 67510 / 90092 =74.935%
; number reverted decision / tried decision: 59209 / 89907 =65.856%
; validated in 4.586s
