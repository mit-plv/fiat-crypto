SECTION .text
	GLOBAL fiat_secp256k1_montgomery_square
fiat_secp256k1_montgomery_square:
sub rsp, 208
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x0 ]
mov rdx, 0xd838091dd2253531 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rbx
mov r15, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, r14
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r12
mulx r12, r13, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x38 ], r13
mov [ rsp - 0x30 ], r12
mulx r12, r13, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r12
mov [ rsp - 0x20 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, 0xfffffffefffffc2f 
mov [ rsp - 0x18 ], r13
mov [ rsp - 0x10 ], r12
mulx r12, r13, r14
test al, al
adox r13, rbx
mov r13, r15
adcx r13, r12
mov rbx, r15
adcx rbx, rdi
adcx r15, rdi
setc r14b
clc
adcx r8, rbp
adcx r11, r9
movzx r9, r14b
lea r9, [ r9 + rdi ]
mov rdx, [ rsi + 0x18 ]
mulx rdi, rbp, [ rsi + 0x0 ]
adcx rbp, rcx
mov rdx, [ rsi + 0x0 ]
mulx r12, rcx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x8 ], rcx
mulx rcx, r14, rdx
adox r13, r8
mov rdx, 0x0 
adcx rdi, rdx
adox rbx, r11
clc
adcx rax, r12
adcx r14, r10
adox r15, rbp
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, [ rsi + 0x18 ]
adox r9, rdi
mov rdx, [ rsi + 0x10 ]
mulx rbp, r11, [ rsi + 0x18 ]
adcx r10, rcx
mov rdx, [ rsp - 0x20 ]
setc r12b
clc
adcx rdx, [ rsp - 0x30 ]
adcx r11, [ rsp - 0x28 ]
mov rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x0 ], r11
mulx r11, rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x8 ], rcx
mov [ rsp + 0x10 ], r8
mulx r8, rcx, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x18 ], r8
mov byte [ rsp + 0x20 ], r12b
mulx r12, r8, [ rsi + 0x10 ]
adcx rcx, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox r13, [ rsp - 0x40 ]
mov rbp, 0xd838091dd2253531 
xchg rdx, r13
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], r10
mulx r10, rcx, rbp
setc r10b
clc
adcx rdi, [ rsp - 0x48 ]
adcx r8, r11
adcx r12, [ rsp - 0x10 ]
mov r11, 0xfffffffefffffc2f 
xchg rdx, rcx
mov byte [ rsp + 0x38 ], r10b
mulx r10, rbp, r11
mov r11, 0xffffffffffffffff 
mov byte [ rsp + 0x40 ], r13b
mov [ rsp + 0x48 ], r14
mulx r14, r13, r11
adox rdi, rbx
adox r8, r15
mov rbx, [ rsp - 0x18 ]
mov r15, 0x0 
adcx rbx, r15
adox r12, r9
mov r9, r13
clc
adcx r9, r10
mov rdx, r13
adcx rdx, r14
adcx r13, r14
adcx r14, r15
clc
adcx rbp, rcx
adcx r9, rdi
adcx rdx, r8
adcx r13, r12
seto bpl
mov rcx, -0x3 
inc rcx
adox r9, [ rsp - 0x8 ]
adox rax, rdx
mov r10, 0xd838091dd2253531 
mov rdx, r9
mulx rdi, r9, r10
xchg rdx, r11
mulx r8, rdi, r9
adox r13, [ rsp + 0x48 ]
setc r12b
clc
mov r15, -0x1 
movzx rcx, byte [ rsp + 0x40 ]
movzx rbp, bpl
adcx rbp, r15
adcx rbx, rcx
setc cl
clc
movzx r12, r12b
adcx r12, r15
adcx rbx, r14
mov rbp, 0xfffffffefffffc2f 
mov rdx, rbp
mulx r14, rbp, r9
mov r12, rdi
setc r9b
clc
adcx r12, r14
adox rbx, [ rsp + 0x30 ]
movzx r14, byte [ rsp + 0x20 ]
mov r15, [ rsp + 0x10 ]
lea r14, [ r14 + r15 ]
mov r15, rdi
adcx r15, r8
adcx rdi, r8
movzx rdx, r9b
movzx rcx, cl
lea rdx, [ rdx + rcx ]
mov rcx, 0x0 
adcx r8, rcx
adox r14, rdx
clc
adcx rbp, r11
adcx r12, rax
seto bpl
mov r11, -0x3 
inc r11
adox r12, [ rsp - 0x38 ]
adcx r15, r13
adcx rdi, rbx
mov rdx, r10
mulx rax, r10, r12
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx r13, rax, r10
adox r15, [ rsp + 0x8 ]
adcx r8, r14
mov r9, 0xfffffffefffffc2f 
mov rdx, r9
mulx rbx, r9, r10
adox rdi, [ rsp + 0x0 ]
movzx r14, bpl
adcx r14, rcx
mov rbp, rax
clc
adcx rbp, rbx
mov r10, rax
adcx r10, r13
adcx rax, r13
adcx r13, rcx
clc
adcx r9, r12
adcx rbp, r15
movzx r9, byte [ rsp + 0x38 ]
mov r12, [ rsp + 0x18 ]
lea r9, [ r9 + r12 ]
adcx r10, rdi
adox r8, [ rsp + 0x28 ]
adcx rax, r8
adox r9, r14
adcx r13, r9
seto r12b
adc r12b, 0x0
movzx r12, r12b
mov r15, rbp
sub r15, rdx
mov rbx, r10
mov rdi, 0xffffffffffffffff 
sbb rbx, rdi
mov r14, rax
sbb r14, rdi
mov r8, r13
sbb r8, rdi
movzx r9, r12b
sbb r9, 0x00000000
cmovc r14, rax
cmovc r15, rbp
cmovc r8, r13
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x18 ], r8
mov [ r9 + 0x0 ], r15
mov [ r9 + 0x10 ], r14
cmovc rbx, r10
mov [ r9 + 0x8 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 208
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.6730
; seed 0259794080422461 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1249844 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=111, initial num_batches=31): 76752 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06140926387613174
; number reverted permutation / tried permutation: 67292 / 90239 =74.571%
; number reverted decision / tried decision: 46265 / 89760 =51.543%
; validated in 2.563s
