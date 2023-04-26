SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 200
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], rbx
mov [ rsp - 0x38 ], rdi
mulx rdi, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], rbx
mov [ rsp - 0x28 ], r12
mulx r12, rbx, [ rsi + 0x10 ]
add rax, rdi
adcx rbx, r10
mov rdx, -0x2 
inc rdx
adox r11, rbp
mov rdx, [ rsi + 0x18 ]
mulx rbp, r10, [ rsi + 0x10 ]
adcx r8, r12
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, r12, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r9, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mov [ rsp - 0x10 ], r11
mulx r11, r14, [ rsi + 0x0 ]
clc
adcx rcx, r11
adox r10, r15
seto dl
mov r15, -0x2 
inc r15
adox r12, r13
mov r13, 0xffffffff 
mov r11b, dl
mov rdx, [ rsp - 0x28 ]
mov [ rsp - 0x8 ], rcx
mulx rcx, r15, r13
mov r13, rdx
mov rdx, [ rsi + 0x0 ]
mov byte [ rsp + 0x0 ], r11b
mov [ rsp + 0x8 ], r14
mulx r14, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp + 0x10 ], r10
mov [ rsp + 0x18 ], r9
mulx r9, r10, [ rsi + 0x18 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x20 ], r8
mov [ rsp + 0x28 ], r9
mulx r9, r8, r13
adox r11, rbp
adox r10, r14
seto bpl
mov r14, -0x2 
inc r14
adox r15, r9
seto r9b
inc r14
adox r8, r13
movzx r8, r9b
lea r8, [ r8 + rcx ]
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, rdx
adcx rdi, [ rsp - 0x38 ]
adcx rcx, [ rsp - 0x40 ]
adox r15, r12
adcx r9, r14
clc
adcx r15, [ rsp - 0x30 ]
mov rdx, 0xffffffffffffffff 
mulx r14, r12, r15
mov rdx, 0xffffffff00000001 
mov [ rsp + 0x30 ], r9
mov [ rsp + 0x38 ], rcx
mulx rcx, r9, r13
mov [ rsp + 0x40 ], rdi
mulx rdi, r13, r15
adox r8, r11
adox r9, r10
adcx rax, r8
adcx rbx, r9
movzx r11, bpl
mov r10, [ rsp + 0x28 ]
lea r11, [ r11 + r10 ]
adox rcx, r11
mov r10, 0xffffffff 
mov rdx, r10
mulx rbp, r10, r15
adcx rcx, [ rsp + 0x20 ]
seto r8b
mov r9, -0x2 
inc r9
adox r10, r14
movzx r8, r8b
movzx r14, r8b
adcx r14, [ rsp + 0x18 ]
setc r11b
clc
adcx r12, r15
adcx r10, rax
mov r12, 0x0 
adox rbp, r12
adcx rbp, rbx
adcx r13, rcx
mov r15, -0x3 
inc r15
adox r10, [ rsp - 0x48 ]
mov rax, 0xffffffffffffffff 
mov rdx, r10
mulx rbx, r10, rax
adcx rdi, r14
movzx r8, r11b
adcx r8, r12
mov rcx, 0xffffffff 
mulx r14, r11, rcx
clc
adcx r11, rbx
adcx r14, r12
adox rbp, [ rsp - 0x10 ]
clc
adcx r10, rdx
adcx r11, rbp
adox r13, [ rsp - 0x18 ]
adox rdi, [ rsp + 0x10 ]
setc r10b
clc
adcx r11, [ rsp + 0x8 ]
setc bl
clc
movzx r10, r10b
adcx r10, r9
adcx r13, r14
mov r14, 0xffffffff00000001 
mulx r10, rbp, r14
adcx rbp, rdi
movzx rdx, byte [ rsp + 0x0 ]
mov rdi, [ rsp - 0x20 ]
lea rdx, [ rdx + rdi ]
xchg rdx, rcx
mulx r12, rdi, r11
mov rdx, r11
mulx r15, r11, rax
adox rcx, r8
adcx r10, rcx
seto r8b
inc r9
adox rdi, r15
movzx r15, r8b
adcx r15, r9
adox r12, r9
add bl, 0x7F
adox r13, [ rsp - 0x8 ]
adox rbp, [ rsp + 0x40 ]
adox r10, [ rsp + 0x38 ]
mulx r8, rbx, r14
adcx r11, rdx
adcx rdi, r13
adcx r12, rbp
adcx rbx, r10
adox r15, [ rsp + 0x30 ]
adcx r8, r15
seto r11b
adc r11b, 0x0
movzx r11, r11b
mov rdx, rdi
sub rdx, rax
mov rcx, r12
mov r13, 0xffffffff 
sbb rcx, r13
mov rbp, rbx
sbb rbp, 0x00000000
mov r10, r8
sbb r10, r14
movzx r15, r11b
sbb r15, 0x00000000
cmovc rbp, rbx
mov r15, [ rsp - 0x50 ]
mov [ r15 + 0x10 ], rbp
cmovc r10, r8
cmovc rdx, rdi
cmovc rcx, r12
mov [ r15 + 0x0 ], rdx
mov [ r15 + 0x8 ], rcx
mov [ r15 + 0x18 ], r10
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 200
ret
; cpu 12th Gen Intel(R) Core(TM) i9-12900KF
; ratio 1.6561
; seed 1194348016026391 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 994230 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=197, initial num_batches=31): 79075 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07953391066453436
; number reverted permutation / tried permutation: 79901 / 89886 =88.891%
; number reverted decision / tried decision: 67840 / 90113 =75.283%
; validated in 1.093s
