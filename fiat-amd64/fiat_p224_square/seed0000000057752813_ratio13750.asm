SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 144
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r11
mulx r11, rdi, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r9
mov [ rsp - 0x38 ], r8
mulx r8, r9, [ rsi + 0x18 ]
test al, al
adox r9, rcx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x30 ], r9
mulx r9, rcx, [ rsi + 0x10 ]
adox rcx, r8
adox r14, r9
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x10 ]
adcx rbx, r11
adcx r8, rbp
mov rdx, 0xffffffffffffffff 
mulx r11, rbp, rdi
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x28 ], r14
mulx r14, r11, [ rsi + 0x0 ]
adcx r11, r9
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x20 ], rcx
mulx rcx, r9, [ rsi + 0x0 ]
mov rdx, 0x0 
adox r15, rdx
adc r14, 0x0
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r9
mulx r9, r15, rbp
xor rdx, rdx
adox r12, rcx
adox rax, r13
mov rdx, [ rsi + 0x18 ]
mulx rcx, r13, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x8 ], rax
mov [ rsp + 0x0 ], r12
mulx r12, rax, rbp
adcx r15, r12
adox r13, r10
mov r10, 0x0 
adox rcx, r10
mov r12, 0xffffffff 
mov rdx, r12
mulx r10, r12, rbp
adcx r12, r9
adc r10, 0x0
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], rcx
mulx rcx, r9, [ rsi + 0x8 ]
add rbp, rdi
adcx rax, rbx
adcx r15, r8
mov rdx, [ rsi + 0x0 ]
mulx rdi, rbp, [ rsi + 0x8 ]
mov rdx, -0x2 
inc rdx
adox rbp, rax
adcx r12, r11
adcx r10, r14
setc bl
clc
adcx rdi, [ rsp - 0x38 ]
adcx r9, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r8, [ rsi + 0x8 ]
adox rdi, r15
adcx r8, rcx
mov rdx, 0x0 
adcx r11, rdx
adox r9, r12
adox r8, r10
mov r14, 0xffffffffffffffff 
mov rdx, r14
mulx rcx, r14, rbp
movzx rcx, bl
adox rcx, r11
mulx r15, rax, r14
mov r12, 0xffffffff00000000 
mov rdx, r14
mulx rbx, r14, r12
mov r10, rdx
clc
adcx r10, rbp
setc r10b
clc
adcx rax, rbx
seto bpl
mov r11, -0x1 
inc r11
mov rbx, -0x1 
movzx r10, r10b
adox r10, rbx
adox rdi, r14
mov r14, 0xffffffff 
mulx r11, r10, r14
adcx r10, r15
adox rax, r9
mov r9, 0x0 
adcx r11, r9
adox r10, r8
clc
adcx rdi, [ rsp - 0x10 ]
adox r11, rcx
adcx rax, [ rsp + 0x0 ]
mov r8, 0xffffffffffffffff 
mov rdx, rdi
mulx rcx, rdi, r8
mov rcx, rdi
seto r15b
mov rbx, -0x3 
inc rbx
adox rcx, rdx
mov rdx, rdi
mulx rcx, rdi, r8
adcx r10, [ rsp - 0x8 ]
mulx rbx, r9, r12
adcx r13, r11
movzx r11, r15b
movzx rbp, bpl
lea r11, [ r11 + rbp ]
setc bpl
clc
adcx rdi, rbx
seto r15b
mov rbx, -0x1 
inc rbx
mov rbx, -0x1 
movzx rbp, bpl
adox rbp, rbx
adox r11, [ rsp + 0x8 ]
setc bpl
clc
movzx r15, r15b
adcx r15, rbx
adcx rax, r9
adcx rdi, r10
mulx r10, r15, r14
seto dl
inc rbx
mov r9, -0x1 
movzx rbp, bpl
adox rbp, r9
adox rcx, r15
adox r10, rbx
mov rbp, -0x3 
inc rbp
adox rax, [ rsp - 0x48 ]
adox rdi, [ rsp - 0x30 ]
adcx rcx, r13
adcx r10, r11
xchg rdx, r8
mulx r11, r13, rax
movzx r11, r8b
adcx r11, rbx
mulx r15, r8, r13
adox rcx, [ rsp - 0x20 ]
mov rdx, r13
mulx rbx, r13, r12
adox r10, [ rsp - 0x28 ]
mov rbp, rdx
clc
adcx rbp, rax
adox r11, [ rsp - 0x18 ]
seto bpl
inc r9
adox r8, rbx
mulx rbx, rax, r14
adcx r13, rdi
adcx r8, rcx
adox rax, r15
adox rbx, r9
adcx rax, r10
adcx rbx, r11
movzx rdi, bpl
adc rdi, 0x0
mov rdx, r13
sub rdx, 0x00000001
mov r15, r8
sbb r15, r12
mov rcx, rax
mov r10, 0xffffffffffffffff 
sbb rcx, r10
mov rbp, rbx
sbb rbp, r14
sbb rdi, 0x00000000
cmovc r15, r8
cmovc rdx, r13
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x8 ], r15
cmovc rbp, rbx
cmovc rcx, rax
mov [ rdi + 0x18 ], rbp
mov [ rdi + 0x0 ], rdx
mov [ rdi + 0x10 ], rcx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 144
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.3750
; seed 1939070763958916 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1417296 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 83366 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.05882045811178469
; number reverted permutation / tried permutation: 67473 / 89581 =75.321%
; number reverted decision / tried decision: 59833 / 90418 =66.174%
; validated in 3.23s
