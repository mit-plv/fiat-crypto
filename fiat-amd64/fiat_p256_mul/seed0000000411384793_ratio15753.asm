SECTION .text
	GLOBAL fiat_p256_mul
fiat_p256_mul:
sub rsp, 176
mov rax, rdx
mov rdx, [ rdx + 0x18 ]
mulx r11, r10, [ rsi + 0x8 ]
mov rdx, [ rax + 0x0 ]
mulx r8, rcx, [ rsi + 0x0 ]
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, rcx
mov [ rsp - 0x78 ], rbp
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rcx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x18 ]
mov rdx, [ rax + 0x18 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x48 ], r11
mov [ rsp - 0x40 ], r10
mulx r10, r11, [ rsi + 0x10 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], r11
mulx r11, r10, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rbx
mov [ rsp - 0x20 ], rdi
mulx rdi, rbx, [ rax + 0x18 ]
test al, al
adox rbp, rcx
adcx r10, r12
mov rdx, [ rax + 0x8 ]
mulx rcx, rbp, [ rsi + 0x0 ]
mov rdx, 0x0 
adcx r11, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, r12, [ rax + 0x10 ]
clc
adcx rbp, r8
adox r10, rbp
adcx r12, rcx
adcx r13, rdi
mov rdx, [ rsi + 0x18 ]
mulx rcx, r8, [ rax + 0x8 ]
adox r11, r12
mov rdx, [ rsi + 0x18 ]
mulx rbp, rdi, [ rax + 0x10 ]
adox r9, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r12, [ rax + 0x0 ]
setc dl
clc
adcx r8, r13
adcx rdi, rcx
adcx r15, rbp
movzx rcx, dl
lea rcx, [ rcx + r14 ]
mov r14, [ rsp - 0x20 ]
mov rdx, 0x0 
adcx r14, rdx
adox rcx, [ rsp - 0x28 ]
mov rdx, [ rsi + 0x8 ]
mulx r13, rbp, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r14
mov [ rsp - 0x8 ], r15
mulx r15, r14, [ rax + 0x8 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x0 ], rdi
mov [ rsp + 0x8 ], r8
mulx r8, rdi, [ rsi + 0x8 ]
clc
adcx rbp, r10
seto dl
mov r10, -0x2 
inc r10
adox r14, r13
adcx r14, r11
mov r11, 0xffffffff 
xchg rdx, rbp
mulx r10, r13, r11
adox rdi, r15
adcx rdi, r9
adox r8, [ rsp - 0x40 ]
mov r9, [ rsp - 0x48 ]
mov r15, 0x0 
adox r9, r15
adcx r8, rcx
mov rcx, rdx
mov rdx, [ rax + 0x0 ]
mulx r11, r15, [ rsi + 0x10 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp + 0x10 ], r12
mov [ rsp + 0x18 ], r15
mulx r15, r12, rcx
mov rdx, [ rax + 0x8 ]
mov [ rsp + 0x20 ], rbx
mov [ rsp + 0x28 ], r8
mulx r8, rbx, [ rsi + 0x10 ]
movzx rdx, bpl
adcx rdx, r9
mov rbp, -0x2 
inc rbp
adox r13, r15
mov r9, 0x0 
adox r10, r9
mov r15, -0x3 
inc r15
adox rbx, r11
setc r11b
clc
adcx r12, rcx
adcx r13, r14
adcx r10, rdi
mov r12, 0xffffffff00000001 
xchg rdx, r12
mulx rdi, r14, rcx
adcx r14, [ rsp + 0x28 ]
adcx rdi, r12
movzx rcx, r11b
adcx rcx, r9
adox r8, [ rsp - 0x30 ]
mov r11, [ rsp - 0x38 ]
adox r11, [ rsp + 0x20 ]
clc
adcx r13, [ rsp + 0x18 ]
adcx rbx, r10
mov r12, 0xffffffff 
mov rdx, r13
mulx r10, r13, r12
mov r9, [ rsp - 0x18 ]
mov r15, 0x0 
adox r9, r15
adcx r8, r14
adcx r11, rdi
mov r14, 0xffffffffffffffff 
mulx r15, rdi, r14
inc rbp
adox r13, r15
adcx r9, rcx
adox r10, rbp
mov rcx, -0x3 
inc rcx
adox rdi, rdx
adox r13, rbx
seto dil
mov rbx, -0x3 
inc rbx
adox r13, [ rsp + 0x10 ]
xchg rdx, r13
mulx r15, rbx, r14
setc bpl
clc
mov rcx, -0x1 
movzx rdi, dil
adcx rdi, rcx
adcx r8, r10
mov r10, 0xffffffff00000001 
xchg rdx, r10
mulx rcx, rdi, r13
adcx rdi, r11
adcx rcx, r9
movzx r13, bpl
mov r11, 0x0 
adcx r13, r11
adox r8, [ rsp + 0x8 ]
adox rdi, [ rsp + 0x0 ]
adox rcx, [ rsp - 0x8 ]
mov rdx, r12
mulx rbp, r12, r10
adox r13, [ rsp - 0x10 ]
clc
adcx r12, r15
adcx rbp, r11
clc
adcx rbx, r10
adcx r12, r8
mov rbx, 0xffffffff00000001 
mov rdx, r10
mulx r9, r10, rbx
adcx rbp, rdi
adcx r10, rcx
adcx r9, r13
setc dl
seto r15b
mov r8, r12
sub r8, r14
movzx rdi, dl
movzx r15, r15b
lea rdi, [ rdi + r15 ]
mov rcx, rbp
mov r15, 0xffffffff 
sbb rcx, r15
mov r13, r10
sbb r13, 0x00000000
mov rdx, r9
sbb rdx, rbx
sbb rdi, 0x00000000
cmovc r8, r12
cmovc r13, r10
mov rdi, [ rsp - 0x50 ]
mov [ rdi + 0x10 ], r13
cmovc rdx, r9
cmovc rcx, rbp
mov [ rdi + 0x18 ], rdx
mov [ rdi + 0x8 ], rcx
mov [ rdi + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.5753
; seed 4137036306240588 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1169819 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=135, initial num_batches=31): 82639 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07064255239485767
; number reverted permutation / tried permutation: 66974 / 90192 =74.257%
; number reverted decision / tried decision: 43540 / 89807 =48.482%
; validated in 1.858s
