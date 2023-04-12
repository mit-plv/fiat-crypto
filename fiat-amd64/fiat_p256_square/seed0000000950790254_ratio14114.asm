SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
sub rsp, 176
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, rdx
mov rdx, 0xffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, r12
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], r13
mulx r13, r8, [ rsi + 0x8 ]
test al, al
adox rax, r13
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x30 ], rax
mulx rax, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r13
mov [ rsp - 0x20 ], r8
mulx r8, r13, [ rsi + 0x8 ]
adcx r13, rax
adcx r14, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rax, [ rsi + 0x18 ]
adcx rax, r15
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], rax
mulx rax, r15, r12
setc dl
clc
adcx rdi, rax
movzx rax, dl
lea rax, [ rax + r8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x10 ], rax
mulx rax, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x8 ], r14
mov [ rsp + 0x0 ], r13
mulx r13, r14, [ rsi + 0x18 ]
setc dl
clc
adcx r11, r13
adcx r8, rcx
movzx rcx, dl
lea rcx, [ rcx + r9 ]
mov rdx, [ rsi + 0x18 ]
mulx r13, r9, rdx
adcx r9, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r9
mulx r9, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x10 ], r8
mov [ rsp + 0x18 ], r11
mulx r11, r8, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp + 0x20 ], r14
mov [ rsp + 0x28 ], rcx
mulx rcx, r14, [ rsi + 0x10 ]
adox r14, r10
mov rdx, 0x0 
adcx r13, rdx
adox rbx, rcx
clc
adcx r15, r12
adox rbp, rdx
mov r15, -0x3 
inc r15
adox r8, [ rsp - 0x38 ]
adcx rdi, r8
adox rax, r11
adox r9, [ rsp - 0x40 ]
mov r10, [ rsp - 0x48 ]
adox r10, rdx
mov r11, -0x3 
inc r11
adox rdi, [ rsp - 0x20 ]
mov r11, 0xffffffff00000001 
mov rdx, r12
mulx rcx, r12, r11
adcx rax, [ rsp + 0x28 ]
adcx r12, r9
adcx rcx, r10
adox rax, [ rsp - 0x30 ]
adox r14, r12
adox rbx, rcx
seto dl
movzx rdx, dl
adcx rdx, rbp
mov rbp, 0xffffffffffffffff 
xchg rdx, rbp
mulx r9, r8, rdi
mov r10, 0xffffffff 
mov rdx, r10
mulx r12, r10, rdi
inc r15
adox r10, r9
setc cl
clc
adcx r8, rdi
adcx r10, rax
mov rdx, r11
mulx r8, r11, rdi
mov rdi, 0x0 
adox r12, rdi
adcx r12, r14
adcx r11, rbx
adcx r8, rbp
mov rax, -0x3 
inc rax
adox r10, [ rsp - 0x28 ]
adox r12, [ rsp + 0x0 ]
movzx r14, cl
adcx r14, rdi
mulx rbp, rbx, r10
mov rcx, 0xffffffffffffffff 
mov rdx, r10
mulx r9, r10, rcx
mov rdi, 0xffffffff 
mulx r15, rax, rdi
adox r11, [ rsp - 0x8 ]
adox r8, [ rsp - 0x18 ]
clc
adcx rax, r9
adox r14, [ rsp - 0x10 ]
mov r9, 0x0 
adcx r15, r9
clc
adcx r10, rdx
adcx rax, r12
seto r10b
mov rdx, -0x3 
inc rdx
adox rax, [ rsp + 0x20 ]
adcx r15, r11
adcx rbx, r8
adox r15, [ rsp + 0x18 ]
adox rbx, [ rsp + 0x10 ]
adcx rbp, r14
movzx r12, r10b
adcx r12, r9
mov rdx, rax
mulx r11, rax, rcx
mulx r10, r8, rdi
clc
adcx r8, r11
adcx r10, r9
clc
adcx rax, rdx
adcx r8, r15
adcx r10, rbx
mov rax, 0xffffffff00000001 
mulx r15, r14, rax
adox rbp, [ rsp + 0x8 ]
adox r13, r12
adcx r14, rbp
adcx r15, r13
seto dl
adc dl, 0x0
movzx rdx, dl
mov rbx, r8
sub rbx, rcx
mov r12, r10
sbb r12, rdi
mov r11, r14
sbb r11, 0x00000000
mov rbp, r15
sbb rbp, rax
movzx r13, dl
sbb r13, 0x00000000
cmovc r11, r14
cmovc rbx, r8
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x0 ], rbx
cmovc r12, r10
mov [ r13 + 0x8 ], r12
cmovc rbp, r15
mov [ r13 + 0x18 ], rbp
mov [ r13 + 0x10 ], r11
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4114
; seed 2137803125293891 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 884572 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=135, initial num_batches=31): 61696 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0697467249698159
; number reverted permutation / tried permutation: 69351 / 89727 =77.291%
; number reverted decision / tried decision: 50599 / 90272 =56.052%
; validated in 1.187s
