SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x10 ]
mulx r10, rax, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rdx
mov rdx, 0xffffffff 
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, r12
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], rbx
mulx rbx, rdi, r12
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x40 ], rbp
mov [ rsp - 0x38 ], r11
mulx r11, rbp, rdx
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x30 ], r11
mov [ rsp - 0x28 ], rbp
mulx rbp, r11, r12
test al, al
adox rdi, r12
adcx r14, rbx
mov rdi, 0x0 
adcx r15, rdi
mov rdx, [ rsi + 0x0 ]
mulx rbx, r12, [ rsi + 0x8 ]
clc
adcx r12, r13
adcx rax, rbx
adox r14, r12
mov rdx, [ rsi + 0x18 ]
mulx rbx, r13, [ rsi + 0x0 ]
adcx r13, r10
adcx rbx, rdi
mov rdx, [ rsi + 0x10 ]
mulx r12, r10, [ rsi + 0x8 ]
adox r15, rax
adox r11, r13
clc
adcx r8, rcx
adcx r10, r9
mov rdx, [ rsi + 0x18 ]
mulx r9, rcx, [ rsi + 0x8 ]
adcx rcx, r12
adcx r9, rdi
clc
adcx r14, [ rsp - 0x38 ]
adcx r8, r15
adcx r10, r11
mov rdx, 0xffffffffffffffff 
mulx r13, rax, r14
mov r12, 0xffffffff 
mov rdx, r14
mulx r15, r14, r12
setc r11b
clc
adcx r14, r13
adcx r15, rdi
adox rbp, rbx
mov rbx, rdx
mov rdx, [ rsi + 0x10 ]
mulx rdi, r13, [ rsi + 0x8 ]
clc
mov rdx, -0x1 
movzx r11, r11b
adcx r11, rdx
adcx rbp, rcx
seto cl
movzx rcx, cl
adcx rcx, r9
inc rdx
adox r13, [ rsp - 0x40 ]
setc r9b
clc
adcx rax, rbx
adox rdi, [ rsp - 0x28 ]
adcx r14, r8
mov rdx, [ rsi + 0x10 ]
mulx r8, rax, [ rsi + 0x18 ]
adcx r15, r10
adox rax, [ rsp - 0x30 ]
seto dl
mov r11, -0x2 
inc r11
adox r14, [ rsp - 0x48 ]
adox r13, r15
movzx r10, dl
lea r10, [ r10 + r8 ]
mov r8, 0xffffffff00000001 
mov rdx, rbx
mulx r15, rbx, r8
mov rdx, r12
mulx r11, r12, r14
adcx rbx, rbp
adox rdi, rbx
adcx r15, rcx
mov rbp, 0xffffffffffffffff 
mov rdx, rbp
mulx rcx, rbp, r14
movzx rbx, r9b
mov r8, 0x0 
adcx rbx, r8
clc
adcx r12, rcx
adox rax, r15
adcx r11, r8
adox r10, rbx
clc
adcx rbp, r14
adcx r12, r13
mov rdx, [ rsi + 0x10 ]
mulx r9, rbp, [ rsi + 0x18 ]
mov rdx, 0xffffffff00000001 
mulx r15, r13, r14
mov rdx, [ rsi + 0x18 ]
mulx rcx, r14, [ rsi + 0x0 ]
adcx r11, rdi
adcx r13, rax
mov rdx, [ rsi + 0x8 ]
mulx rbx, rdi, [ rsi + 0x18 ]
seto dl
mov rax, -0x3 
inc rax
adox r14, r12
adcx r15, r10
mov r10, 0xffffffff 
xchg rdx, r14
mulx r8, r12, r10
setc al
clc
adcx rdi, rcx
adcx rbp, rbx
adox rdi, r11
adox rbp, r13
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mulx r13, r11, rdx
adcx r11, r9
adox r11, r15
mov rdx, 0x0 
adcx r13, rdx
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx rbx, r9, rcx
clc
adcx r12, rbx
movzx r15, al
movzx r14, r14b
lea r15, [ r15 + r14 ]
mov r14, 0x0 
adcx r8, r14
adox r13, r15
clc
adcx r9, rcx
adcx r12, rdi
adcx r8, rbp
mov r9, 0xffffffff00000001 
mov rdx, rcx
mulx rax, rcx, r9
adcx rcx, r11
adcx rax, r13
seto dl
adc dl, 0x0
movzx rdx, dl
mov rdi, r12
mov rbp, 0xffffffffffffffff 
sub rdi, rbp
mov r11, r8
sbb r11, r10
mov rbx, rcx
sbb rbx, 0x00000000
mov r15, rax
sbb r15, r9
movzx r13, dl
sbb r13, 0x00000000
cmovc rbx, rcx
cmovc r11, r8
mov r13, [ rsp - 0x50 ]
mov [ r13 + 0x8 ], r11
cmovc rdi, r12
mov [ r13 + 0x0 ], rdi
cmovc r15, rax
mov [ r13 + 0x18 ], r15
mov [ r13 + 0x10 ], rbx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen 9 7950X 16-Core Processor
; ratio 1.4867
; seed 3307607861175400 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 853265 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=134, initial num_batches=31): 62076 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07275113827474465
; number reverted permutation / tried permutation: 70044 / 90196 =77.658%
; number reverted decision / tried decision: 48515 / 89803 =54.024%
; validated in 1.215s
