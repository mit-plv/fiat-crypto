SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r9, r8, rdx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, rax
mov [ rsp - 0x60 ], r14
xor r14, r14
adox r12, rax
mov rdx, [ rsi + 0x8 ]
mulx r14, r12, [ rsi + 0x18 ]
mov rdx, 0xffffffff 
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, rax
adcx r15, r13
mov r13, 0x0 
adcx rdi, r13
clc
adcx r11, r10
adox r15, r11
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rsi + 0x10 ]
adcx r10, rcx
adox rdi, r10
mov rdx, [ rsi + 0x18 ]
mulx r10, rcx, [ rsi + 0x0 ]
adcx rcx, r11
mov rdx, 0xffffffff00000001 
mulx r13, r11, rax
mov rax, 0x0 
adcx r10, rax
adox r11, rcx
mov rdx, [ rsi + 0x10 ]
mulx rax, rcx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x48 ], r9
mov [ rsp - 0x40 ], r8
mulx r8, r9, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x38 ], r14
mov [ rsp - 0x30 ], r12
mulx r12, r14, [ rsi + 0x10 ]
adox r13, r10
clc
adcx r14, r8
adcx rcx, r12
mov rdx, [ rsi + 0x10 ]
mulx r8, r10, [ rsi + 0x18 ]
adcx r10, rax
mov rdx, [ rsi + 0x8 ]
mulx r12, rax, rdx
mov rdx, 0x0 
adcx r8, rdx
clc
adcx rbx, r15
mov r15, 0xffffffffffffffff 
mov rdx, r15
mov [ rsp - 0x28 ], r8
mulx r8, r15, rbx
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x20 ], r10
mov [ rsp - 0x18 ], rcx
mulx rcx, r10, [ rsi + 0x10 ]
seto dl
mov [ rsp - 0x10 ], r14
mov r14, -0x2 
inc r14
adox rax, rbp
adox r10, r12
adcx rax, rdi
adcx r10, r11
mov bpl, dl
mov rdx, [ rsi + 0x8 ]
mulx r11, rdi, [ rsi + 0x18 ]
adox rdi, rcx
adcx rdi, r13
mov rdx, 0x0 
adox r11, rdx
mov r13, 0xffffffff 
mov rdx, rbx
mulx r12, rbx, r13
movzx rcx, bpl
adcx rcx, r11
inc r14
adox rbx, r8
setc bpl
clc
adcx r15, rdx
adcx rbx, rax
adox r12, r14
mov r15, 0xffffffff00000001 
mulx rax, r8, r15
mov rdx, -0x3 
inc rdx
adox r9, rbx
adcx r12, r10
adox r12, [ rsp - 0x10 ]
mov rdx, r9
mulx r10, r9, r13
adcx r8, rdi
adcx rax, rcx
adox r8, [ rsp - 0x18 ]
adox rax, [ rsp - 0x20 ]
movzx rdi, bpl
adcx rdi, r14
adox rdi, [ rsp - 0x28 ]
mov r11, 0xffffffffffffffff 
mulx rcx, rbp, r11
clc
adcx r9, rcx
adcx r10, r14
clc
adcx rbp, rdx
adcx r9, r12
adcx r10, r8
mulx rbx, rbp, r15
adcx rbp, rax
adcx rbx, rdi
mov rdx, [ rsi + 0x18 ]
mulx r8, r12, [ rsi + 0x0 ]
seto dl
adc dl, 0x0
movzx rdx, dl
adox r12, r9
mov al, dl
mov rdx, [ rsi + 0x10 ]
mulx rcx, rdi, [ rsi + 0x18 ]
mov rdx, r12
mulx r9, r12, r11
adcx r8, [ rsp - 0x30 ]
adcx rdi, [ rsp - 0x38 ]
adcx rcx, [ rsp - 0x40 ]
adox r8, r10
adox rdi, rbp
adox rcx, rbx
mulx rbp, r10, r13
mov rbx, [ rsp - 0x48 ]
adcx rbx, r14
movzx r14, al
adox r14, rbx
clc
adcx r10, r9
seto al
mov r9, -0x2 
inc r9
adox r12, rdx
mov r12, 0x0 
adcx rbp, r12
adox r10, r8
adox rbp, rdi
mulx rdi, r8, r15
adox r8, rcx
adox rdi, r14
seto dl
mov rcx, r10
sub rcx, r11
movzx rbx, dl
movzx rax, al
lea rbx, [ rbx + rax ]
mov rax, rbp
sbb rax, r13
mov r14, r8
sbb r14, 0x00000000
mov rdx, rdi
sbb rdx, r15
sbb rbx, 0x00000000
cmovc rcx, r10
cmovc r14, r8
cmovc rdx, rdi
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x10 ], r14
cmovc rax, rbp
mov [ rbx + 0x0 ], rcx
mov [ rbx + 0x8 ], rax
mov [ rbx + 0x18 ], rdx
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i7-6770HQ CPU @ 2.60GHz
; ratio 1.5801
; seed 2558778281067972 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1869596 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=124, initial num_batches=31): 124687 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06669194842094228
; number reverted permutation / tried permutation: 68080 / 89897 =75.731%
; number reverted decision / tried decision: 56414 / 90102 =62.611%
; validated in 1.919s
