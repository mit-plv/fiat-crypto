SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 160
mov rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx r11, r10, [ rax + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mulx r8, rcx, [ rax + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rax + 0x0 ]
test al, al
adox r10, r12
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r12, [ rsi + 0x8 ]
adcx rcx, r14
adox r12, r11
mov rdx, [ rax + 0x10 ]
mulx r14, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, r13
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x40 ], r12
mulx r12, r9, [ rax + 0x18 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], rbp
mulx rbp, r10, rdi
adox r9, r15
mov r15, 0x0 
adox r12, r15
adcx r11, r8
mov rdx, [ rsi + 0x0 ]
mulx r15, r8, [ rax + 0x18 ]
adcx r8, r14
mov rdx, rdi
mov r14, -0x2 
inc r14
adox rdx, r13
adox r10, rcx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r13, [ rax + 0x8 ]
setc dl
clc
adcx r13, rbx
movzx rbx, dl
lea rbx, [ rbx + r15 ]
mov rdx, [ rax + 0x10 ]
mulx r14, r15, [ rsi + 0x10 ]
adcx r15, rcx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r15
mulx r15, rcx, [ rax + 0x18 ]
adcx rcx, r14
mov rdx, 0xffffffff 
mov [ rsp - 0x20 ], rcx
mulx rcx, r14, rdi
mov rdx, 0x0 
adcx r15, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r15
mov [ rsp - 0x10 ], r13
mulx r13, r15, rdi
clc
adcx r15, rbp
adcx r14, r13
mov rdi, 0x0 
adcx rcx, rdi
clc
adcx r10, [ rsp - 0x30 ]
mulx r13, rbp, r10
adox r15, r11
adcx r15, [ rsp - 0x38 ]
mulx r11, r13, rbp
mov rdi, 0xffffffff00000000 
mov rdx, rdi
mov [ rsp - 0x8 ], r11
mulx r11, rdi, rbp
adox r14, r8
adcx r14, [ rsp - 0x40 ]
adox rcx, rbx
adcx r9, rcx
mov r8, rbp
seto bl
mov rcx, -0x2 
inc rcx
adox r8, r10
movzx r8, bl
adcx r8, r12
adox rdi, r15
setc r12b
clc
adcx rdi, [ rsp - 0x48 ]
mov r10, 0xffffffffffffffff 
mov rdx, rdi
mulx r15, rdi, r10
mov r15, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbx, [ rax + 0x0 ]
mov rdx, 0xffffffff 
mov [ rsp + 0x0 ], rbx
mulx rbx, r10, rbp
setc bpl
clc
adcx r13, r11
adox r13, r14
adcx r10, [ rsp - 0x8 ]
mov r11, 0x0 
adcx rbx, r11
adox r10, r9
adox rbx, r8
mov rdx, [ rax + 0x8 ]
mulx r9, r14, [ rsi + 0x18 ]
clc
adcx r14, rcx
seto dl
dec r11
movzx rbp, bpl
adox rbp, r11
adox r13, [ rsp - 0x10 ]
adox r10, [ rsp - 0x28 ]
adox rbx, [ rsp - 0x20 ]
mov r8b, dl
mov rdx, [ rax + 0x18 ]
mulx rcx, rbp, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x8 ], rbx
mulx rbx, r11, [ rsi + 0x18 ]
adcx r11, r9
movzx rdx, r8b
movzx r12, r12b
lea rdx, [ rdx + r12 ]
adox rdx, [ rsp - 0x18 ]
adcx rbp, rbx
mov r12, 0x0 
adcx rcx, r12
mov r8, 0xffffffff00000000 
xchg rdx, rdi
mulx rbx, r9, r8
mov r12, 0xffffffffffffffff 
mov [ rsp + 0x10 ], rcx
mulx rcx, r8, r12
clc
adcx r8, rbx
mov rbx, 0xffffffff 
mov [ rsp + 0x18 ], rbp
mulx rbp, r12, rbx
adcx r12, rcx
mov rcx, 0x0 
adcx rbp, rcx
clc
adcx rdx, r15
adcx r9, r13
seto dl
mov r15, -0x3 
inc r15
adox r9, [ rsp + 0x0 ]
adcx r8, r10
adox r14, r8
adcx r12, [ rsp + 0x8 ]
adcx rbp, rdi
movzx r13, dl
adcx r13, rcx
mov r10, 0xffffffffffffffff 
mov rdx, r10
mulx rdi, r10, r9
mulx r8, rdi, r10
adox r11, r12
mov rdx, r10
mulx r12, r10, rbx
mov rcx, 0xffffffff00000000 
mulx rbx, r15, rcx
clc
adcx rdi, rbx
adcx r10, r8
mov r8, 0x0 
adcx r12, r8
clc
adcx rdx, r9
adcx r15, r14
adox rbp, [ rsp + 0x18 ]
adox r13, [ rsp + 0x10 ]
adcx rdi, r11
adcx r10, rbp
adcx r12, r13
seto dl
adc dl, 0x0
movzx rdx, dl
mov r9, r15
sub r9, 0x00000001
mov r14, rdi
sbb r14, rcx
mov r11, r10
mov rbx, 0xffffffffffffffff 
sbb r11, rbx
mov rbp, r12
mov r13, 0xffffffff 
sbb rbp, r13
movzx rcx, dl
sbb rcx, 0x00000000
cmovc r11, r10
cmovc r9, r15
cmovc r14, rdi
mov rcx, [ rsp - 0x50 ]
mov [ rcx + 0x0 ], r9
cmovc rbp, r12
mov [ rcx + 0x18 ], rbp
mov [ rcx + 0x10 ], r11
mov [ rcx + 0x8 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 160
ret
; cpu Intel(R) Core(TM) i7-10710U CPU @ 1.10GHz
; ratio 1.4813
; seed 4187171054767717 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 2007467 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=209, initial num_batches=31): 146326 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.07289086196684678
; number reverted permutation / tried permutation: 63466 / 90127 =70.418%
; number reverted decision / tried decision: 57732 / 89872 =64.238%
; validated in 4.829s
