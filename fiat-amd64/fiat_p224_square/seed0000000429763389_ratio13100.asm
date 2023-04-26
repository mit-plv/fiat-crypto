SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 176
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r9, r8, rdx
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rbx
mov [ rsp - 0x68 ], r13
mov r13, 0xffffffff00000000 
mov rdx, r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, rbx
mov [ rsp - 0x58 ], r15
mov r15, 0xffffffff 
mov rdx, rbx
mov [ rsp - 0x50 ], rdi
mulx rdi, rbx, r15
test al, al
adox rbp, r14
adox rbx, r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mulx r15, r14, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x48 ], rbx
mov [ rsp - 0x40 ], rbp
mulx rbp, rbx, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], rbp
mov [ rsp - 0x30 ], rbx
mulx rbx, rbp, [ rsi + 0x8 ]
mov rdx, 0x0 
adox rdi, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], rdi
mov [ rsp - 0x20 ], rbp
mulx rbp, rdi, [ rsi + 0x0 ]
adcx r8, rbx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x18 ], rdi
mulx rdi, rbx, [ rsi + 0x8 ]
adcx rbx, r9
mov rdx, -0x2 
inc rdx
adox r11, r10
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rsi + 0x18 ]
adcx r10, rdi
mov rdx, 0x0 
adcx r9, rdx
adox r14, rcx
mov rdx, [ rsi + 0x18 ]
mulx rdi, rcx, [ rsi + 0x0 ]
adox rcx, r15
mov rdx, 0x0 
adox rdi, rdx
test al, al
adox r12, rax
adox r13, r11
adox r14, [ rsp - 0x40 ]
mov rdx, [ rsi + 0x18 ]
mulx rax, r12, [ rsi + 0x10 ]
adox rcx, [ rsp - 0x48 ]
mov rdx, [ rsi + 0x18 ]
mulx r11, r15, [ rsi + 0x0 ]
adcx r11, [ rsp - 0x30 ]
adcx r12, [ rsp - 0x38 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x10 ], r12
mov [ rsp - 0x8 ], r11
mulx r11, r12, rdx
adcx r12, rax
setc dl
clc
adcx r13, [ rsp - 0x20 ]
adcx r8, r14
adcx rbx, rcx
adox rdi, [ rsp - 0x28 ]
adcx r10, rdi
movzx r14, dl
lea r14, [ r14 + r11 ]
mov rdx, [ rsi + 0x10 ]
mulx rcx, rax, [ rsi + 0x8 ]
setc dl
clc
adcx rax, rbp
mov rbp, 0xffffffffffffffff 
xchg rdx, r13
mulx rdi, r11, rbp
mov rdi, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x0 ], r14
mulx r14, rbp, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp + 0x8 ], r12
mov [ rsp + 0x10 ], r15
mulx r15, r12, rdx
movzx rdx, r13b
adox rdx, r9
mov r9, 0xffffffffffffffff 
xchg rdx, r9
mov [ rsp + 0x18 ], r9
mulx r9, r13, r11
adcx r12, rcx
adcx rbp, r15
mov rcx, 0xffffffff00000000 
mov rdx, rcx
mulx r15, rcx, r11
mov rdx, r11
mov [ rsp + 0x20 ], rbp
seto bpl
mov [ rsp + 0x28 ], r12
mov r12, -0x2 
inc r12
adox rdx, rdi
mov rdx, 0x0 
adcx r14, rdx
adox rcx, r8
mov rdi, 0xffffffff 
mov rdx, r11
mulx r8, r11, rdi
clc
adcx r13, r15
adcx r11, r9
adox r13, rbx
setc bl
clc
adcx rcx, [ rsp - 0x18 ]
movzx rdx, bl
lea rdx, [ rdx + r8 ]
adcx rax, r13
mov r9, 0xffffffffffffffff 
xchg rdx, rcx
mulx r8, r15, r9
mov r8, 0xffffffff00000000 
xchg rdx, r15
mulx r13, rbx, r8
adox r11, r10
adcx r11, [ rsp + 0x28 ]
adox rcx, [ rsp + 0x18 ]
adcx rcx, [ rsp + 0x20 ]
movzx r10, bpl
mov r12, 0x0 
adox r10, r12
adcx r14, r10
mov rbp, rdx
mov r10, -0x3 
inc r10
adox rbp, r15
adox rbx, rax
mulx r15, rbp, rdi
mulx r12, rax, r9
setc dl
clc
adcx rax, r13
adox rax, r11
adcx rbp, r12
mov r13, 0x0 
adcx r15, r13
adox rbp, rcx
clc
adcx rbx, [ rsp + 0x10 ]
xchg rdx, rbx
mulx rcx, r11, r9
xchg rdx, r8
mulx r12, rcx, r11
adcx rax, [ rsp - 0x8 ]
mov rdx, r11
mulx r13, r11, r9
mulx r9, r10, rdi
adcx rbp, [ rsp - 0x10 ]
adox r15, r14
movzx r14, bl
mov rdi, 0x0 
adox r14, rdi
adcx r15, [ rsp + 0x8 ]
adcx r14, [ rsp + 0x0 ]
mov rbx, -0x3 
inc rbx
adox r11, r12
adox r10, r13
setc r12b
clc
adcx rdx, r8
adcx rcx, rax
adcx r11, rbp
adcx r10, r15
adox r9, rdi
adcx r9, r14
movzx rdx, r12b
adc rdx, 0x0
mov r8, rcx
sub r8, 0x00000001
mov rax, r11
mov r13, 0xffffffff00000000 
sbb rax, r13
mov rbp, r10
mov r15, 0xffffffffffffffff 
sbb rbp, r15
mov r12, r9
mov r14, 0xffffffff 
sbb r12, r14
sbb rdx, 0x00000000
cmovc r12, r9
cmovc r8, rcx
cmovc rax, r11
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x18 ], r12
mov [ rdx + 0x8 ], rax
cmovc rbp, r10
mov [ rdx + 0x10 ], rbp
mov [ rdx + 0x0 ], r8
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 176
ret
; cpu AMD Ryzen 7 5800X 8-Core Processor
; ratio 1.3100
; seed 4161737509132058 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1310438 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=139, initial num_batches=31): 82108 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06265691318475197
; number reverted permutation / tried permutation: 69772 / 89726 =77.761%
; number reverted decision / tried decision: 47656 / 90273 =52.791%
; validated in 2.676s
