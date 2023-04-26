SECTION .text
	GLOBAL fiat_p256_square
fiat_p256_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mulx r9, r8, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x70 ], r12
mov [ rsp - 0x68 ], r13
mulx r13, r12, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x60 ], r14
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x0 ]
xor rdx, rdx
adox r12, r10
adox r14, r13
mov rdx, [ rsi + 0x18 ]
mulx r13, r10, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r9
mulx r9, rdi, rax
mov rdx, 0xffffffff 
mov [ rsp - 0x40 ], r8
mov [ rsp - 0x38 ], rcx
mulx rcx, r8, rax
adcx r8, r9
mov r9, 0x0 
adcx rcx, r9
adox r10, r15
adox r13, r9
test al, al
adox rdi, rax
adox r8, r12
adox rcx, r14
mov rdx, [ rsi + 0x8 ]
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mulx r14, r12, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x30 ], r12
mulx r12, r9, rdx
adcx rdi, r14
mov rdx, 0xffffffff00000001 
mov [ rsp - 0x28 ], rdi
mulx rdi, r14, rax
adcx r9, r15
adox r14, r10
mov rdx, [ rsi + 0x8 ]
mulx r10, rax, [ rsi + 0x0 ]
adox rdi, r13
mov rdx, [ rsi + 0x8 ]
mulx r15, r13, [ rsi + 0x18 ]
seto dl
mov [ rsp - 0x20 ], r9
mov r9, -0x2 
inc r9
adox rbx, r10
adox r11, rbp
setc bpl
clc
adcx rax, r8
adcx rbx, rcx
adcx r11, r14
adox r13, [ rsp - 0x38 ]
mov r8, 0x0 
adox r15, r8
adcx r13, rdi
inc r9
mov r8, -0x1 
movzx rbp, bpl
adox rbp, r8
adox r12, [ rsp - 0x40 ]
movzx rcx, dl
adcx rcx, r15
mov rbp, [ rsp - 0x48 ]
adox rbp, r9
mov r14, 0xffffffffffffffff 
mov rdx, rax
mulx r10, rax, r14
mov rdi, 0xffffffff 
mulx r9, r15, rdi
inc r8
adox rax, rdx
setc al
clc
adcx r15, r10
adcx r9, r8
adox r15, rbx
adox r9, r11
mov rbx, 0xffffffff00000001 
mulx r10, r11, rbx
clc
adcx r15, [ rsp - 0x30 ]
mov rdx, r15
mulx r8, r15, rdi
adox r11, r13
adox r10, rcx
adcx r9, [ rsp - 0x28 ]
adcx r11, [ rsp - 0x20 ]
movzx r13, al
mov rcx, 0x0 
adox r13, rcx
mulx rcx, rax, rbx
mulx rdi, rbx, r14
adcx r12, r10
mov r10, -0x2 
inc r10
adox rbx, rdx
adcx rbp, r13
setc bl
clc
adcx r15, rdi
adox r15, r9
mov rdx, 0x0 
adcx r8, rdx
mov rdx, [ rsi + 0x0 ]
mulx r13, r9, [ rsi + 0x18 ]
clc
adcx r9, r15
adox r8, r11
mov rdx, [ rsi + 0x8 ]
mulx rdi, r11, [ rsi + 0x18 ]
adox rax, r12
adox rcx, rbp
seto dl
inc r10
adox r11, r13
movzx r12, dl
movzx rbx, bl
lea r12, [ r12 + rbx ]
mov rdx, [ rsi + 0x10 ]
mulx rbp, rbx, [ rsi + 0x18 ]
adcx r11, r8
adox rbx, rdi
adcx rbx, rax
mov rdx, [ rsi + 0x18 ]
mulx r13, r15, rdx
adox r15, rbp
adcx r15, rcx
mov rdx, r9
mulx r8, r9, r14
adox r13, r10
adcx r13, r12
mov rdi, -0x3 
inc rdi
adox r9, rdx
mov r9, 0xffffffff 
mulx rcx, rax, r9
setc r12b
clc
adcx rax, r8
adcx rcx, r10
adox rax, r11
mov rbp, 0xffffffff00000001 
mulx r8, r11, rbp
adox rcx, rbx
adox r11, r15
adox r8, r13
movzx rdx, r12b
adox rdx, r10
mov rbx, rax
sub rbx, r14
mov r15, rcx
sbb r15, r9
mov r12, r11
sbb r12, 0x00000000
mov r13, r8
sbb r13, rbp
sbb rdx, 0x00000000
cmovc r15, rcx
cmovc r12, r11
cmovc rbx, rax
mov rdx, [ rsp - 0x50 ]
mov [ rdx + 0x0 ], rbx
cmovc r13, r8
mov [ rdx + 0x18 ], r13
mov [ rdx + 0x10 ], r12
mov [ rdx + 0x8 ], r15
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu Intel(R) Core(TM) i9-10900K CPU @ 3.70GHz
; ratio 1.5593
; seed 3967559225294246 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1135528 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=122, initial num_batches=31): 77007 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.067816029195229
; number reverted permutation / tried permutation: 68418 / 90181 =75.867%
; number reverted decision / tried decision: 55310 / 89818 =61.580%
; validated in 1.915s
