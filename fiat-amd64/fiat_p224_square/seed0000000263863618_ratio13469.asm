SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x10 ]
mulx rcx, r11, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mulx r9, r8, rax
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rsi + 0x8 ]
xor rdx, rdx
adox r9, r10
mov r10, 0xffffffff 
mov rdx, r8
mov [ rsp - 0x78 ], rbp
mulx rbp, r8, r10
mov [ rsp - 0x70 ], r12
mov r12, rdx
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x58 ], r15
mulx r10, r15, [ rsi + 0x10 ]
mov rdx, 0xffffffff00000000 
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r13
mulx r13, rdi, r12
adox r11, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x40 ], r10
mulx r10, rbx, [ rsi + 0x0 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x38 ], r10
mov [ rsp - 0x30 ], rbx
mulx rbx, r10, r12
adcx r10, r13
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x28 ], r15
mulx r15, r13, [ rsi + 0x8 ]
adcx r8, rbx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x20 ], rbp
mulx rbp, rbx, [ rsi + 0x18 ]
adox rbx, rcx
mov rdx, 0x0 
adox rbp, rdx
mov rcx, -0x3 
inc rcx
adox r13, r14
mov rdx, [ rsi + 0x10 ]
mulx rcx, r14, rdx
adox r14, r15
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x18 ], r14
mulx r14, r15, [ rsi + 0x10 ]
adox r15, rcx
setc dl
clc
adcx r12, rax
mov r12b, dl
mov rdx, [ rsi + 0x8 ]
mulx rcx, rax, [ rsi + 0x0 ]
adcx rdi, r9
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x10 ], r15
mulx r15, r9, rdx
adcx r10, r11
adcx r8, rbx
movzx rdx, r12b
mov r11, [ rsp - 0x20 ]
lea rdx, [ rdx + r11 ]
adcx rdx, rbp
mov r11, 0x0 
adox r14, r11
mov r12, -0x3 
inc r12
adox r9, rcx
adox r15, [ rsp - 0x28 ]
mov rbx, rdx
mov rdx, [ rsi + 0x18 ]
mulx rcx, rbp, [ rsi + 0x8 ]
adox rbp, [ rsp - 0x40 ]
adox rcx, r11
mov rdx, -0x3 
inc rdx
adox rax, rdi
mov rdx, 0xffffffffffffffff 
mulx r11, rdi, rax
adox r9, r10
adox r15, r8
adox rbp, rbx
mulx r10, r11, rdi
mov r8, rdi
seto bl
inc r12
adox r8, rax
mov r8, 0xffffffff00000000 
mov rdx, rdi
mulx rax, rdi, r8
adox rdi, r9
movzx r9, bl
adcx r9, rcx
setc cl
clc
adcx r11, rax
adox r11, r15
mov r15, 0xffffffff 
mulx rax, rbx, r15
adcx rbx, r10
mov rdx, 0x0 
adcx rax, rdx
clc
adcx rdi, [ rsp - 0x48 ]
adcx r13, r11
adox rbx, rbp
adcx rbx, [ rsp - 0x18 ]
mov rbp, 0xffffffffffffffff 
mov rdx, rdi
mulx r10, rdi, rbp
xchg rdx, rdi
mulx r11, r10, rbp
adox rax, r9
movzx r9, cl
mov r12, 0x0 
adox r9, r12
adcx rax, [ rsp - 0x10 ]
adcx r14, r9
mulx r9, rcx, r8
mov r15, rdx
mov r8, -0x3 
inc r8
adox r15, rdi
mov r15, 0xffffffff 
mulx r12, rdi, r15
adox rcx, r13
setc r13b
clc
adcx r10, r9
adox r10, rbx
adcx rdi, r11
mov rdx, [ rsi + 0x18 ]
mulx r11, rbx, [ rsi + 0x8 ]
mov rdx, 0x0 
adcx r12, rdx
adox rdi, rax
adox r12, r14
clc
adcx rcx, [ rsp - 0x30 ]
mov rdx, rcx
mulx rax, rcx, rbp
mov rax, rdx
mov rdx, [ rsi + 0x18 ]
mulx r9, r14, [ rsi + 0x10 ]
movzx rdx, r13b
mov r8, 0x0 
adox rdx, r8
mov r13, 0xffffffff00000000 
xchg rdx, rcx
mulx r15, r8, r13
mov r13, -0x2 
inc r13
adox rbx, [ rsp - 0x38 ]
adcx rbx, r10
adox r14, r11
adcx r14, rdi
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx rdi, r11, rdx
adox r11, r9
adcx r11, r12
mov rdx, 0x0 
adox rdi, rdx
mov r12, r10
mov r9, -0x3 
inc r9
adox r12, rax
adox r8, rbx
mov rdx, rbp
mulx r12, rbp, r10
adcx rdi, rcx
setc al
clc
adcx rbp, r15
mov rcx, 0xffffffff 
mov rdx, rcx
mulx r15, rcx, r10
adcx rcx, r12
mov r10, 0x0 
adcx r15, r10
adox rbp, r14
adox rcx, r11
adox r15, rdi
movzx rbx, al
adox rbx, r10
mov r14, r8
sub r14, 0x00000001
mov r11, rbp
mov r12, 0xffffffff00000000 
sbb r11, r12
mov rax, rcx
mov rdi, 0xffffffffffffffff 
sbb rax, rdi
mov r10, r15
sbb r10, rdx
sbb rbx, 0x00000000
cmovc r10, r15
cmovc rax, rcx
cmovc r14, r8
mov rbx, [ rsp - 0x50 ]
mov [ rbx + 0x18 ], r10
mov [ rbx + 0x0 ], r14
cmovc r11, rbp
mov [ rbx + 0x8 ], r11
mov [ rbx + 0x10 ], rax
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
ret
; cpu AMD Ryzen Threadripper 1900X 8-Core Processor
; ratio 1.3469
; seed 0303928856378873 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1980256 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=98, initial num_batches=31): 119434 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.06031240405280933
; number reverted permutation / tried permutation: 75504 / 90102 =83.798%
; number reverted decision / tried decision: 49921 / 89897 =55.531%
; validated in 3.446s
