SECTION .text
	GLOBAL fiat_p224_square
fiat_p224_square:
sub rsp, 240
mov rdx, [ rsi + 0x0 ]
mulx r10, rax, rdx
mov rdx, [ rsi + 0x8 ]
mulx rcx, r11, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mulx r9, r8, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x80 ], rbx
mov [ rsp - 0x78 ], rbp
mulx rbp, rbx, rax
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x70 ], r12
mulx r12, rbp, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x58 ], r15
mov [ rsp - 0x50 ], rdi
mulx rdi, r15, [ rsi + 0x10 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x48 ], r13
mov [ rsp - 0x40 ], r8
mulx r8, r13, rdx
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x38 ], r12
mov [ rsp - 0x30 ], rbp
mulx rbp, r12, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x0 ]
mov [ rsp - 0x28 ], rbp
mov [ rsp - 0x20 ], rcx
mulx rcx, rbp, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x18 ], r11
mov [ rsp - 0x10 ], r14
mulx r14, r11, rbx
xor rdx, rdx
adox rbp, r10
adcx r13, r9
mov rdx, [ rsi + 0x8 ]
mulx r9, r10, [ rsi + 0x10 ]
adox r15, rcx
adcx r10, r8
adox r12, rdi
mov rdx, 0xffffffff00000000 
mulx r8, rdi, rbx
mov rdx, [ rsi + 0x18 ]
mov [ rsp - 0x8 ], r10
mulx r10, rcx, [ rsi + 0x8 ]
adcx rcx, r9
setc dl
clc
adcx r11, r8
mov r9, [ rsp - 0x10 ]
seto r8b
mov [ rsp + 0x0 ], rcx
mov rcx, -0x2 
inc rcx
adox r9, [ rsp - 0x18 ]
mov rcx, [ rsp - 0x30 ]
adox rcx, [ rsp - 0x20 ]
mov [ rsp + 0x8 ], rcx
mov rcx, 0xffffffff 
xchg rdx, rbx
mov [ rsp + 0x10 ], r9
mov [ rsp + 0x18 ], r10
mulx r10, r9, rcx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov byte [ rsp + 0x20 ], bl
mov [ rsp + 0x28 ], r10
mulx r10, rbx, [ rsi + 0x10 ]
adcx r9, r14
setc dl
clc
adcx rcx, rax
adcx rdi, rbp
adcx r11, r15
adox rbx, [ rsp - 0x38 ]
seto cl
mov rax, -0x2 
inc rax
adox rdi, [ rsp - 0x40 ]
mov r14, 0xffffffffffffffff 
xchg rdx, rdi
mulx r15, rbp, r14
movzx r15, r8b
mov rax, [ rsp - 0x28 ]
lea r15, [ r15 + rax ]
adcx r9, r12
adox r13, r11
mov rax, 0xffffffff 
xchg rdx, rax
mulx r12, r8, rbp
adox r9, [ rsp - 0x8 ]
mov rdx, [ rsi + 0x18 ]
mulx r14, r11, [ rsi + 0x8 ]
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x30 ], rbx
mov [ rsp + 0x38 ], r9
mulx r9, rbx, [ rsi + 0x0 ]
movzx rdx, dil
mov [ rsp + 0x40 ], rbx
mov rbx, [ rsp + 0x28 ]
lea rdx, [ rdx + rbx ]
movzx rbx, byte [ rsp + 0x20 ]
mov rdi, [ rsp + 0x18 ]
lea rbx, [ rbx + rdi ]
adcx rdx, r15
movzx rdi, cl
lea rdi, [ rdi + r10 ]
mov r10, rdx
mov rdx, [ rsi + 0x18 ]
mulx r15, rcx, [ rsi + 0x10 ]
adox r10, [ rsp + 0x0 ]
seto dl
mov [ rsp + 0x48 ], rdi
mov rdi, -0x2 
inc rdi
adox r11, r9
movzx r9, dl
adcx r9, rbx
adox rcx, r14
mov r14, 0xffffffffffffffff 
mov rdx, rbp
mulx rbx, rbp, r14
mov rdi, 0xffffffff00000000 
mov [ rsp + 0x50 ], rcx
mulx rcx, r14, rdi
setc dil
clc
adcx rbp, rcx
adcx r8, rbx
mov rbx, 0x0 
adcx r12, rbx
mov rcx, rdx
mov rdx, [ rsi + 0x18 ]
mov [ rsp + 0x58 ], r11
mulx r11, rbx, rdx
clc
adcx rcx, rax
adcx r14, r13
adcx rbp, [ rsp + 0x38 ]
adox rbx, r15
mov rdx, 0x0 
adox r11, rdx
mov rcx, -0x3 
inc rcx
adox r14, [ rsp - 0x48 ]
mov rax, 0xffffffffffffffff 
mov rdx, rax
mulx r13, rax, r14
adcx r8, r10
adcx r12, r9
movzx r13, dil
mov r15, 0x0 
adcx r13, r15
adox rbp, [ rsp + 0x10 ]
mov r10, 0xffffffff00000000 
mov rdx, rax
mulx rdi, rax, r10
adox r8, [ rsp + 0x8 ]
adox r12, [ rsp + 0x30 ]
adox r13, [ rsp + 0x48 ]
mov r9, rdx
clc
adcx r9, r14
adcx rax, rbp
seto r9b
mov r14, -0x3 
inc r14
adox rax, [ rsp + 0x40 ]
mov r14, 0xffffffffffffffff 
xchg rdx, r14
mulx r15, rbp, rax
mulx rcx, r15, r14
seto dl
mov r10, -0x2 
inc r10
adox r15, rdi
adcx r15, r8
mov rdi, 0xffffffff00000000 
xchg rdx, rbp
mulx r10, r8, rdi
mov rdi, 0xffffffff 
xchg rdx, r14
mov [ rsp + 0x60 ], r11
mov [ rsp + 0x68 ], r8
mulx r8, r11, rdi
adox r11, rcx
mov rdx, 0x0 
adox r8, rdx
adcx r11, r12
adcx r8, r13
movzx r12, r9b
adc r12, 0x0
mov r9, 0xffffffffffffffff 
mov rdx, r9
mulx r13, r9, r14
test al, al
adox r9, r10
mov rdx, rdi
mulx rcx, rdi, r14
adox rdi, r13
mov r10, 0x0 
adox rcx, r10
adcx r14, rax
dec r10
movzx rbp, bpl
adox rbp, r10
adox r15, [ rsp + 0x58 ]
adox r11, [ rsp + 0x50 ]
adox rbx, r8
adcx r15, [ rsp + 0x68 ]
adcx r9, r11
adcx rdi, rbx
adox r12, [ rsp + 0x60 ]
adcx rcx, r12
seto r14b
adc r14b, 0x0
movzx r14, r14b
mov rax, r15
sub rax, 0x00000001
mov rbp, r9
mov r8, 0xffffffff00000000 
sbb rbp, r8
mov r13, rdi
mov r11, 0xffffffffffffffff 
sbb r13, r11
mov rbx, rcx
sbb rbx, rdx
movzx r12, r14b
sbb r12, 0x00000000
cmovc rax, r15
cmovc rbx, rcx
mov r12, [ rsp - 0x50 ]
mov [ r12 + 0x0 ], rax
cmovc rbp, r9
mov [ r12 + 0x8 ], rbp
mov [ r12 + 0x18 ], rbx
cmovc r13, rdi
mov [ r12 + 0x10 ], r13
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 240
ret
; cpu AMD Ryzen 9 5950X 16-Core Processor
; ratio 1.2661
; seed 1055341502723241 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 1370678 ms on 180000 evaluations.
; Time spent for assembling and measuring (initial batch_size=156, initial num_batches=31): 88609 ms
; number of used evaluations: 180000
; Ratio (time for assembling + measure)/(total runtime for 180000 evals): 0.0646461094436476
; number reverted permutation / tried permutation: 69387 / 90374 =76.778%
; number reverted decision / tried decision: 47480 / 89625 =52.976%
; validated in 2.591s
