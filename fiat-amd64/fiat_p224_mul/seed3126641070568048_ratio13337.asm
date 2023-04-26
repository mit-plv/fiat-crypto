SECTION .text
	GLOBAL fiat_p224_mul
fiat_p224_mul:
sub rsp, 256
mov rax, rdx
mov rdx, [ rsi + 0x0 ]
mulx r11, r10, [ rax + 0x0 ]
mov rdx, [ rsi + 0x8 ]
mulx r8, rcx, [ rax + 0x10 ]
mov rdx, [ rsi + 0x10 ]
mov [ rsp - 0x80 ], rbx
mulx rbx, r9, [ rax + 0x8 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x78 ], rbp
mov [ rsp - 0x70 ], r12
mulx r12, rbp, [ rsi + 0x8 ]
mov rdx, 0xffffffffffffffff 
mov [ rsp - 0x68 ], r13
mov [ rsp - 0x60 ], r14
mulx r14, r13, r10
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x58 ], r15
mulx r15, r14, [ rsi + 0x18 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp - 0x50 ], rdi
mov [ rsp - 0x48 ], r15
mulx r15, rdi, [ rsi + 0x10 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x40 ], r14
mov [ rsp - 0x38 ], r8
mulx r8, r14, [ rsi + 0x18 ]
mov rdx, [ rsi + 0x8 ]
mov [ rsp - 0x30 ], r8
mov [ rsp - 0x28 ], rcx
mulx rcx, r8, [ rax + 0x0 ]
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x20 ], r8
mov [ rsp - 0x18 ], r12
mulx r12, r8, [ rsi + 0x10 ]
test al, al
adox r9, r12
adox rdi, rbx
mov rdx, r13
adcx rdx, r10
mov rdx, 0xffffffffffffffff 
mulx rbx, r10, r13
mov rdx, [ rax + 0x0 ]
mov [ rsp - 0x10 ], rdi
mulx rdi, r12, [ rsi + 0x18 ]
mov rdx, [ rax + 0x8 ]
mov [ rsp - 0x8 ], r12
mov [ rsp + 0x0 ], r9
mulx r9, r12, [ rsi + 0x0 ]
setc dl
clc
adcx r14, rdi
setc dil
clc
adcx r12, r11
mov r11b, dl
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x8 ], r14
mov [ rsp + 0x10 ], r8
mulx r8, r14, [ rsi + 0x10 ]
mov rdx, [ rax + 0x18 ]
mov byte [ rsp + 0x18 ], dil
mov [ rsp + 0x20 ], rbp
mulx rbp, rdi, [ rsi + 0x0 ]
mov rdx, [ rax + 0x10 ]
mov [ rsp + 0x28 ], rcx
mov [ rsp + 0x30 ], rbx
mulx rbx, rcx, [ rsi + 0x0 ]
adox r14, r15
adcx rcx, r9
adcx rdi, rbx
mov rdx, 0xffffffff00000000 
mulx r9, r15, r13
seto bl
mov rdx, -0x1 
inc rdx
mov rdx, -0x1 
movzx r11, r11b
adox r11, rdx
adox r12, r15
mov r11, 0x0 
adcx rbp, r11
mov r15, 0xffffffff 
mov rdx, r15
mulx r11, r15, r13
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x38 ], r14
mulx r14, r13, [ rsi + 0x8 ]
clc
adcx r10, r9
movzx rdx, bl
lea rdx, [ rdx + r8 ]
adcx r15, [ rsp + 0x30 ]
adox r10, rcx
mov r8, [ rsp + 0x20 ]
setc bl
clc
adcx r8, [ rsp + 0x28 ]
mov rcx, [ rsp - 0x28 ]
adcx rcx, [ rsp - 0x18 ]
adox r15, rdi
mov rdi, rdx
mov rdx, [ rax + 0x18 ]
mov [ rsp + 0x40 ], r14
mulx r14, r9, [ rsi + 0x18 ]
adcx r13, [ rsp - 0x38 ]
setc dl
clc
adcx r12, [ rsp - 0x20 ]
mov [ rsp + 0x48 ], rdi
mov rdi, [ rsp - 0x30 ]
mov [ rsp + 0x50 ], r14
seto r14b
mov byte [ rsp + 0x58 ], dl
movzx rdx, byte [ rsp + 0x18 ]
mov [ rsp + 0x60 ], r13
mov r13, 0x0 
dec r13
adox rdx, r13
adox rdi, [ rsp - 0x40 ]
adcx r8, r10
adcx rcx, r15
adox r9, [ rsp - 0x48 ]
mov rdx, 0xffffffffffffffff 
mulx r15, r10, r12
movzx r15, bl
lea r15, [ r15 + r11 ]
seto r11b
inc r13
mov rbx, -0x1 
movzx r14, r14b
adox r14, rbx
adox rbp, r15
adcx rbp, [ rsp + 0x60 ]
mulx r15, r14, r10
mov r13, 0xffffffff 
mov rdx, r10
mulx rbx, r10, r13
mov r13, rdx
mov [ rsp + 0x68 ], r9
seto r9b
mov [ rsp + 0x70 ], rdi
mov rdi, -0x2 
inc rdi
adox r13, r12
mov r13, 0xffffffff00000000 
mulx rdi, r12, r13
movzx rdx, byte [ rsp + 0x58 ]
mov r13, [ rsp + 0x40 ]
lea rdx, [ rdx + r13 ]
adox r12, r8
movzx r13, r11b
mov r8, [ rsp + 0x50 ]
lea r13, [ r13 + r8 ]
movzx r8, r9b
adcx r8, rdx
setc r11b
clc
adcx r14, rdi
adcx r10, r15
mov r9, 0x0 
adcx rbx, r9
clc
adcx r12, [ rsp + 0x10 ]
adox r14, rcx
adox r10, rbp
adox rbx, r8
mov rcx, 0xffffffffffffffff 
mov rdx, rcx
mulx rbp, rcx, r12
mulx r15, rbp, rcx
adcx r14, [ rsp + 0x0 ]
adcx r10, [ rsp - 0x10 ]
movzx rdi, r11b
adox rdi, r9
mov r11, 0xffffffff00000000 
mov rdx, r11
mulx r8, r11, rcx
mov rdx, rcx
mov [ rsp + 0x78 ], r13
mov r13, -0x3 
inc r13
adox rdx, r12
adcx rbx, [ rsp + 0x38 ]
adcx rdi, [ rsp + 0x48 ]
adox r11, r14
mov rdx, 0xffffffff 
mulx r14, r12, rcx
setc cl
clc
adcx rbp, r8
adox rbp, r10
adcx r12, r15
adcx r14, r9
adox r12, rbx
clc
adcx r11, [ rsp - 0x8 ]
mov r15, 0xffffffffffffffff 
mov rdx, r11
mulx r10, r11, r15
mov r10, r11
setc r8b
clc
adcx r10, rdx
adox r14, rdi
movzx r10, cl
adox r10, r9
dec r9
movzx r8, r8b
adox r8, r9
adox rbp, [ rsp + 0x8 ]
adox r12, [ rsp + 0x70 ]
adox r14, [ rsp + 0x68 ]
adox r10, [ rsp + 0x78 ]
mov rbx, 0xffffffff 
mov rdx, r11
mulx rcx, r11, rbx
mov rdi, 0xffffffff00000000 
mulx r9, r8, rdi
mulx rbx, r13, r15
adcx r8, rbp
seto dl
mov rbp, -0x2 
inc rbp
adox r13, r9
adcx r13, r12
adox r11, rbx
adcx r11, r14
mov r12, 0x0 
adox rcx, r12
adcx rcx, r10
setc r14b
mov r10, r8
sub r10, 0x00000001
movzx r9, r14b
movzx rdx, dl
lea r9, [ r9 + rdx ]
mov rdx, r13
sbb rdx, rdi
mov rbx, r11
sbb rbx, r15
mov r14, rcx
mov r12, 0xffffffff 
sbb r14, r12
sbb r9, 0x00000000
cmovc r14, rcx
cmovc rbx, r11
cmovc rdx, r13
mov r9, [ rsp - 0x50 ]
mov [ r9 + 0x8 ], rdx
cmovc r10, r8
mov [ r9 + 0x0 ], r10
mov [ r9 + 0x10 ], rbx
mov [ r9 + 0x18 ], r14
mov rbx, [ rsp - 0x80 ]
mov rbp, [ rsp - 0x78 ]
mov r12, [ rsp - 0x70 ]
mov r13, [ rsp - 0x68 ]
mov r14, [ rsp - 0x60 ]
mov r15, [ rsp - 0x58 ]
add rsp, 256
ret
; cpu 11th Gen Intel(R) Core(TM) i7-11700KF @ 3.60GHz
; ratio 1.3337
; seed 3126641070568048 
; CC / CFLAGS clang / -march=native -mtune=native -O3 
; time needed: 8278 ms on 1000 evaluations.
; Time spent for assembling and measuring (initial batch_size=137, initial num_batches=31): 500 ms
; number of used evaluations: 1000
; Ratio (time for assembling + measure)/(total runtime for 1000 evals): 0.060401063058709833
; number reverted permutation / tried permutation: 369 / 495 =74.545%
; number reverted decision / tried decision: 352 / 504 =69.841%
; validated in 3.453s
